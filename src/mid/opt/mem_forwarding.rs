use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::mid::analyse::use_info::{BlockUsage, TargetSource, UseInfo};
use crate::mid::ir::{Block, Global, Immediate, InstructionInfo, Program, Scoped, StackSlot, Terminator, Type, Value};
use crate::mid::util::lattice::Lattice;

/// Optimize load/store instructions:
/// * replace loads with previously stored values
/// * remove dead stores
pub fn mem_forwarding(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let mut loads_replaced = 0;
    let mut stores_removed = 0;

    // replace loads
    for block in use_info.blocks() {
        let instrs = prog.get_block(block).instructions.clone();

        for (index, &instr) in instrs.iter().enumerate() {
            let instr_info = prog.get_instr(instr);
            if let &InstructionInfo::Load { addr, ty: load_ty } = instr_info {
                let location = Location { ptr: addr, ty: load_ty };
                let lattice = find_value_for_location_at_instr(prog, &use_info, location, block, Some(index));

                if let Some(value) = lattice.as_value_of_type(prog, load_ty) {
                    loads_replaced += 1;
                    use_info.replace_value_usages(prog, instr.into(), value);
                }
            }
        }
    }

    // remove dead stores
    // (in a separate pass because this can invalidate use_info)
    let mut cache = LivenessCache::default();
    for block in use_info.blocks() {
        // TODO abstract this index/remove/increment mess somewhere
        //  it's like retain except we don't have ownership
        let mut instr_index = 0;

        loop {
            let block_info = prog.get_block(block);
            if instr_index >= block_info.instructions.len() {
                break;
            }

            let instr = block_info.instructions[instr_index];
            let remove = if let &InstructionInfo::Store { addr, ty, value: _ } = prog.get_instr(instr) {
                let location = Location { ptr: addr, ty };

                let liveness = compute_liveness(prog, block, instr_index + 1, location, &mut cache);

                match liveness {
                    Liveness::Dead => true,
                    Liveness::MaybeLive => false,
                }
            } else {
                false
            };

            if remove {
                prog.get_block_mut(block).instructions.remove(instr_index);
                stores_removed += 1;
                // don't increment index
            } else {
                instr_index += 1;
            }
        }
    }

    println!("mem_forwarding replaced {} loads and removed {} stores", loads_replaced, stores_removed);
    loads_replaced > 0 || stores_removed > 0
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
struct Location {
    ptr: Value,
    ty: Type,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Alias {
    /// At least one of the pointers if undefined
    Undef,
    /// Both storages point to the same place
    Exactly,
    /// We don't have enough information to say anything
    UnknownOrPartial,
    /// Both storages definitely don't overlap at all
    No,
}

#[derive(Debug)]
enum Origin {
    /// The pointer is undefined.
    Undef,

    /// The given slot, from the current function.
    FuncStackSlot(StackSlot),
    /// Any slot from the current function.
    // TODO consider tracking which specific func slots it can be
    FuncAnyStackSlot,

    /// Some other value external to this function.
    FuncExternal,

    /// We don't have enough information.
    Unknown,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Liveness {
    Dead,
    MaybeLive,
}

impl Liveness {
    // TODO implement general "lattice" or "merge" trait with top(), bottom(), merge() => fold, ...
    fn merge(left: Liveness, right: Liveness) -> Liveness {
        match (left, right) {
            (Liveness::MaybeLive, _) | (_, Liveness::MaybeLive) => Liveness::MaybeLive,
            (Liveness::Dead, Liveness::Dead) => Liveness::Dead,
        }
    }
}

type LivenessCache = HashMap<(Block, Location), Liveness>;

fn compute_liveness(prog: &Program, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // the values in the cache apply to the start of the block
    if start == 0 {
        match cache.entry((block, loc)) {
            // we've found the answer in the cache already, great!
            Entry::Occupied(entry) => return *entry.get(),
            // otherwise temporarily assume the current block is dead
            Entry::Vacant(entry) => entry.insert(Liveness::Dead),
        };
    }

    // check the rest of the block and its successors
    let liveness = compute_liveness_inner(prog, block, start, loc, cache);

    // put the true liveness into the cache
    if start == 0 {
        let prev = cache.insert((block, loc), liveness);
        assert_eq!(prev, Some(Liveness::Dead));
    }

    liveness
}

/// The same as [compute_liveness] except we don't manage the cache here.
fn compute_liveness_inner(prog: &Program, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // check the following instructions
    if let Some(liveness) = compute_liveness_by_instructions(prog, block, start, loc) {
        return liveness;
    }

    // fallthrough to the successors
    match &prog.get_block(block).terminator {
        Terminator::Jump { target } => {
            compute_liveness(prog, target.block, 0, loc, cache)
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            Liveness::merge(
                compute_liveness(prog, true_target.block, 0, loc, cache),
                compute_liveness(prog, false_target.block, 0, loc, cache),
            )
        }
        Terminator::Return { value: _ } => {
            let origin = pointer_origin(prog, loc.ptr);
            match origin {
                // function-internal, so cannot be observed after return
                Origin::FuncStackSlot(_) | Origin::FuncAnyStackSlot => Liveness::Dead,
                // maybe external, so can potentially be observed
                // TODO maybe we can do something better with undef here?
                Origin::Undef | Origin::Unknown | Origin::FuncExternal => Liveness::MaybeLive,
            }
        }
        // no successor, so dead
        Terminator::Unreachable => Liveness::Dead,
    }
}

// TODO ideally this would use some common "instruction side effect" infrastructure
fn compute_liveness_by_instructions(prog: &Program, block: Block, start: usize, loc: Location) -> Option<Liveness> {
    let block_info = prog.get_block(block);
    for &instr in &block_info.instructions[start..] {
        match *prog.get_instr(instr) {
            // (maybe) aliasing load => alive
            InstructionInfo::Load { addr, ty } => {
                let load_loc = Location { ptr: addr, ty };
                match locations_alias(prog, loc, load_loc) {
                    // could alias, we have to assume live
                    Alias::Exactly | Alias::UnknownOrPartial => return Some(Liveness::MaybeLive),
                    // can't alias, keep going
                    Alias::Undef | Alias::No => {}
                }
            }
            // (exactly) aliasing store => dead
            InstructionInfo::Store { addr, ty, value: _ } => {
                let store_loc = Location { ptr: addr, ty };
                match locations_alias(prog, loc, store_loc) {
                    // value is overwritten, we know the previous one is dead
                    // TODO a "covering" alias is enough already, it doesn't have to be exact
                    Alias::Exactly => return Some(Liveness::Dead),
                    // may not be overwritten, keep going
                    // TODO maybe we can do something better with undef here?
                    Alias::Undef | Alias::UnknownOrPartial | Alias::No => {}
                }
            }

            // these could have side effects, we have to assume live
            // TODO we can do better for calls
            InstructionInfo::Call { .. } => return Some(Liveness::MaybeLive),
            InstructionInfo::BlackBox { .. } => return Some(Liveness::MaybeLive),

            // no memory reads
            InstructionInfo::Arithmetic { .. } => {}
            InstructionInfo::Comparison { .. } => {}
            InstructionInfo::TupleFieldPtr { .. } => {}
            InstructionInfo::PointerOffSet { .. } => {}
            InstructionInfo::Cast { .. } => {}
        }
    }

    None
}

fn find_value_for_location_at_instr(prog: &Program, use_info: &UseInfo, location: Location, block: Block, index: Option<usize>) -> Lattice {
    let block_info = prog.get_block(block);
    let index = index.unwrap_or(block_info.instructions.len());

    // first see if any instruction before the load aliases
    for &instr in block_info.instructions[0..index].iter().rev() {
        match prog.get_instr(instr) {
            &InstructionInfo::Store { addr: store_ptr, ty: store_ty, value } => {
                let store_location = Location { ptr: store_ptr, ty: store_ty };
                match locations_alias(prog, location, store_location) {
                    // propagate undef
                    Alias::Undef => return Lattice::Undef,
                    // we know the exact value last stored to the pointer!
                    Alias::Exactly => return Lattice::Known(value),
                    // we have to give up
                    Alias::UnknownOrPartial => return Lattice::Overdef,
                    // continue walking backwards
                    Alias::No => {}
                }
            }

            // could have side effects, we have to give up
            // TODO we can do better for calls:
            //   * side effect free functions
            //   * if we don't leak a slot to external or to this call the function can't store to it
            InstructionInfo::Call { .. } => return Lattice::Overdef,
            InstructionInfo::BlackBox { .. } => return Lattice::Overdef,

            // no memory writes
            InstructionInfo::Load { .. } => {}
            InstructionInfo::Arithmetic { .. } => {}
            InstructionInfo::Comparison { .. } => {}
            InstructionInfo::TupleFieldPtr { .. } => {}
            InstructionInfo::PointerOffSet { .. } => {}
            InstructionInfo::Cast { .. } => {}
        }
    }

    // otherwise the value is the merge of the value at the end of each predecessor
    Lattice::fold(use_info[block].iter().map(|BlockUsage { target_kind }| {
        match target_kind.source() {
            // we've reached the start of the function, depending on the origin the value is undef or overdef
            TargetSource::Entry(_) => match pointer_origin(prog, location.ptr) {
                Origin::Undef => Lattice::Undef,
                Origin::Unknown | Origin::FuncExternal => Lattice::Overdef,
                Origin::FuncStackSlot(_) | Origin::FuncAnyStackSlot => Lattice::Undef,
            },
            // continue searching along the preceding block
            TargetSource::Block(pos) => {
                find_value_for_location_at_instr(prog, use_info, location, pos.block, None)
            }
        }
    }))
}

fn locations_alias(prog: &Program, left: Location, right: Location) -> Alias {
    let same_ty = left.ty == right.ty;

    match pointers_alias(prog, left.ptr, right.ptr) {
        Alias::Undef => Alias::Undef,
        Alias::Exactly => {
            if same_ty {
                Alias::Exactly
            } else {
                Alias::UnknownOrPartial
            }
        }
        Alias::UnknownOrPartial => Alias::UnknownOrPartial,
        Alias::No => Alias::No,
    }
}

fn pointers_alias(prog: &Program, ptr_left: Value, ptr_right: Value) -> Alias {
    let ptr_left = simplify_ptr(prog, ptr_left);
    let ptr_right = simplify_ptr(prog, ptr_right);

    if ptr_left.is_undef() || ptr_right.is_undef() {
        return Alias::Undef;
    }
    if ptr_left == ptr_right {
        return Alias::Exactly;
    }

    let alias_from_origin = origins_alias(pointer_origin(prog, ptr_left), pointer_origin(prog, ptr_right));
    if let Alias::No | Alias::Exactly = alias_from_origin {
        return alias_from_origin;
    }

    if let (Some(instr_left), Some(instr_right)) = (ptr_left.as_instr(), ptr_right.as_instr()) {
        match (prog.get_instr(instr_left), prog.get_instr(instr_right)) {
            (
                &InstructionInfo::PointerOffSet { ty: inner_ty_left, base: base_left, index: index_left },
                &InstructionInfo::PointerOffSet { ty: inner_ty_right, base: base_right, index: index_right },
            ) => {
                let base_alias = pointers_alias(prog, base_left, base_right);
                if base_alias == Alias::Undef {
                    return Alias::Undef;
                }
                if (inner_ty_left == inner_ty_right) && (index_left == index_right) {
                    return base_alias;
                }
                // the zero-size type case is already handled by simplify_ptr
            }

            (
                &InstructionInfo::TupleFieldPtr { base: base_left, index: index_left, tuple_ty: tuple_ty_left },
                &InstructionInfo::TupleFieldPtr { base: base_right, index: index_right, tuple_ty: tuple_ty_right },
            ) => {
                let base_alias = pointers_alias(prog, base_left, base_right);
                if base_alias == Alias::Undef {
                    return Alias::Undef;
                }
                if tuple_ty_left == tuple_ty_right && index_left == index_right {
                    return base_alias;
                }
            }

            _ => {}
        }
    }

    Alias::UnknownOrPartial
}

fn simplify_ptr(prog: &Program, ptr: Value) -> Value {
    assert_eq!(prog.type_of_value(ptr), prog.ty_ptr());

    if let Some(instr) = ptr.as_instr() {
        match *prog.get_instr(instr) {
            InstructionInfo::PointerOffSet { ty, base, index } => {
                if prog.is_zero_sized_type(ty) {
                    return simplify_ptr(prog, base);
                }
                if let Some(cst) = index.as_const() {
                    if cst.is_zero() {
                        return simplify_ptr(prog, base);
                    }
                }
            }
            InstructionInfo::TupleFieldPtr { base, index: _, tuple_ty } => {
                // index == 0 is not enough to decay to base pointer, since the layout of tuples is decided by the backend
                // however, single-element tuples are still guaranteed to have the same layout as the single item inside them
                let field_count = prog.get_type(tuple_ty).unwrap_tuple().unwrap().fields.len();
                if field_count == 0 || field_count == 1 {
                    return simplify_ptr(prog, base);
                }
            }
            _ => {}
        }
    }

    ptr
}

// TODO do some proper dataflow analysis here
//  specifically this would be useful for things like:
//    * phis
//    * load/store forwarding, which is what we're doing here in the first place!)
// TODO ideally incorporate this into SCCP?
fn pointer_origin(prog: &Program, ptr: Value) -> Origin {
    assert_eq!(prog.type_of_value(ptr), prog.ty_ptr());

    match ptr {
        Value::Immediate(value) => match value {
            Immediate::Void => unreachable!("Void cannot have pointer type: {:?}", ptr),
            Immediate::Undef(_) => Origin::Undef,
            Immediate::Const(_) => Origin::FuncExternal,
        },
        Value::Global(value) => match value {
            Global::Func(_) => unreachable!("Function cannot have pointer type: {:?}", ptr),
            Global::Extern(_) => Origin::FuncExternal,
            Global::Data(_) => Origin::FuncExternal,
        },
        Value::Scoped(value) => match value {
            Scoped::Param(_) => Origin::FuncExternal,
            Scoped::Slot(slot) => Origin::FuncStackSlot(slot),
            Scoped::Phi(_) => Origin::Unknown,
            Scoped::Instr(instr) => match prog.get_instr(instr) {
                InstructionInfo::Load { .. } => Origin::Unknown,
                InstructionInfo::Store { .. } | InstructionInfo::Arithmetic { .. } | InstructionInfo::Comparison { .. } =>
                    unreachable!("This instruction cannot return pointer type: {:?}", instr),
                InstructionInfo::Call { .. } => Origin::Unknown,
                &InstructionInfo::TupleFieldPtr { base, index: _, tuple_ty: _, } => pointer_origin(prog, base),
                &InstructionInfo::PointerOffSet { ty: _, base, index: _ } => pointer_origin(prog, base),
                // TODO when we add ptr/int casts maybe we can look through them?
                InstructionInfo::Cast { .. } => Origin::Unknown,
                InstructionInfo::BlackBox { .. } => Origin::Unknown,
            }
        },
    }
}

fn origins_alias(left: Origin, right: Origin) -> Alias {
    match (left, right) {
        (Origin::Undef, _) | (_, Origin::Undef) => Alias::Undef,
        (Origin::Unknown, _) | (_, Origin::Unknown) => Alias::UnknownOrPartial,
        (Origin::FuncExternal, Origin::FuncExternal) => Alias::UnknownOrPartial,

        (Origin::FuncStackSlot(left), Origin::FuncStackSlot(right)) => {
            if left == right {
                Alias::Exactly
            } else {
                Alias::No
            }
        }
        (Origin::FuncAnyStackSlot, Origin::FuncAnyStackSlot) => Alias::UnknownOrPartial,
        (Origin::FuncStackSlot(_), Origin::FuncAnyStackSlot) | (Origin::FuncAnyStackSlot, Origin::FuncStackSlot(_)) => Alias::UnknownOrPartial,

        (Origin::FuncExternal, Origin::FuncStackSlot(_) | Origin::FuncAnyStackSlot) => Alias::No,
        (Origin::FuncStackSlot(_) | Origin::FuncAnyStackSlot, Origin::FuncExternal) => Alias::No,
    }
}

impl Origin {
    // TODO start using this when we switch to something more dataflow-like
    #[allow(dead_code)]
    fn merge(left: Origin, right: Origin) -> Origin {
        match (left, right) {
            (Origin::Unknown, _) | (_, Origin::Unknown) => Origin::Unknown,
            (Origin::Undef, other) | (other, Origin::Undef) => other,

            (Origin::FuncStackSlot(left), Origin::FuncStackSlot(right)) => {
                if left == right {
                    Origin::FuncStackSlot(left)
                } else {
                    Origin::FuncAnyStackSlot
                }
            }
            (Origin::FuncAnyStackSlot | Origin::FuncStackSlot(_), Origin::FuncAnyStackSlot | Origin::FuncStackSlot(_)) => Origin::FuncAnyStackSlot,

            (Origin::FuncExternal, Origin::FuncExternal) => Origin::FuncExternal,

            (Origin::FuncAnyStackSlot | Origin::FuncStackSlot(_), Origin::FuncExternal) => Origin::Unknown,
            (Origin::FuncExternal, Origin::FuncAnyStackSlot | Origin::FuncStackSlot(_)) => Origin::Unknown,
        }
    }
}