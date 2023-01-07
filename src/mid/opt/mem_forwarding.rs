use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, ExpressionInfo, Function, Global, Immediate, InstructionInfo, Program, Scoped, StackSlot, Terminator, Type, Value};
use crate::mid::util::lattice::Lattice;

/// Optimize load/store instructions:
/// * replace loads with previously stored values
/// * remove dead stores
pub fn mem_forwarding(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let mut loads_replaced = 0;
    let mut stores_removed = 0;

    // replace loads
    let mut lattice_cache = LatticeCache::default();
    for func in use_info.funcs() {
        for &block in use_info.func_blocks(func) {
            let instrs = prog.get_block(block).instructions.clone();

            for (index, &instr) in instrs.iter().enumerate() {
                let instr_info = prog.get_instr(instr);
                if let &InstructionInfo::Load { addr, ty: load_ty } = instr_info {
                    let loc = Location { ptr: addr, ty: load_ty };
                    let lattice = find_value_for_location_at_instr(prog, &use_info, func, loc, block, Some(index), &mut lattice_cache);

                    if let Some(value) = lattice.as_value_of_type(prog, load_ty) {
                        loads_replaced += 1;
                        use_info.replace_value_usages(prog, instr.into(), value);
                    }
                }
            }
        }
    }

    // remove dead stores
    // (in a separate pass because this can invalidate use_info)
    let mut liveness_cache = LivenessCache::default();
    for func in use_info.funcs() {
        for &block in use_info.func_blocks(func) {
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
                    let loc = Location { ptr: addr, ty };
                    let liveness = compute_liveness(prog, func, block, instr_index + 1, loc, &mut liveness_cache);
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

/// The liveness cache stores the liveness for each location at the start of the given block.
/// This can also include a temporary "dead" assumption to break loops.
type LivenessCache = HashMap<(Block, Location), Liveness>;

fn compute_liveness(prog: &Program, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
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
    let liveness = compute_liveness_inner(prog, func, block, start, loc, cache);

    // put the true liveness into the cache
    if start == 0 {
        let prev = cache.insert((block, loc), liveness);
        assert_eq!(prev, Some(Liveness::Dead));
    }

    liveness
}

/// The same as [compute_liveness] except we don't manage the cache here.
fn compute_liveness_inner(prog: &Program, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // check the following instructions
    if let Some(liveness) = compute_liveness_by_instructions(prog, func, block, start, loc) {
        return liveness;
    }

    // fallthrough to the successors
    match &prog.get_block(block).terminator {
        Terminator::Jump { target } => {
            compute_liveness(prog, func, target.block, 0, loc, cache)
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            Liveness::merge(
                compute_liveness(prog, func, true_target.block, 0, loc, cache),
                compute_liveness(prog, func, false_target.block, 0, loc, cache),
            )
        }
        Terminator::Return { value: _ } => {
            let origin = pointer_origin(prog, func, loc.ptr);
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
        Terminator::LoopForever => Liveness::Dead,
    }
}

// TODO ideally this would use some common "instruction side effect" infrastructure
fn compute_liveness_by_instructions(prog: &Program, func: Function, block: Block, start: usize, loc: Location) -> Option<Liveness> {
    let block_info = prog.get_block(block);
    for &instr in &block_info.instructions[start..] {
        match *prog.get_instr(instr) {
            // (maybe) aliasing load => alive
            InstructionInfo::Load { addr, ty } => {
                let load_loc = Location { ptr: addr, ty };
                match locations_alias(prog, func, loc, load_loc) {
                    // could alias, we have to assume live
                    Alias::Exactly | Alias::UnknownOrPartial => return Some(Liveness::MaybeLive),
                    // can't alias, keep going
                    Alias::Undef | Alias::No => {}
                }
            }
            // (exactly) aliasing store => dead
            InstructionInfo::Store { addr, ty, value: _ } => {
                let store_loc = Location { ptr: addr, ty };
                match locations_alias(prog, func, loc, store_loc) {
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
        }
    }

    None
}

/// The lattice cache stores the lattice value for each location at the end of the given block.
/// This can also include a temporary "undef" assumption to break loops.
type LatticeCache = HashMap<(Block, Location), Lattice>;

fn find_value_for_location_at_instr(
    prog: &Program,
    use_info: &UseInfo,
    func: Function,
    loc: Location,
    block: Block,
    index: Option<usize>,
    cache: &mut LatticeCache,
) -> Lattice {
    if index.is_none() {
        match cache.entry((block, loc)) {
            Entry::Occupied(entry) => return *entry.get(),
            Entry::Vacant(entry) => entry.insert(Lattice::Undef),
        };
    }

    let lattice = find_value_for_location_at_instr_inner(prog, use_info, func, loc, block, index, cache);

    if index.is_none() {
        let prev = cache.insert((block, loc), lattice);
        assert_eq!(prev, Some(Lattice::Undef));
    }

    lattice
}

/// The same as [find_value_for_location_at_instr] except we don't manage the cache here.
fn find_value_for_location_at_instr_inner(
    prog: &Program,
    use_info: &UseInfo,
    func: Function,
    loc: Location,
    block: Block,
    index: Option<usize>,
    cache: &mut LatticeCache,
) -> Lattice {
    let block_info = prog.get_block(block);
    let index = index.unwrap_or(block_info.instructions.len());

    // first see if any instruction before the load aliases
    for &instr in block_info.instructions[0..index].iter().rev() {
        match prog.get_instr(instr) {
            &InstructionInfo::Store { addr: store_ptr, ty: store_ty, value } => {
                let store_loc = Location { ptr: store_ptr, ty: store_ty };
                match locations_alias(prog, func, loc, store_loc) {
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
        }
    }

    // otherwise the value is the merge of the value at the end of each predecessor
    Lattice::fold(use_info[block].iter().map(|usage| {
        match usage {
            // we've reached the start of the function, depending on the origin the value is undef or overdef
            BlockUsage::FuncEntry(_) => match pointer_origin(prog, func, loc.ptr) {
                Origin::Undef => Lattice::Undef,
                Origin::Unknown | Origin::FuncExternal => Lattice::Overdef,
                Origin::FuncStackSlot(_) | Origin::FuncAnyStackSlot => Lattice::Undef,
            },
            // continue searching along the preceding block
            BlockUsage::Target { pos, kind: _ } => {
                find_value_for_location_at_instr(prog, use_info, func, loc, pos.block, None, cache)
            }
        }
    }))
}

fn locations_alias(prog: &Program, func: Function, left: Location, right: Location) -> Alias {
    let same_ty = left.ty == right.ty;

    match pointers_alias(prog, func, left.ptr, right.ptr) {
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

fn pointers_alias(prog: &Program, func: Function, ptr_left: Value, ptr_right: Value) -> Alias {
    let ptr_left = simplify_ptr(prog, ptr_left);
    let ptr_right = simplify_ptr(prog, ptr_right);

    if ptr_left.is_undef() || ptr_right.is_undef() {
        return Alias::Undef;
    }
    if ptr_left == ptr_right {
        return Alias::Exactly;
    }

    let alias_from_origin = origins_alias(pointer_origin(prog, func, ptr_left), pointer_origin(prog, func, ptr_right));
    if let Alias::No = alias_from_origin {
        return alias_from_origin;
    }

    if let (Some(expr_left), Some(expr_right)) = (ptr_left.as_expr(), ptr_right.as_expr()) {
        match (prog.get_expr(expr_left), prog.get_expr(expr_right)) {
            (
                &ExpressionInfo::PointerOffSet { ty: inner_ty_left, base: base_left, index: index_left },
                &ExpressionInfo::PointerOffSet { ty: inner_ty_right, base: base_right, index: index_right },
            ) => {
                let base_alias = pointers_alias(prog, func, base_left, base_right);
                if base_alias == Alias::Undef {
                    return Alias::Undef;
                }
                if (inner_ty_left == inner_ty_right) && (index_left == index_right) {
                    return base_alias;
                }
                // the zero-size type case is already handled by simplify_ptr
            }

            (
                &ExpressionInfo::TupleFieldPtr { base: base_left, index: index_left, tuple_ty: tuple_ty_left },
                &ExpressionInfo::TupleFieldPtr { base: base_right, index: index_right, tuple_ty: tuple_ty_right },
            ) => {
                let base_alias = pointers_alias(prog, func, base_left, base_right);
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

    if let Some(expr) = ptr.as_expr() {
        match *prog.get_expr(expr) {
            ExpressionInfo::PointerOffSet { ty, base, index } => {
                if prog.is_zero_sized_type(ty) {
                    return simplify_ptr(prog, base);
                }
                if let Some(cst) = index.as_const() {
                    if cst.is_zero() {
                        return simplify_ptr(prog, base);
                    }
                }
            }
            ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty } => {
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
fn pointer_origin(prog: &Program, func: Function, ptr: Value) -> Origin {
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
            Scoped::Param(param) => {
                // check if this is a function param
                if prog.get_block(prog.get_func(func).entry).params.contains(&param) {
                    Origin::FuncExternal
                } else {
                    Origin::Unknown
                }
            }
            Scoped::Slot(slot) => Origin::FuncStackSlot(slot),
            Scoped::Instr(instr) => match prog.get_instr(instr) {
                InstructionInfo::Load { .. } => Origin::Unknown,
                InstructionInfo::Store { .. } =>
                    unreachable!("Instruction cannot return pointer type: {:?}", instr),
                InstructionInfo::Call { .. } => Origin::Unknown,
                InstructionInfo::BlackBox { .. } => Origin::Unknown,
            }
        },
        Value::Expr(expr) => match prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { .. } | ExpressionInfo::Comparison { .. } =>
                unreachable!("Expression cannot return pointer type: {:?}", expr),
            &ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _, } => pointer_origin(prog, func, base),
            &ExpressionInfo::PointerOffSet { ty: _, base, index: _ } => pointer_origin(prog, func, base),
            // TODO when we add ptr/int casts maybe we can look through them?
            ExpressionInfo::Cast { .. } => Origin::Unknown,
        }
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