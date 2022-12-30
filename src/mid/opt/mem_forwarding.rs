use crate::mid::analyse::use_info::{BlockUsage, TargetSource, UseInfo};
use crate::mid::ir::{Block, Global, Immediate, InstructionInfo, Program, Scoped, StackSlot, Type, Value};
use crate::mid::util::lattice::Lattice;

pub fn mem_forwarding(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let mut replaced = 0;

    for block in use_info.blocks() {
        let instrs = prog.get_block(block).instructions.clone();

        for (index, &instr) in instrs.iter().enumerate() {
            let instr_info = prog.get_instr(instr);
            if let &InstructionInfo::Load { addr, ty: load_ty } = instr_info {
                let location = Location { ptr: addr, ty: load_ty };
                let lattice = find_value_for_location_at_instr(prog, &use_info, location, block, Some(index));

                if let Some(value) = lattice.as_value_of_type(prog, load_ty) {
                    replaced += 1;
                    use_info.replace_value_usages(prog, instr.into(), value);
                }
            }
        }
    }

    println!("mem_forwarding replaced {} values", replaced);
    replaced > 0
}

#[derive(Debug, Copy, Clone)]
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
            // call could have side effects, we have to give up
            // TODO can we do better here?
            //   * side effect free functions
            //   * if we don't leak a slot to external or to this call the function can't store to it
            InstructionInfo::Call { .. } => return Lattice::Overdef,

            // no memory interactions
            InstructionInfo::Load { .. } => {}
            InstructionInfo::Arithmetic { .. } => {}
            InstructionInfo::Comparison { .. } => {}
            InstructionInfo::TupleFieldPtr { .. } => {}
            InstructionInfo::PointerOffSet { .. } => {}
            InstructionInfo::Cast { .. } => {}
            InstructionInfo::BlackBox { .. } => {}
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
                    return base_alias;
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
                    return base_alias;
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