use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ExpressionInfo, Function, Global, GlobalSlot, Immediate, InstructionInfo, Program, Scoped, StackSlot, Type, Value};

/// A location in memory, defined by the base pointer and the type.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Location {
    pub ptr: Value,
    pub ty: Type,
}

/// A decision on whether two [Location]s can alias.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum LocAlias {
    /// At least one of the locations is undefined.
    Undef,
    /// The locations overlap exactly.
    Exactly,
    /// We don't know whether the locations overlap or they overlap partially.
    UnknownOrPartial,
    /// The locations don't overlap at all.
    No,
}

/// A decision on whether two pointers can alias. This is different from [Location
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum PtrAlias {
    /// At least one of the pointers is undefined.
    Undef,
    /// Both pointers refer to exactly the same address.
    Exactly,
    /// We don't know whether the pointers alias.
    Unknown,
    /// Both pointers always refer to different addresses.
    No,
    /// If loads and stores only use the given type, this is the same as [PtrAlias::No].
    /// Otherwise the same as [PtrAlias::Unknown].
    NoIfType(Type),
}

/// A simplified version of a pointer.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct CorePtr {
    pub base: Value,
    pub offset: Offset,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Offset {
    None,
    Pointer(Type, i64),
    TupleField(Type, u32),
}

// TODO allow for multiple slots to be tracked?
/// The origin of a pointer.
/// This is a useful concept because pointers with different origins can by definition not alias.
#[derive(Debug)]
pub enum Origin {
    /// The pointer is undefined.
    Undef,

    /// A stack slot from the current function. Contains [Some] is the exact slot is known, [None] otherwise.
    FuncSlot(Option<StackSlot>),
    /// A global slot. Contains [Some] is the exact slot is known, [None] otherwise.
    GlobalSlot(Option<GlobalSlot>),

    /// Some location external to the current function frame.
    FuncExternal,

    //// We don't have enough information.
    Unknown,
}

pub fn locations_alias(prog: &Program, use_info: &UseInfo, func: Function, left: Location, right: Location) -> LocAlias {
    let same_ty = left.ty == right.ty;

    match pointers_alias(prog, use_info, func, left.ptr, right.ptr) {
        PtrAlias::Undef => LocAlias::Undef,
        PtrAlias::Unknown => LocAlias::UnknownOrPartial,
        PtrAlias::No => LocAlias::No,

        PtrAlias::Exactly => {
            if same_ty {
                LocAlias::Exactly
            } else {
                LocAlias::UnknownOrPartial
            }
        }
        PtrAlias::NoIfType(expected_ty) => {
            if same_ty && left.ty == expected_ty {
                LocAlias::No
            } else {
                LocAlias::UnknownOrPartial
            }
        }
    }
}

pub fn pointers_alias(prog: &Program, use_info: &UseInfo, func: Function, ptr_left: Value, ptr_right: Value) -> PtrAlias {
    let simple_left = core_ptr(prog, ptr_left);
    let simple_right = core_ptr(prog, ptr_right);

    if simple_left.base.is_undef() || simple_right.base.is_undef() {
        return PtrAlias::Undef;
    }
    if simple_left == simple_right {
        return PtrAlias::Exactly;
    }

    if simple_left.base == simple_right.base {
        match (simple_left.offset, simple_right.offset) {
            (Offset::None, Offset::None) => unreachable!(),

            // zero offset compared to non-zero offset
            (Offset::None, Offset::Pointer(ty, index)) | (Offset::Pointer(ty, index), Offset::None) => {
                assert!(!prog.is_zero_sized_type(ty) && index != 0);
                return PtrAlias::NoIfType(ty);
            }

            (Offset::Pointer(left_ty, left_index), Offset::Pointer(right_ty, right_index)) => {
                if left_ty == right_ty {
                    return if left_index == right_index {
                        PtrAlias::Exactly
                    } else {
                        PtrAlias::NoIfType(left_ty)
                    };
                }
            }

            (Offset::TupleField(left_ty, left_index), Offset::TupleField(right_ty, right_index)) => {
                if left_ty == right_ty {
                    return if left_index == right_index {
                        PtrAlias::Exactly
                    } else {
                        PtrAlias::NoIfType(left_ty)
                    };
                };
            }

            _ => {}
        }

        // bases still match, so origin check won't achieve anything anyway
        return PtrAlias::Unknown;
    }

    let origin_left = pointer_origin(prog, func, simple_left.base);
    let origin_right = pointer_origin(prog, func, simple_right.base);
    if !origins_can_alias(prog, use_info, origin_left, origin_right) {
        return PtrAlias::No;
    }

    PtrAlias::Unknown
}

pub fn core_ptr(prog: &Program, ptr: Value) -> CorePtr {
    assert_eq!(prog.type_of_value(ptr), prog.ty_ptr());

    if let Some(expr) = ptr.as_expr() {
        let expr_info = prog.get_expr(expr);
        match *expr_info {
            ExpressionInfo::PointerOffSet { ty, base, index } => {
                if prog.is_zero_sized_type(ty) {
                    return core_ptr(prog, base);
                }
                if let Some(index) = index.as_const() {
                    assert_eq!(prog.get_type(index.ty).unwrap_int(), Some(prog.ptr_size_bits()));
                    let index = index.value.signed();

                    return match index {
                        0 => core_ptr(prog, base),
                        _ => CorePtr { base, offset: Offset::Pointer(ty, index) }
                    };
                }
            }
            ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } => {
                // index == 0 is not enough to decay to base pointer, since the layout of tuples is decided by the backend
                // however, single-element tuples are still guaranteed to have the same layout as the single item inside them
                let field_count = prog.get_type(tuple_ty).unwrap_tuple().unwrap().fields.len();
                assert!(field_count > 0);
                if field_count == 1 {
                    return core_ptr(prog, base);
                }

                return CorePtr {
                    base,
                    offset: Offset::TupleField(tuple_ty, index),
                };
            }
            ExpressionInfo::Obscure { .. } => {
                // don't look deeper
            }
            _ => panic!("Unexpected pointer-yielding expression {:?} {:?}", expr, expr_info),
        }
    }

    CorePtr {
        base: ptr,
        offset: Offset::None,
    }
}

// TODO do some proper dataflow analysis here
//  specifically this would be useful for things like:
//    * phis
//    * load/store forwarding, which is what we're doing here in the first place!)
// TODO ideally incorporate this into SCCP?
pub fn pointer_origin(prog: &Program, func: Function, ptr: Value) -> Origin {
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
            Global::GlobalSlot(slot) => Origin::GlobalSlot(Some(slot)),
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
            Scoped::Slot(slot) => Origin::FuncSlot(Some(slot)),
            Scoped::Instr(instr) => match prog.get_instr(instr) {
                InstructionInfo::Load { .. } => Origin::Unknown,
                InstructionInfo::Call { .. } => Origin::Unknown,
                InstructionInfo::Store { .. } | InstructionInfo::BlackHole { .. } | InstructionInfo::MemBarrier =>
                    unreachable!("Instruction cannot return pointer type: {:?}", instr),
            }
        },
        Value::Expr(expr) => match prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { .. } | ExpressionInfo::Comparison { .. } =>
                unreachable!("Expression cannot return pointer type: {:?}", expr),
            &ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _, } => pointer_origin(prog, func, base),
            &ExpressionInfo::PointerOffSet { ty: _, base, index: _ } => pointer_origin(prog, func, base),
            // TODO when we add ptr/int casts maybe we can look through them?
            ExpressionInfo::Cast { .. } => Origin::Unknown,
            ExpressionInfo::Obscure { .. } => Origin::Unknown,
        }
    }
}

pub fn origins_can_alias(prog: &Program, use_info: &UseInfo, left: Origin, right: Origin) -> bool {
    match (left, right) {
        // undef doesn't alias with everything
        (Origin::Undef, _) | (_, Origin::Undef) => false,

        // two slots of the type type only alias if they're the same slot (or we don't know which slot it is)
        (Origin::FuncSlot(left), Origin::FuncSlot(right)) => match (left, right) {
            (None, _) | (_, None) => true,
            (Some(left), Some(right)) => left == right,
        },
        (Origin::GlobalSlot(left), Origin::GlobalSlot(right)) => match (left, right) {
            (None, _) | (_, None) => true,
            (Some(left), Some(right)) => left == right,
        },

        // slots that don't escape can only alias themselves, which was already covered
        (Origin::FuncSlot(Some(slot)), _) | (_, Origin::FuncSlot(Some(slot))) => {
            use_info.value_only_used_as_load_store_addr(prog, slot.into(), None, |_| true)
        }
        (Origin::GlobalSlot(Some(slot)), _) | (_, Origin::GlobalSlot(Some(slot))) => {
            use_info.value_only_used_as_load_store_addr(prog, slot.into(), None, |_| true)
        }

        (Origin::FuncExternal | Origin::GlobalSlot(_), Origin::FuncSlot(_)) => false,
        (Origin::FuncSlot(_), Origin::FuncExternal | Origin::GlobalSlot(_)) => false,

        (Origin::FuncExternal, Origin::FuncExternal) => true,
        (Origin::FuncExternal, Origin::GlobalSlot(_)) => true,
        (Origin::GlobalSlot(_), Origin::FuncExternal) => true,

        // don't put this first, we want other matches (notable the slots) to be checked first
        (Origin::Unknown, _) | (_, Origin::Unknown) => true,
    }
}
