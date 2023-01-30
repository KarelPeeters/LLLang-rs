use std::cmp::max;

use itertools::Itertools;

pub use constants::WIN64_ABI_PARAM_REGS as ABI_PARAM_REGS;
pub use constants::WIN64_ABI_RETURN_REG as ABI_RETURN_REG;

use crate::back::abi::constants::{WIN64_ABI_CALL_VOLATILE_REGS, WIN64_ABI_PARAM_REGS, WIN64_ABI_RETURN_REG};
use crate::back::layout::Layout;
use crate::back::register::{Register, RSize};
use crate::mid::ir::{CallingConvention, FunctionType, Program, Type};

// TODO reuse existing stack slots for reg passing (and in general)
// TODO move the "too large abi" param passing stuff to an IR norm pass?
// TODO caller and callee saved? do we need distinctions between preferred and not or will it figure it out itself
//   when calls clobber stuff?

#[allow(dead_code)]
mod constants {
    use crate::back::register::Register;
    use crate::back::register::Register::*;

    pub const WIN64_ABI_PARAM_REGS: &[Register] = &[C, D, R8, R9];
    pub const WIN64_ABI_RETURN_REG: Register = A;

    pub const WIN64_ABI_CALL_VOLATILE_REGS: &[Register] = &[A, C, D, R8, R9, R10, R11];
    pub const WIN64_ABI_CALL_NON_VOLATILE_REGS: &[Register] = &[B, BP, DI, SI, SP, R12, R13, R14, R15];
}

// TODO add a way to tell functions that they can clobber part of the parent stack range (eg for params in win64)

/// All sizes are in bytes.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FunctionAbi {
    /// Stack space that needs to be allocated by the callee, for register parameter shadow space and stack parameters.
    /// This does **not** include the return address location pushed by `call` or additional slots necessary for passing
    /// parameters by reference.
    pub stack_space_allocated_by_caller: u32,
    /// How much the stack needs to be aligned **after** the return address is pushed.
    pub stack_alignment_bytes: u32,

    pub by_ref_slot_types: Vec<Type>,

    pub stack_space_freed_by_caller: u32,
    pub stack_space_freed_by_callee: u32,

    /// The registers the function is not required to preserve. Also called the _volatile / caller-saved registers_.
    /// All other registers are either _nonvolatile / callee-saved_ or special purpose (like the stack pointer).
    pub volatile_registers: Vec<Register>,

    pub pass_params: Vec<PassInfo>,
    pub pass_ret: PassInfo,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct PassInfo {
    pub pos: PassPosition,
    pub by: PassBy,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum PassPosition {
    Reg(Register),
    StackSlot { stack_offset: u32 },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum PassBy {
    Value,
    // index indo by_ref_slot_types
    Ref(usize),
}

impl FunctionAbi {
    pub fn for_type(prog: &Program, ty: &FunctionType) -> Self {
        match ty.conv {
            CallingConvention::Win64 => Self::for_type_win64(prog, ty),
            CallingConvention::Custom => Self::for_type_custom(prog, ty),
        }
    }

    pub fn for_type_custom(prog: &Program, ty: &FunctionType) -> Self {
        // TODO make up our own better calling convention?
        Self::for_type_win64(prog, ty)
    }

    pub fn for_type_win64(prog: &Program, ty: &FunctionType) -> Self {
        // Relevant Microsoft docs:
        //   * calling conv:  https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170
        //   * general stack: https://learn.microsoft.com/en-us/cpp/build/stack-usage?view=msvc-170

        // for large types: replace with ptr first, then push to stack
        //   stack slots must be 16-byte aligned
        // struct smaller than register: put in register, let callee take it apart
        // if param doesn't fit in reg, skip that register


        let &FunctionType { ref params, ret, conv: _ } = ty;

        let mut ref_slot_types = vec![];
        let mut next_param_index = 0;

        let pass_ret = if win64_passed_by_ref(Layout::for_type(prog, ret)) {
            // return first ref slot and param
            next_param_index += 1;
            ref_slot_types.push(ret);
            PassInfo {
                pos: PassPosition::Reg(WIN64_ABI_PARAM_REGS[0]),
                by: PassBy::Ref(0),
            }
        } else {
            PassInfo {
                pos: PassPosition::Reg(WIN64_ABI_RETURN_REG),
                by: PassBy::Value,
            }
        };

        let pass_params = params.iter().map(|&param| {
            let param_index = next_param_index;
            next_param_index += 1;

            // TODO structs cannot be passed in registers, even if they fit
            let param_layout = Layout::for_type(prog, param);

            let by = if win64_passed_by_ref(param_layout) {
                ref_slot_types.push(param);
                PassBy::Ref(ref_slot_types.len() - 1)
            } else {
                PassBy::Value
            };

            let pos = if let Some(&reg) = WIN64_ABI_PARAM_REGS.get(param_index as usize) {
                PassPosition::Reg(reg)
            } else {
                // don't subtract reg count, we still allocate shadow stack space for those
                let stack_offset = RSize::FULL.bytes() * param_index;
                PassPosition::StackSlot { stack_offset }
            };

            PassInfo { pos, by }
        }).collect_vec();

        let stack_space = RSize::FULL.bytes() * max(4, next_param_index as u32);

        FunctionAbi {
            stack_space_allocated_by_caller: stack_space,
            stack_alignment_bytes: 16,
            stack_space_freed_by_caller: 0,
            stack_space_freed_by_callee: 0,
            volatile_registers: WIN64_ABI_CALL_VOLATILE_REGS.to_owned(),
            by_ref_slot_types: ref_slot_types,
            pass_params,
            pass_ret,
        }
    }
}

fn win64_passed_by_ref(layout: Layout) -> bool {
    // The win64 calling conv doesn't clarify what to do with zero sized types.
    // There's no register size for zero-sized types,
    //   but it would be completely pointless to allocate stack space for them
    if layout.size_bytes == 0 {
        return false;
    }

    // TODO this is not exactly right:
    //   for returns it needs to be 1, 2, 4, 8, 16, 32, 64 bits   -> what type has size 2 bits??
    //   for params it needs to be 8, 16, 32, 64 bits
    RSize::from_bytes(layout.size_bytes).is_none()
}

#[cfg(test)]
mod test {
    use std::fmt::Debug;
    use std::hash::Hash;

    use itertools::Itertools;

    use crate::back::abi::{FunctionAbi, PassBy, PassInfo, PassPosition};
    use crate::back::abi::constants::{WIN64_ABI_CALL_NON_VOLATILE_REGS, WIN64_ABI_CALL_VOLATILE_REGS, WIN64_ABI_PARAM_REGS};
    use crate::back::register::Register;
    use crate::mid::ir::{CallingConvention, FunctionType, Program, TupleType};

    fn assert_unique<T: Eq + Debug + Hash>(items: &[T]) {
        assert_eq!(items.iter().unique().count(), items.len(), "Expected unique items, got {:?}", items);
    }

    #[test]
    fn makes_sense() {
        assert_unique(WIN64_ABI_PARAM_REGS);
        assert_unique(WIN64_ABI_CALL_VOLATILE_REGS);
        assert_unique(WIN64_ABI_CALL_NON_VOLATILE_REGS);
        assert_eq!(Register::ALL.len(), WIN64_ABI_CALL_VOLATILE_REGS.len() + WIN64_ABI_CALL_NON_VOLATILE_REGS.len());
    }

    #[test]
    fn windows_abi_basic() {
        let mut prog = Program::new(64);
        let ty_int = prog.define_type_int(32);

        let ty = FunctionType {
            params: vec![ty_int; 6],
            ret: prog.ty_void(),
            conv: CallingConvention::Win64,
        };

        let expected_pass_params = vec![
            PassInfo { pos: PassPosition::Reg(Register::C), by: PassBy::Value },
            PassInfo { pos: PassPosition::Reg(Register::D), by: PassBy::Value },
            PassInfo { pos: PassPosition::Reg(Register::R8), by: PassBy::Value },
            PassInfo { pos: PassPosition::Reg(Register::R9), by: PassBy::Value },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 4 * 8 }, by: PassBy::Value },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 5 * 8 }, by: PassBy::Value },
        ];
        let expected = FunctionAbi {
            stack_space_allocated_by_caller: 6 * 8,
            stack_alignment_bytes: 16,
            by_ref_slot_types: vec![],
            stack_space_freed_by_caller: 0,
            stack_space_freed_by_callee: 0,
            volatile_registers: WIN64_ABI_CALL_VOLATILE_REGS.to_owned(),
            pass_params: expected_pass_params,
            pass_ret: PassInfo { pos: PassPosition::Reg(Register::A), by: PassBy::Value },
        };

        let actual = FunctionAbi::for_type(&prog, &ty);
        assert_eq!(format!("{:#?}", actual), format!("{:#?}", expected));
    }

    #[test]
    fn windows_abi_too_few() {
        let mut prog = Program::new(64);
        let ty_int = prog.define_type_int(32);

        let ty = FunctionType {
            params: vec![ty_int; 2],
            ret: prog.ty_void(),
            conv: CallingConvention::Win64,
        };

        let expected_pass_params = vec![
            PassInfo { pos: PassPosition::Reg(Register::C), by: PassBy::Value },
            PassInfo { pos: PassPosition::Reg(Register::D), by: PassBy::Value },
        ];
        let expected = FunctionAbi {
            stack_space_allocated_by_caller: 4 * 8,
            stack_alignment_bytes: 16,
            by_ref_slot_types: vec![],
            stack_space_freed_by_caller: 0,
            stack_space_freed_by_callee: 0,
            volatile_registers: WIN64_ABI_CALL_VOLATILE_REGS.to_owned(),
            pass_params: expected_pass_params,
            pass_ret: PassInfo { pos: PassPosition::Reg(Register::A), by: PassBy::Value },
        };

        let actual = FunctionAbi::for_type(&prog, &ty);
        assert_eq!(format!("{:#?}", actual), format!("{:#?}", expected));
    }

    #[test]
    fn windows_abi_large() {
        let mut prog = Program::new(64);
        let ty_int = prog.define_type_int(32);

        let ty_struct_arg = prog.define_type_tuple(TupleType { fields: vec![ty_int, ty_int, ty_int, ty_int] });
        let ty_struct_ret = prog.define_type_tuple(TupleType { fields: vec![ty_int, ty_int, ty_int] });

        let ty = FunctionType {
            params: vec![ty_struct_arg, ty_int, ty_struct_arg, ty_int, ty_struct_arg, ty_int, ty_int],
            ret: ty_struct_ret,
            conv: CallingConvention::Win64,
        };

        let expected_pass_params = vec![
            // return value is ref in first arg and slot!
            PassInfo { pos: PassPosition::Reg(Register::D), by: PassBy::Ref(1) },
            PassInfo { pos: PassPosition::Reg(Register::R8), by: PassBy::Value },
            PassInfo { pos: PassPosition::Reg(Register::R9), by: PassBy::Ref(2) },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 4 * 8 }, by: PassBy::Value },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 5 * 8 }, by: PassBy::Ref(3) },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 6 * 8 }, by: PassBy::Value },
            PassInfo { pos: PassPosition::StackSlot { stack_offset: 7 * 8 }, by: PassBy::Value },
        ];
        let expected = FunctionAbi {
            stack_space_allocated_by_caller: 8 * 8,
            stack_alignment_bytes: 16,
            by_ref_slot_types: vec![ty_struct_ret, ty_struct_arg, ty_struct_arg, ty_struct_arg],
            stack_space_freed_by_caller: 0,
            stack_space_freed_by_callee: 0,
            volatile_registers: WIN64_ABI_CALL_VOLATILE_REGS.to_owned(),
            pass_params: expected_pass_params,
            pass_ret: PassInfo { pos: PassPosition::Reg(Register::C), by: PassBy::Ref(0) },
        };

        let actual = FunctionAbi::for_type(&prog, &ty);
        assert_eq!(format!("{:#?}", actual), format!("{:#?}", expected));
    }
}
