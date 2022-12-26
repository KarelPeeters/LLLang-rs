use crate::back::layout::Layout;
use crate::back::x64_asm::{PARAM_REGISTERS, Register};
use crate::mid::ir::{Function, FunctionType, Program, Type};

pub const STACK_ALIGNMENT: i32 = 16;

pub enum ArgPosition {
    Register(Register),
    Stack { rev_offset: i32 },
}

pub struct CallLayout {
    pub params: Vec<ArgPosition>,
    pub stack_param_area: i32,
}

#[derive(Debug)]
pub struct InvalidParameterSize{
    index: usize,
    ty: Type,
    layout: Layout,
}

impl CallLayout {
    pub fn for_func(prog: &Program, func: Function) -> Result<Self, InvalidParameterSize> {
        let func_ty = &prog.get_func(func).func_ty;
        Self::for_type(prog, func_ty)
    }

    pub fn for_type(prog: &Program, func_ty: &FunctionType) -> Result<Self, InvalidParameterSize> {
        let mut stack_param_area = 0;
        let mut args = vec![];
        for (pi, &param_ty) in func_ty.params.iter().enumerate() {
            let layout = Layout::for_type(prog, param_ty);

            if ![1, 2, 4, 8].contains(&layout.size) {
                return Err(InvalidParameterSize {
                    index: pi,
                    ty: param_ty,
                    layout,
                });
            }

            if pi < 4 {
                // pass in register
                args.push(ArgPosition::Register(PARAM_REGISTERS[pi]));
            } else {
                // pass on stack
                args.push(ArgPosition::Stack { rev_offset: stack_param_area });
                stack_param_area += layout.size;
            }
        }

        Ok(CallLayout {
            params: args,
            stack_param_area,
        })
    }
}
