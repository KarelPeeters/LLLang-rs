use crate::mid::ir::{Program, Terminator, Value, TypeInfo};

const HEADER: &str = r"
global _main
extern  _ExitProcess@4

section .text
_main:
";

pub fn lower(prog: &Program) -> String {
    let mut result = String::new();

    result.push_str(HEADER);

    let main = prog.get_func(prog.main);
    let entry = prog.get_block(main.entry);

    for &_instr in &entry.instructions {
        panic!("instructions not supported yet")
    }

    match &entry.terminator {
        Terminator::Return { value } => {
            match value {
                Value::Const(cst) => {
                    let ty = prog.get_type(cst.ty);
                    assert_eq!(ty, &TypeInfo::Integer { bits: 32 }, "only 32 bit integers supported for now");
                    result.push_str(&format!("push {}\n", cst.value));
                    result.push_str("call _ExitProcess@4\n");
                },
                Value::Slot(_) => panic!("slots loading not supported yet"),
                Value::Instr(_) => panic!("instr loading not supported yet"),
            }
        }
        Terminator::Unreachable => {
            result.push_str("hlt\n");
        }
    }


    result
}