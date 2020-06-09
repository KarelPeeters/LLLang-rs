use crate::mid::ir;
use crate::mid::ir::{Const, Terminator, Value};

pub fn run(prog: &ir::Program) -> i32 {
    let func = prog.get_func(prog.main);
    let block = prog.get_block(func.entry);

    for _ in &block.instructions {
        panic!("Instructions not supported yet")
    }

    let value = match &block.terminator {
        Terminator::Return { value: Value::Const(Const { value, .. }) } => *value,
        Terminator::Return { .. } => panic!("Non const returns not yet supported"),
        Terminator::Unreachable => panic!("Reached Unreachable"),
    };

    value
}