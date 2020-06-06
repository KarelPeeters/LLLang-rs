use crate::mid::ir;
use crate::mid::ir::TerminatorInfo;

pub fn run(prog: &ir::Program) -> i32 {
    let func = prog.func(prog.entry);
    let block = prog.block(func.entry);
    let term = prog.term(block.terminator);

    for _ in &block.instructions {
        panic!("Instructions not supported yet")
    }

    let value = match &term {
        TerminatorInfo::Return { value } => *value,
        TerminatorInfo::Unreachable => panic!("Reached Unreachable"),
    };

    value
}