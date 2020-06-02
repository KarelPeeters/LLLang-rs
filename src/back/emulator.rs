use crate::mid::ir;
use crate::mid::ir::Terminator;

pub fn run(func: &ir::Function) -> i32 {
    match func.entry.terminator {
        Terminator::Return { value } => value,
    }
}