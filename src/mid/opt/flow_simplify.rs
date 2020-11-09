use crate::mid::ir::{Block, Program, Terminator, Value};

//TODO also implement jump threading
//  make sure to implement that so everything happens at once without having to rerun the pass
pub fn flow_simplify(prog: &mut Program) -> bool {
    let blocks: Vec<Block> = prog.nodes.blocks.iter().map(|(block, _)| block).collect();
    let mut count = 0;

    for block in blocks {
        let info = prog.get_block_mut(block);

        let old_term = std::mem::replace(&mut info.terminator, Terminator::Unreachable);

        let new_term = match old_term {
            Terminator::Jump { .. } => old_term,
            Terminator::Branch { cond, true_target, false_target } => {
                match &cond {
                    Value::Undef(_) => {
                        count += 1;
                        Terminator::Unreachable
                    }
                    Value::Const(cst) => {
                        count += 1;
                        let target = if cst.value != 0 { true_target } else { false_target };
                        Terminator::Jump { target }
                    }
                    _ => Terminator::Branch { cond, true_target, false_target },
                }
            }
            Terminator::Return { .. } => old_term,
            Terminator::Unreachable => old_term,
        };

        info.terminator = new_term;
    }

    println!("flow_simplify replaced {} terminators", count);
    count != 0
}