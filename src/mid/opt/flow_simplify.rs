use std::collections::HashSet;

use itertools::Itertools;

use crate::mid::ir::{Block, BlockInfo, Program, Target, Terminator, Value};

//TODO also consider combining instructions from multiple blocks together
pub fn flow_simplify(prog: &mut Program) -> bool {
    let mut count_skipped = 0;
    let mut count_branch_removed = 0;

    // simplify function entries
    let funcs = prog.nodes.funcs.keys().collect_vec();
    for func in funcs {
        let entry = &prog.get_func(func).entry;
        let (delta, new_target) = EndPoint::find_target(prog, entry.clone(), None);
        count_skipped += delta;
        prog.get_func_mut(func).entry = new_target;
    }

    // simplify block terminators
    let blocks = prog.nodes.blocks.keys().collect_vec();
    for block in blocks {
        let info = prog.get_block_mut(block);
        let old_term = std::mem::replace(&mut info.terminator, Terminator::Unreachable);

        let new_term = match old_term.clone() {
            Terminator::Jump { target } => {
                // convert to the final terminator
                let (delta, new_term) = EndPoint::find_terminator(prog, target.clone(), Some(block));
                count_skipped += delta;
                new_term
            }
            Terminator::Branch { cond, true_target, false_target } => {
                match &cond {
                    Value::Undef(_) => {
                        // undefined condition, this is undefined behavior
                        count_branch_removed += 1;
                        Terminator::Unreachable
                    }
                    Value::Const(cst) => {
                        // const condition, remove the branch and replace with final terminator
                        let target = if cst.value != 0 { true_target } else { false_target };
                        count_branch_removed += 1;

                        let (delta, new_term) = EndPoint::find_terminator(prog, target, Some(block));
                        count_skipped += delta;
                        new_term
                    }
                    _ => {
                        // general condition, we can still try to replace the targets
                        let (true_delta, true_target) = EndPoint::find_target(prog, true_target, Some(block));
                        let (false_delta, false_target) = EndPoint::find_target(prog, false_target, Some(block));
                        count_skipped += true_delta + false_delta;
                        Terminator::Branch { cond, true_target, false_target }
                    }
                }
            }
            Terminator::Return { .. } => old_term,
            Terminator::Unreachable => old_term,
        };

        let mut info = prog.get_block_mut(block);
        info.terminator = new_term;
    }

    println!("flow_simplify skipped {} blocks and removed {} branches", count_skipped, count_branch_removed);
    let count = count_skipped + count_branch_removed;
    count != 0
}

#[derive(Debug)]
struct EndPoint {
    count_skipped: usize,
    fallback_target: Target,
    terminator: Option<Terminator>,
}

impl EndPoint {
    fn find_target(prog: &Program, start: Target, start_block: Option<Block>) -> (usize, Target) {
        Self::find(prog, start, start_block).to_target()
    }

    fn find_terminator(prog: &Program, start: Target, start_block: Option<Block>) -> (usize, Terminator) {
        Self::find(prog, start, start_block).to_terminator()
    }

    fn find(prog: &Program, start: Target, start_block: Option<Block>) -> Self {
        let mut blocks_seen = HashSet::new();
        blocks_seen.extend(start_block.iter());
        let mut count_skipped = 0;

        let Target { mut block, mut phi_values } = start;

        loop {
            if !blocks_seen.insert(block) {
                // prevent infinite loop
                break;
            }
            if !phi_values.is_empty() {
                break;
            }

            let BlockInfo { phis, instructions, terminator }
                = prog.get_block(block);
            assert_eq!(phis.len(), phi_values.len());
            if !instructions.is_empty() {
                break;
            }

            // TODO is the way this works correct? doesn't it depend on the later choice between terminator and target?
            count_skipped += 1;

            match terminator {
                Terminator::Jump { target } => {
                    let Target { block: new_block, phi_values: new_phi_values } = target;
                    block = *new_block;
                    phi_values = new_phi_values.clone();
                }
                terminator => {
                    return EndPoint {
                        count_skipped,
                        fallback_target: Target { block, phi_values },
                        terminator: Some(terminator.clone()),
                    };
                }
            }
        }

        EndPoint {
            count_skipped,
            fallback_target: Target { block, phi_values },
            terminator: None,
        }
    }

    fn to_target(self) -> (usize, Target) {
        let count_skipped = if self.terminator.is_some() {
            self.count_skipped - 1
        } else {
            self.count_skipped
        };

        (count_skipped, self.fallback_target)
    }

    fn to_terminator(self) -> (usize, Terminator) {
        let terminator = match self.terminator {
            None => Terminator::Jump { target: self.fallback_target },
            Some(terminator) => terminator,
        };
        (self.count_skipped, terminator)
    }
}
