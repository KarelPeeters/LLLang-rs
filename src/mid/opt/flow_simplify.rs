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
        let (delta, endpoint) = EndPoint::find(prog, entry.clone(), &[]);
        count_skipped += delta;

        prog.get_func_mut(func).entry = endpoint.to_target();
    }

    // simplify block terminators
    let blocks = prog.nodes.blocks.keys().collect_vec();
    for block in blocks {
        let info = prog.get_block_mut(block);
        let old_term = std::mem::replace(&mut info.terminator, Terminator::Unreachable);

        let new_term = match old_term {
            Terminator::Jump { target } => {
                // convert to the final terminator
                let (delta, endpoint) = EndPoint::find(prog, target.clone(), &[block]);
                count_skipped += delta;
                endpoint.to_terminator()
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

                        let (delta, endpoint) = EndPoint::find(prog, target, &[block]);
                        count_skipped += delta;
                        endpoint.to_terminator()
                    }
                    _ => {
                        // general condition, we can still try to replace the targets
                        let (true_delta, true_endpoint) = EndPoint::find(prog, true_target, &[block]);
                        let (false_delta, false_endpoint) = EndPoint::find(prog, false_target, &[block]);
                        let true_target = true_endpoint.to_target();
                        let false_target = false_endpoint.to_target();

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
    fallback_target: Target,
    terminator: Option<Terminator>,
}

impl EndPoint {
    fn find(prog: &mut Program, target: Target, blocks_seen: &[Block]) -> (usize, Self) {
        let mut blocks_seen: HashSet<Block> = blocks_seen.iter().copied().collect();

        let Target { mut block, mut phi_values } = target;
        let mut count_skipped = 0;

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
                    let endpoint = EndPoint {
                        fallback_target: Target { block, phi_values },
                        terminator: Some(terminator.clone()),
                    };
                    return (count_skipped, endpoint);
                }
            }
        }

        let endpoint = EndPoint {
            fallback_target: Target { block, phi_values },
            terminator: None,
        };
        (count_skipped, endpoint)
    }

    fn to_target(self) -> Target {
        self.fallback_target
    }

    fn to_terminator(self) -> Terminator {
        match self.terminator {
            None => Terminator::Jump { target: self.fallback_target },
            Some(terminator) => terminator,
        }
    }
}
