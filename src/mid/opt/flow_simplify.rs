use itertools::Itertools;

use crate::mid::ir::{Block, BlockInfo, Function, Immediate, Program, Target, Terminator, Value};
use crate::util::internal_iter::InternalIterator;

#[derive(Default, Debug, Copy, Clone)]
struct Counts {
    entries: usize,
    terminators: usize,
}

//TODO combine this with block_threading in a single pass?
// TODO replace the current "repeat until fixpoint" with a proper graph solver algorithm
pub fn flow_simplify(prog: &mut Program) -> bool {
    let mut counts = Counts::default();

    for func in prog.nodes.funcs.keys().collect_vec() {
        counts = counts + flow_simplify_func(prog, func);
    }

    println!("flow_simplify changed {} terminators and {} entries", counts.terminators, counts.entries);
    counts.changed()
}

fn flow_simplify_func(prog: &mut Program, func: Function) -> Counts {
    let entry = prog.get_func(func).entry;
    let blocks = prog.reachable_blocks(entry).collect_vec();

    let mut counts = Counts::default();

    loop {
        let delta = flow_simplify_step(prog, func, &blocks);
        counts = counts + delta;

        if !delta.changed() {
            break;
        }
    }

    counts
}

fn flow_simplify_step(prog: &mut Program, func: Function, blocks: &[Block]) -> Counts {
    let mut counts = Counts::default();

    // simplify terminators
    for &block in blocks {
        let old_term = &prog.get_block(block).terminator;

        let new_term = simplify_terminator(prog, block, old_term);
        if let Some(new_term) = new_term {
            counts.terminators += 1;
            prog.get_block_mut(block).terminator = new_term;
        }
    }

    // skip entry block
    // TODO in if the entry is the only thing pointing to the block we can do better
    let old_entry = prog.get_func(func).entry;
    if prog.get_block(old_entry).params.is_empty() {
        if let Some(new_entry) = skip_entry(prog, old_entry) {
            counts.entries += 1;
            prog.get_func_mut(func).entry = new_entry;
        }
    }

    counts
}

fn simplify_terminator(prog: &Program, block: Block, terminator: &Terminator) -> Option<Terminator> {
    match *terminator {
        Terminator::Branch { cond, ref true_target, ref false_target } => {
            match cond {
                // undefined condition is undefined behaviour
                Value::Immediate(Immediate::Undef(_)) => Some(Terminator::Unreachable),
                // const condition means this is actually just a jump
                Value::Immediate(Immediate::Const(cst)) => {
                    let target = if cst.as_bool().unwrap() { true_target } else { false_target };
                    Some(Terminator::Jump { target: target.clone() })
                }
                _ => {
                    // try cutting out unreachable branches
                    // TODO technically we can add a hint that the condition must be true/false
                    let true_valid = !is_empty_unreachable(prog, true_target.block);
                    let false_value = !is_empty_unreachable(prog, false_target.block);
                    match (true_valid, false_value) {
                        // if both invalid this terminator is invalid
                        (false, false) => Some(Terminator::Unreachable),
                        // if one invalid we must take the other one
                        (false, true) => Some(Terminator::Jump { target: false_target.clone() }),
                        (true, false) => Some(Terminator::Jump { target: true_target.clone() }),
                        // otherwise it really is a branch
                        (true, true) => {
                            let new_true_target = skip_target_to_target(prog,  true_target);
                            let new_false_target = skip_target_to_target(prog,  false_target);

                            if new_true_target.is_some() || new_false_target.is_some() {
                                Some(Terminator::Branch {
                                    cond,
                                    true_target: new_true_target.unwrap_or_else(|| true_target.clone()),
                                    false_target: new_false_target.unwrap_or_else(|| false_target.clone()),
                                })
                            } else {
                                None
                            }
                        },
                    }
                }
            }
        }

        Terminator::Jump { ref target } => {
            if target.block == block && prog.get_block(block).instructions.is_empty() {
                // replace empty self loop with dedicated terminator
                Some(Terminator::LoopForever)
            } else {
                // try skipping
                skip_target_to_target(prog, target).map(|target| Terminator::Jump { target })
            }
        }

        Terminator::Return { .. } | Terminator::Unreachable | Terminator::LoopForever => None,
    }
}

fn skip_entry(prog: &Program, block: Block) -> Option<Block> {
    let BlockInfo { params, instructions, terminator, debug_name: _ } = prog.get_block(block);

    if params.is_empty() && instructions.is_empty() {
        if let Terminator::Jump { target: Target { block: next, args: ref args_next } } = *terminator {
            if args_next.is_empty() {
                return Some(next);
            }
        }
    }

    None
}

fn skip_target_to_target(prog: &Program, target: &Target) -> Option<Target> {
    if target.args.is_empty() {
        let BlockInfo { params, instructions, terminator, debug_name: _ } = prog.get_block(target.block);
        assert!(params.is_empty());

        if instructions.is_empty() {
            if let Terminator::Jump { target: next_target } = terminator {
                return Some(next_target.clone());
            }
        }
    }

    None
}

fn is_empty_unreachable(prog: &Program, block: Block) -> bool {
    let block_info = prog.get_block(block);
    if !block_info.instructions.is_empty() {
        return false;
    }

    let term = &block_info.terminator;
    matches!(term, Terminator::Unreachable)
}

impl Counts {
    fn changed(&self) -> bool {
        self.entries > 0 || self.terminators > 0
    }
}

impl std::ops::Add for Counts {
    type Output = Counts;

    fn add(self, rhs: Self) -> Self::Output {
        Counts {
            entries: self.entries + rhs.entries,
            terminators: self.terminators + rhs.terminators,
        }
    }
}