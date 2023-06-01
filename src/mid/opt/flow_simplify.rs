use std::collections::HashSet;

use itertools::Itertools;

use crate::mid::ir::{Block, Immediate, Program, Target, Terminator, Value};

//TODO combine this with block_threading in a single pass?
pub fn flow_simplify(prog: &mut Program) -> bool {
    let mut count_skipped = 0;
    let mut count_simplified = 0;

    // simplify function entries
    let funcs = prog.nodes.funcs.keys().collect_vec();
    for func in funcs {
        let entry = prog.get_func(func).entry;

        if prog.get_block(entry).params.is_empty() {
            // convert to final entry
            let (skipped, new_entry) = find_block(prog, entry);
            count_skipped += skipped;
            prog.get_func_mut(func).entry = new_entry;
        }
    }

    // simplify block terminators
    let blocks = prog.nodes.blocks.keys().collect_vec();
    for block in blocks {
        let info = prog.get_block_mut(block);
        let old_term = std::mem::replace(&mut info.terminator, Terminator::Unreachable);

        let (simplified, simple_term) = simplify_terminator(prog, old_term.clone());
        count_simplified += simplified as usize;

        let new_term = match simple_term {
            Terminator::Jump { .. } => {
                // convert to final terminator
                let (delta, new_term) = find_terminator(prog, block, simple_term);
                count_skipped += delta;
                new_term
            }
            Terminator::Branch { cond, true_target, false_target } => {
                // convert to final targets
                let (true_delta, true_target) = find_target(prog, block, true_target);
                let (false_delta, false_target) = find_target(prog, block, false_target);
                count_skipped += true_delta + false_delta;
                Terminator::Branch { cond, true_target, false_target }
            }
            Terminator::Return { .. } => simple_term,
            Terminator::Unreachable => simple_term,
            Terminator::LoopForever => simple_term,
        };

        let mut info = prog.get_block_mut(block);
        info.terminator = new_term;
    }

    println!("flow_simplify skipped {} blocks and simplified {} terminators", count_skipped, count_simplified);
    let count = count_skipped + count_simplified;
    count != 0
}

fn simplify_terminator(prog: &Program, terminator: Terminator) -> (bool, Terminator) {
    match terminator {
        Terminator::Branch { cond, true_target, false_target } => {
            match cond {
                // undefined condition is undefined behaviour
                Value::Immediate(Immediate::Undef(_)) => (true, Terminator::Unreachable),
                // const condition means this is actually just a jump
                Value::Immediate(Immediate::Const(cst)) => {
                    let target = if cst.as_bool().unwrap() { true_target } else { false_target };
                    (true, Terminator::Jump { target })
                }
                _ => {
                    // try cutting out unreachable branches
                    // TODO technically we can add a hint that the condition must be true/false
                    let true_unreachable = is_empty_unreachable(prog, true_target.block);
                    let false_unreachable = is_empty_unreachable(prog, false_target.block);
                    match (true_unreachable, false_unreachable) {
                        (true, true) => (true, Terminator::Unreachable),
                        (true, false) => (true, Terminator::Jump { target: false_target }),
                        (false, true) => (true, Terminator::Jump { target: true_target }),
                        // otherwise it really is a branch
                        (false, false) => (false, Terminator::Branch { cond, true_target, false_target })
                    }
                }
            }
        }

        Terminator::Jump { .. } | Terminator::Return { .. } | Terminator::Unreachable | Terminator::LoopForever =>
            (false, terminator),
    }
}

fn is_empty_unreachable(prog: &Program, block: Block) -> bool {
    let block_info = prog.get_block(block);
    if !block_info.instructions.is_empty() {
        return false;
    }

    let term = &block_info.terminator;
    matches!(term, Terminator::Unreachable)
}

// TODO is there a way to merge find_block, find_target and find_term? they're all pretty similar...
// TODO replace all of this ad-hoc stuff with a proper "graph solver" thing
fn find_block(prog: &Program, start: Block) -> (usize, Block) {
    let mut skipped = 0;
    let mut blocks_seen = HashSet::new();

    let mut curr = start;
    loop {
        if !blocks_seen.insert(curr) {
            break;
        }

        let curr_info = prog.get_block(curr);
        assert!(curr_info.params.is_empty());
        if !curr_info.instructions.is_empty() {
            break;
        }

        match simplify_terminator(prog, curr_info.terminator.clone()).1 {
            Terminator::Jump { target: Target { block: next, args } } if args.is_empty() => {
                skipped += 1;
                curr = next;
            }
            _ => break,
        }
    }

    (skipped, curr)
}

fn find_target(prog: &Program, start_block: Block, start_target: Target) -> (usize, Target) {
    let mut skipped = 0;
    let mut blocks_seen = HashSet::new();
    blocks_seen.insert(start_block);

    let mut curr = start_target;

    loop {
        let &Target { block: curr_block, ref args } = &curr;
        if !args.is_empty() {
            break;
        }

        let curr_info = prog.get_block(curr_block);
        assert!(curr_info.params.is_empty());
        if !curr_info.instructions.is_empty() {
            break;
        }

        match simplify_terminator(prog, curr_info.terminator.clone()).1 {
            Terminator::Jump { target: next } => {
                if !blocks_seen.insert(next.block) {
                    break;
                }

                skipped += 1;
                curr = next.clone();
            }
            _ => break,
        }
    }

    (skipped, curr)
}

fn find_terminator(prog: &Program, start_block: Block, start_term: Terminator) -> (usize, Terminator) {
    let mut skipped = 0;
    let mut blocks_seen = HashSet::new();
    blocks_seen.insert(start_block);

    // this is always already simplified
    let mut curr_simple = start_term;

    while let Terminator::Jump { target: Target { block, ref args } } = curr_simple {
        let block_info = prog.get_block(block);
        if args.is_empty() && block_info.instructions.is_empty() {
            if !blocks_seen.insert(block) {
                return (skipped, Terminator::LoopForever);
            }
            curr_simple = simplify_terminator(prog, block_info.terminator.clone()).1;
            skipped += 1;
        } else {
            break;
        }
    }

    (skipped, curr_simple)
}