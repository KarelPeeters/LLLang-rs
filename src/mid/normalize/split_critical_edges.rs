use std::cmp::max;
use std::collections::VecDeque;

use itertools::Itertools;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::ir::{BlockInfo, Program, Target, Terminator};
use crate::util::internal_iter::InternalIterator;

pub fn split_critical_edges(prog: &mut Program) -> bool {
    let mut split_edges = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for &func in &funcs {
        let dom_info = DomInfo::new(prog, func);

        for &block in dom_info.blocks() {
            let terminator = prog.get_block(block).terminator.clone();
            let mut replacement_targets = VecDeque::new();

            terminator.targets().for_each(|(target, _)| {
                // check if the target block is critical
                let target_count = terminator.targets()
                    .filter(|(other, _)| other.block == target.block)
                    .count();

                let pred_count = max(
                    dom_info.iter_predecessors(target.block).count(),
                    target_count,
                );
                let is_critical = pred_count > 1;

                let replacement = if is_critical {
                    // split the current critical edge
                    let target = target.clone();

                    let new_block = prog.define_block(BlockInfo {
                        params: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump { target },
                        debug_name: None, // TODO proper debug name
                    });

                    Some(Target { block: new_block, args: vec![] })
                } else {
                    None
                };

                replacement_targets.push_back(replacement);
            });

            prog.get_block_mut(block).terminator.targets_mut().for_each(|(target, _)| {
                if let Some(replacement) = replacement_targets.pop_front().unwrap() {
                    *target = replacement;
                    split_edges += 1;
                }
            });
        }
    }

    println!("split {} critical edges", split_edges);
    split_edges > 0
}