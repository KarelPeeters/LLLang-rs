use std::cmp::max;
use std::collections::VecDeque;

use itertools::Itertools;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::ir::{BlockInfo, Program, Target, Terminator};

pub fn split_critical_edges(prog: &mut Program) -> bool {
    let mut split_edges = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for &func in &funcs {
        let dom_info = DomInfo::new(prog, func);

        for &block in dom_info.blocks() {
            let terminator = prog.get_block(block).terminator.clone();
            let mut replacement_targets = VecDeque::new();

            terminator.for_each_target(|target, _| {
                // check if the target block is critical
                let mut target_count = 0;
                terminator.for_each_target(|other, _| target_count += (other.block == target.block) as usize);
                let pred_count = max(
                    dom_info.iter_predecessors(target.block).count(),
                    target_count
                );
                let is_critical = pred_count > 1;

                let replacement = if is_critical {
                    // split the current critical edge
                    let target = target.clone();

                    let new_block = prog.define_block(BlockInfo {
                        params: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump { target },
                    });

                    Some(Target { block: new_block, args: vec![] })
                } else {
                    None
                };

                replacement_targets.push_back(replacement);
            });

            prog.get_block_mut(block).terminator.for_each_target_mut(|target, _| {
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