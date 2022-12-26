use std::collections::VecDeque;

use itertools::Itertools;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::ir::{BlockInfo, Program, Target, Terminator};

pub fn split_critical_edges(prog: &mut Program) -> bool {
    let mut split_edges = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for &func in &funcs {
        let dom_info = DomInfo::new(prog, func);

        for &block in &dom_info.blocks {
            let mut terminator = prog.get_block(block).terminator.clone();
            let mut replacement_targets = VecDeque::new();

            terminator.for_each_target_mut(|target| {
                let replacement = if dom_info.iter_predecessors(target.block).count() > 1 {
                    // we've found a critical edge, split it
                    split_edges += 1;

                    let dummy_target = Target { block: target.block, phi_values: vec![] };
                    let target = std::mem::replace(target, dummy_target);

                    let new_block = prog.define_block(BlockInfo {
                        phis: vec![],
                        instructions: vec![],
                        terminator: Terminator::Jump { target },
                    });

                    Some(Target { block: new_block, phi_values: vec![] })
                } else {
                    None
                };

                replacement_targets.push_back(replacement);
            });

            prog.get_block_mut(block).terminator.for_each_target_mut(|target| {
                if let Some(replacement) = replacement_targets.pop_front().unwrap() {
                    *target = replacement;
                }
            });
        }
    }

    split_edges > 0
}