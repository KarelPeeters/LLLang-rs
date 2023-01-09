use std::collections::HashSet;

use itertools::Itertools;

use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Program, Scoped, Target, Terminator, Value};
use crate::util::VecExt;

/// Skip over blocks whose only purpose is to shuffle some params/args around,
/// by instead jumping directly to the successor block.
// TODO combine this with flow_simplify?
pub fn phi_pushing(prog: &mut Program) -> bool {
    let mut changed_terminators = 0;

    // blocks that are blacklisted, either because it's the entry block or because we've changed this block already
    // TODO can we do more stuff in a single pass?
    let mut blacklist = HashSet::new();

    let use_info = UseInfo::new(prog);

    for func in use_info.funcs() {
        let func_entry = prog.get_func(func).entry;
        blacklist.clear();
        blacklist.insert(func_entry);

        for &block in use_info.func_blocks(func) {
            let block_info = prog.get_block(block);

            // ensure we can skip this block: no instructions, jump terminator, no blacklist block on either side
            if blacklist.contains(&block) || !block_info.instructions.is_empty() {
                continue;
            }
            let target = if let Terminator::Jump { target } = &block_info.terminator {
                if target.block == block || blacklist.contains(&target.block) {
                    continue;
                }
                target.clone()
            } else {
                continue;
            };

            // we can skip this block, start taking it apart
            let Target { block: target_block, args: target_args } = target;

            // remove phis from old block
            let mut old_params = std::mem::take(&mut prog.get_block_mut(block).params);
            let old_param_types = old_params.iter().map(|&phi| prog.get_param(phi).ty).collect_vec();

            // add undef args to other uses of the target block
            for usage in &use_info[target_block] {
                let (pred_pos, kind) = unwrap_match!(usage, BlockUsage::Target { pos, kind } => (pos, kind));
                let target = kind.get_target_mut(&mut prog.get_block_mut(pred_pos.block).terminator);
                target.args.extend(old_param_types.iter().map(|&ty| Value::undef(ty)));
            }

            // add old params to the target params
            for usage in &use_info[block] {
                assert!(!use_info[target_block].contains(usage), "Trying to change usage we already added undefs to");

                changed_terminators += 1;

                let (pred_pos, kind) = unwrap_match!(usage, BlockUsage::Target { pos, kind } => (pos, kind));
                let target = kind.get_target_mut(&mut prog.get_block_mut(pred_pos.block).terminator);
                blacklist.insert(pred_pos.block);

                let Target { block: pred_target_block, args: old_pred_args } = target;

                // replace the target with the skipped block
                *pred_target_block = target_block;

                // insert replaced phi values at the start of the block
                let mut new_pred_phi_values = target_args.iter().map(|&value| {
                    if let Value::Scoped(Scoped::Param(param)) = value {
                        if let Some(index) = old_params.index_of(&param) {
                            return old_pred_args[index];
                        }
                    }
                    value
                }).collect_vec();
                new_pred_phi_values.append(old_pred_args);
                *old_pred_args = new_pred_phi_values;
            }

            // add phis to new block
            prog.get_block_mut(target_block).params.append(&mut old_params);
            blacklist.insert(target_block);
        }
    }

    println!("changed_terminators changed {} terminators", changed_terminators);
    changed_terminators != 0
}
