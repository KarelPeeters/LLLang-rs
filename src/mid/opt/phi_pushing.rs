use itertools::Itertools;

use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Program, Target, Terminator, Value};
use crate::util::VecExt;

pub fn phi_pushing(prog: &mut Program) -> bool {
    let mut changed_terminators = 0;

    let use_info = UseInfo::new(prog);

    for block in use_info.blocks() {
        let block_info = prog.get_block(block);
        if !block_info.instructions.is_empty() {
            // we can't handle this
            continue;
        }
        let target = if let Terminator::Jump { target } = &block_info.terminator {
            if target.block == block {
                continue;
            }
            target.clone()
        } else {
            continue;
        };

        let Target { block: target_block, phi_values: target_phi_values } = target;

        // remove phis from old block
        let mut old_phis = std::mem::take(&mut prog.get_block_mut(block).phis);
        let old_phi_types = old_phis.iter().map(|&phi| prog.get_phi(phi).ty).collect_vec();

        // add undef phi values to other uses of the target block
        for usage in &use_info[target_block] {
            usage.target_kind.get_target_mut(prog)
                .phi_values.extend(old_phi_types.iter().map(|&ty| Value::Undef(ty)));
        }

        // add old phi values to the target phi values
        for usage in &use_info[block] {
            assert!(!use_info[target_block].contains(usage), "Trying to change usage we already added undefs to");

            changed_terminators += 1;

            let Target { block: pred_target_block, phi_values: old_pred_phi_values } =
                usage.target_kind.get_target_mut(prog);

            // replace the target with the skipped block
            *pred_target_block = target_block;

            // insert replaced phi values at the start of the block
            let mut new_pred_phi_values = target_phi_values.iter().map(|&value| {
                if let Value::Phi(phi) = value {
                    if let Some(index) = old_phis.index_of(&phi) {
                        return old_pred_phi_values[index];
                    }
                }
                value
            }).collect_vec();
            new_pred_phi_values.append(old_pred_phi_values);
            *old_pred_phi_values = new_pred_phi_values;
        }

        // add phis to new block
        prog.get_block_mut(target_block).phis.append(&mut old_phis);
    }

    changed_terminators != 0
}
