use itertools::Itertools;
use crate::mid::ir::{BlockInfo, Program, Target, Terminator};

pub fn ensure_no_entry_phi_args(prog: &mut Program) {
    let funcs = prog.nodes.funcs.keys().collect_vec();

    for func in funcs {
        let entry = &mut prog.nodes.funcs[func].entry;

        if entry.phi_values.len() > 0 {
            let new_block = prog.nodes.blocks.push(BlockInfo {
                phis: vec![],
                instructions: vec![],
                terminator: Terminator::Jump { target: entry.clone() },
            });

            *entry = Target {
                block: new_block,
                phi_values: vec![],
            };
        }
    }
}
