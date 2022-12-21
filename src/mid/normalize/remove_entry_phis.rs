use itertools::Itertools;
use crate::mid::ir::{BlockInfo, Program, Target, Terminator};

pub fn remove_entry_phis(prog: &mut Program) -> bool {
    let mut changed_entries = 0;
    let funcs = prog.nodes.funcs.keys().collect_vec();

    for func in funcs {
        let entry = &mut prog.nodes.funcs[func].entry;

        if entry.phi_values.len() > 0 {
            changed_entries += 1;
            
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

    println!("remove_entry_phis changed {} entries", changed_entries);
    changed_entries > 0
}
