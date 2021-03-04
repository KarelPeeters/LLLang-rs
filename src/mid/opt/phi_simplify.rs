use crate::mid::ir::{Program, Phi, Target, Function};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::analyse::dom_info::DomInfo;
use itertools::Itertools;

pub fn phi_simplify(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let mut count = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();

    for &func in &funcs {
        count += phi_simplify_func(prog, &use_info, func);
    }

    println!("phi_simplify simplified {} phi nodes", count);
    count != 0
}

fn phi_simplify_func(prog: &mut Program, use_info: &UseInfo, func: Function) -> usize {
    let dom_info = DomInfo::new(prog, func);
    let mut count = 0;

    for block in &dom_info.blocks {
        let block_info = prog.get_block(block);

        //TODO do we need to the lattice stuff here? can't that be done as part of SCCP?
        // TODO here we only need to optimize the placement of phi nodes, not their values
    }

    count
}