use itertools::{Itertools, zip};

use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Program, Value};
use crate::mid::util::lattice::Lattice;

// TODO merge this with SCCP somehow (and make it more general, for all values not just phis)
/// Replace phi values that can only have a single value with that value.
pub fn phi_combine(prog: &mut Program) -> bool {
    let mut replaced_phis = 0;

    let blocks = prog.nodes.blocks.keys().collect_vec();
    for &block in &blocks {
        // TODO somehow move this outside, but we might invalidate it by accident
        let use_info = UseInfo::new(prog);
        let block_info = prog.get_block(block);

        // combine phi values of all targets that jump to this block
        let mut phi_values = vec![Lattice::Undef; block_info.phis.len()];
        for usage in &use_info[block] {
            let target = usage.target_kind.get_target(prog);
            assert_eq!(phi_values.len(), target.phi_values.len());

            for (curr, &new) in zip(&mut phi_values, &target.phi_values) {
                *curr = Lattice::merge(*curr, value_to_lattice(new));
            }
        }

        // try to replace the phis with their values
        let phis = block_info.phis.clone();
        for (&phi, &phi_value) in zip(&phis, &phi_values) {
            if let Some(value) = phi_value.as_value_of_type(prog.get_phi(phi).ty) {
                replaced_phis += 1;
                use_info.replace_value_usages(prog, phi.into(), value);
            }
        }
    }

    println!("phi_combine replaced {} phis", replaced_phis);
    replaced_phis != 0
}

fn value_to_lattice(value: Value) -> Lattice {
    match value {
        Value::Undef(_) => Lattice::Undef,
        Value::Const(_) | Value::Func(_) | Value::Param(_) | Value::Slot(_) |
        Value::Phi(_) | Value::Instr(_) | Value::Extern(_) | Value::Data(_) => Lattice::Known(value),
    }
}