use itertools::{Itertools, zip};

use crate::mid::analyse::dom_info::{DomInfo, DomPosition};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Immediate, Program, Value};
use crate::mid::util::lattice::Lattice;

// TODO merge this with SCCP somehow (and make it more general, for all values not just phis)
// TODO it's kind of sad that we can't replace things with non-dominating values, could we maybe change the IR semantics
//   to consider non-visited values as undef? -> that loses a lot of verify constraints, is that good or bad?
// TODO otherwise add the "is_strict_dom" check to other passes that replace values
/// Replace phi values that can only have a single value with that value.
pub fn phi_combine(prog: &mut Program) -> bool {
    let mut replaced_phis = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for func in funcs {
        let dom_info = DomInfo::new(prog, func);

        for &block in &dom_info.blocks {
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
                if let Some(value) = phi_value.as_value_of_type(prog, prog.get_phi(phi).ty) {
                    // TODO maybe store and look up the def position in use_info instead?
                    let def_pos = DomPosition::find_def_slow(prog, func, value).unwrap();

                    let replacement_count = use_info.replace_value_usages_if(prog, phi.into(), value, |usage| {
                        let use_pos = usage.as_dom_pos();
                        dom_info.pos_is_strict_dominator(def_pos, use_pos)
                    });

                    if replacement_count > 0 {
                        replaced_phis += 1;
                    }
                }
            }
        }
    }

    println!("phi_combine replaced {} phis", replaced_phis);
    replaced_phis != 0
}

fn value_to_lattice(value: Value) -> Lattice {
    match value {
        Value::Immediate(Immediate::Void | Immediate::Undef(_)) => Lattice::Undef,
        Value::Immediate(Immediate::Const(_)) | Value::Global(_) | Value::Scoped(_) => Lattice::Known(value),
    }
}