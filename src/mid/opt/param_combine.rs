use itertools::{Itertools, zip};

use crate::mid::analyse::dom_info::{DomInfo, DomPosition};
use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Immediate, Program, Value};
use crate::mid::util::lattice::Lattice;

// TODO merge this with SCCP somehow (and make it more general, for all values not just params)
// TODO it's kind of sad that we can't replace things with non-dominating values, could we maybe change the IR semantics
//   to consider non-visited values as undef? -> that loses a lot of verify constraints, is that good or bad?
// TODO otherwise add the "is_strict_dom" check to other passes that replace values
// TODO combine duplicate param/arg pairs somewhere?
/// Replace param values that can only have a single value with that value.
pub fn param_combine(prog: &mut Program) -> bool {
    let mut replaced_params = 0;
    let mut replaced_usages = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for func in funcs {
        let dom_info = DomInfo::new(prog, func);

        'blocks: for &block in dom_info.blocks() {
            // TODO somehow move this outside, but we might invalidate it by accident
            let use_info = UseInfo::new(prog);
            let block_info = prog.get_block(block);

            // combine the args of all targets that jump to this block
            let mut param_values = vec![Lattice::Undef; block_info.params.len()];
            for usage in &use_info[block] {
                match usage {
                    BlockUsage::FuncEntry(_) => {
                        // we can't do anything with this block
                        continue 'blocks;
                    }
                    BlockUsage::Target { pos, kind } => {
                        let target = kind.get_target(&prog.get_block(pos.block).terminator);
                        assert_eq!(param_values.len(), target.args.len());

                        for (curr, &new) in zip(&mut param_values, &target.args) {
                            *curr = Lattice::merge(*curr, value_to_lattice(new));
                        }
                    }
                }
            }

            // try to replace the params with their values
            let params = block_info.params.clone();
            for (&param, &arg) in zip(&params, &param_values) {
                if let Some(value) = arg.as_value_of_type(prog, prog.get_param(param).ty) {
                    // TODO maybe store and look up the def position in use_info instead?
                    let def_pos = DomPosition::find_def_slow(prog, func, value).unwrap();

                    let replacement_count = use_info.replace_value_usages_if(prog, param.into(), value, |usage| {
                        match usage.as_dom_pos() {
                            Ok(use_pos) => dom_info.pos_is_strict_dominator(def_pos, use_pos),
                            // TODO properly check this for expressions and then allow replacing them
                            //   this requires recursing through usages
                            Err(_expr) => false,
                        }
                    });

                    replaced_usages += replacement_count;
                    if replacement_count > 0 {
                        replaced_params += 1;
                    }
                }
            }
        }
    }

    println!("param_combine replaced {} params with {} usages", replaced_params, replaced_usages);
    replaced_params != 0 || replaced_usages != 0
}

fn value_to_lattice(value: Value) -> Lattice {
    match value {
        Value::Immediate(Immediate::Undef(_)) => Lattice::Undef,
        _ => Lattice::Known(value),
    }
}