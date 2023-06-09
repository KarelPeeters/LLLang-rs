use itertools::{Itertools, zip};

use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::analyse::value_dom::value_strictly_dominates_usage_slow;
use crate::mid::ir::{Immediate, Program, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::lattice::Lattice;

/// Replace param values that can only have a single value with that value.
#[derive(Debug)]
pub struct ParamCombinePass;

impl ProgramPass for ParamCombinePass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let changed = param_combine(prog, ctx);
        PassResult {
            changed,
            preserved_dom_info: true,
            preserved_use_info: !changed,
        }
    }

    fn is_idempotent(&self) -> bool {
        // TODO can we make this idempotent?
        false
    }
}

// TODO merge this with SCCP somehow (and make it more general, for all values not just params)
// TODO combine duplicate param/arg pairs somewhere?
fn param_combine(prog: &mut Program, ctx: &mut PassContext) -> bool {
    let mut replaced_params = 0;
    let mut replaced_usages = 0;

    let funcs = prog.nodes.funcs.keys().collect_vec();
    for func in funcs {
        let dom_info = ctx.dom_info(prog, func);

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
                    let replacement_count = use_info.replace_value_usages_if(prog, param.into(), value, |prog, usage| {
                        value_strictly_dominates_usage_slow(prog, &dom_info, &use_info, value, usage).unwrap()
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