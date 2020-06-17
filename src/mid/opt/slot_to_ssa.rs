use crate::mid::ir::{Program, Function};

pub fn slot_to_ssa(prog: &mut Program) {
    //TODO this is kind of awkward, find a better way to do this
    let mut funcs = Vec::new();
    prog.visit_funcs(|f| funcs.push(f));

    for func in funcs {
        slot_to_ssa_func(prog, func)
    }
}

fn slot_to_ssa_func(prog: &mut Program, func: Function) {
    //calculate dominance graph
    //calculate value usage

    //for each slot only used as load/store address
    //
}

fn dom_graph(prog: &Program, func: Function) {

}

struct UseInfo {

}

fn usage_info(prog: &Program) {

}