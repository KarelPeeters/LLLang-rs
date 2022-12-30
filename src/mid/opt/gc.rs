use crate::mid::analyse::use_info::for_each_usage_in_instr;
use crate::mid::ir::{Block, BlockInfo, FunctionInfo, Global, Program, Target, Value};
use crate::mid::util::visit::{VisitedResult, Visitor, VisitState};

struct GcVisitor;

impl GcVisitor {
    fn add_target(&mut self, state: &mut VisitState, target: &Target) {
        state.add_block(target.block);
        for &value in &target.phi_values {
            state.add_value(value);
        }
    }
}

impl Visitor for GcVisitor {
    fn visit_value(&mut self, state: &mut VisitState, value: Value) {
        match value {
            Value::Global(Global::Func(func)) => {
                let FunctionInfo {
                    entry, params, slots,
                    ty: _, func_ty: _, global_name: _, debug_name: _
                } = state.prog.get_func(func);

                self.add_target(state, entry);
                for &param in params {
                    state.add_value(param);
                }
                for &slot in slots {
                    state.add_value(slot);
                }
            }
            Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => {
                // no additional tracking here
            }
        }
    }

    fn visit_block(&mut self, state: &mut VisitState, block: Block) {
        let BlockInfo { phis, instructions, terminator } = state.prog.get_block(block);

        for &phi in phis {
            state.add_value(phi);
        }

        for &instr in instructions {
            state.add_value(instr);

            for_each_usage_in_instr((), state.prog.get_instr(instr), |value, _| {
                state.add_value(value);
            });
        }

        terminator.for_each_target(|target| {
            self.add_target(state, target);
        });
    }
}

fn collect_used(prog: &Program) -> VisitedResult {
    let mut state = VisitState::new(prog);
    state.add_value(prog.main);
    state.run(GcVisitor)
}

pub fn gc(prog: &mut Program) -> bool {
    let visited = collect_used(prog);

    let before_count = prog.nodes.total_node_count();

    prog.nodes.funcs.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.params.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.slots.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.blocks.retain(|n, _| visited.visited_blocks.contains(&n));
    prog.nodes.phis.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.instrs.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.exts.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.datas.retain(|n, _| visited.visited_values.contains(&n.into()));

    let after_count = prog.nodes.total_node_count();

    println!("gc removed {}/{} nodes", before_count - after_count, before_count);
    before_count != after_count
}