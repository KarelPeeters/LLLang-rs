use crate::mid::analyse::usage::{for_each_usage_in_expr, for_each_usage_in_instr, for_each_usage_in_term, TermUsage};
use crate::mid::ir::{Block, BlockInfo, FunctionInfo, Global, Program, Value};
use crate::mid::util::visit::{VisitedResult, Visitor, VisitState};

struct GcVisitor;

impl Visitor for GcVisitor {
    fn visit_value(&mut self, state: &mut VisitState, value: Value) {
        match value {
            Value::Global(Global::Func(func)) => {
                let &FunctionInfo {
                    entry, ref slots,
                    ty: _, func_ty: _, debug_name: _
                } = state.prog.get_func(func);

                state.add_block(entry);
                state.add_values(slots.iter().copied());
            }
            Value::Expr(expr) => {
                for_each_usage_in_expr(state.prog.get_expr(expr), |inner, _| {
                    state.add_value(inner);
                })
            }
            Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => {
                // no additional tracking here
            }
        }
    }

    fn visit_block(&mut self, state: &mut VisitState, block: Block) {
        let BlockInfo { params, instructions, terminator } = state.prog.get_block(block);

        state.add_values(params.iter().copied());
        state.add_values(instructions.iter().copied());

        for &instr in instructions {
            for_each_usage_in_instr(state.prog.get_instr(instr), |value, _| {
                state.add_value(value);
            });
        }

        for_each_usage_in_term(
            terminator,
            |usage| match usage {
                TermUsage::Value(value, _) => state.add_value(value),
                TermUsage::Block(block, _) => state.add_block(block),
            },
        );
    }
}

fn collect_used(prog: &Program) -> VisitedResult {
    let mut state = VisitState::new(prog);
    state.add_values(prog.root_functions.values().copied());
    state.run(&mut GcVisitor)
}

pub fn gc(prog: &mut Program) -> bool {
    let visited = collect_used(prog);

    let before_count = prog.nodes.total_node_count();

    prog.nodes.funcs.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.params.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.slots.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.blocks.retain(|n, _| visited.visited_blocks.contains(&n));
    prog.nodes.instrs.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.exprs.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.exts.retain(|n, _| visited.visited_values.contains(&n.into()));
    prog.nodes.datas.retain(|n, _| visited.visited_values.contains(&n.into()));

    let after_count = prog.nodes.total_node_count();

    println!("gc removed {}/{} nodes", before_count - after_count, before_count);
    before_count != after_count
}