use crate::mid::analyse::usage::TermUsage;
use crate::mid::ir::{Block, BlockInfo, FunctionInfo, Global, Program, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::visit::{VisitedResult, Visitor, VisitState};
use crate::util::internal_iter::InternalIterator;

#[derive(Debug)]
pub struct GcPass;

impl ProgramPass for GcPass {
    fn run(&self, prog: &mut Program, _: &mut PassContext) -> PassResult {
        PassResult {
            changed: gc(prog),
            // gc always preserves there, they only care about reachable items
            preserved_dom_info: true,
            preserved_use_info: true,
        }
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

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
                state.prog.get_expr(expr).operands().for_each(|(inner, _)| {
                    state.add_value(inner);
                })
            }
            Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => {
                // no additional tracking here
            }
        }
    }

    fn visit_block(&mut self, state: &mut VisitState, block: Block) {
        let BlockInfo { params, instructions, terminator, debug_name: _ } = state.prog.get_block(block);

        state.add_values(params.iter().copied());
        state.add_values(instructions.iter().copied());

        for &instr in instructions {
            state.prog.get_instr(instr).operands().for_each(|(value, _)| {
                state.add_value(value);
            });
        }

        terminator.operands().for_each(|usage| {
            match usage {
                TermUsage::Value(value, _) => state.add_value(value),
                TermUsage::Block(block, _) => state.add_block(block),
            }
        });
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