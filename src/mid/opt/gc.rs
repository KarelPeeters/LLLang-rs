use std::collections::{HashSet, VecDeque};

use crate::mid::ir::{Block, BlockInfo, Function, FunctionInfo, InstructionInfo, Program, Value};

#[derive(Default)]
struct Visited {
    used_blocks: HashSet<Block>,
    used_values: HashSet<Value>,
    funcs: VecDeque<Function>,
    blocks: VecDeque<Block>,
}

impl Visited {
    fn add_value(&mut self, value: Value) {
        if self.used_values.insert(value) {
            match value {
                Value::Func(func) => {
                    //queue this function for visiting
                    self.funcs.push_back(func)
                }
                Value::Undef(_) | Value::Const(_) | Value::Param(_) | Value::Slot(_) |
                Value::Instr(_) | Value::Extern(_) | Value::Data(_) | Value::Phi(_) => {
                    //there are only tracked as values
                }
            }
        }
    }

    fn add_block(&mut self, block: Block) {
        if self.used_blocks.insert(block) {
            self.blocks.push_back(block)
        }
    }
}

fn collect_used(prog: &Program) -> Visited {
    let mut todo = Visited::default();
    todo.add_value(Value::Func(prog.main));

    while let Some(func) = todo.funcs.pop_front() {
        let FunctionInfo { ty: _, func_ty: _, global_name: _, entry, params, slots }
            = prog.get_func(func);

        todo.add_block(entry.block);
        for &param in params {
            todo.add_value(Value::Param(param));
        }
        for &slot in slots {
            todo.add_value(Value::Slot(slot));
        }

        while let Some(block) = todo.blocks.pop_front() {
            let BlockInfo { phis, instructions, terminator } = prog.get_block(block);

            for &phi in phis {
                todo.add_value(Value::Phi(phi));
            }

            for instr in instructions {
                todo.add_value(Value::Instr(*instr));

                match prog.get_instr(*instr) {
                    InstructionInfo::Load { addr } => {
                        todo.add_value(*addr);
                    }
                    InstructionInfo::Store { addr, value } => {
                        todo.add_value(*addr);
                        todo.add_value(*value);
                    }
                    InstructionInfo::Call { target, args } => {
                        todo.add_value(*target);
                        for arg in args {
                            todo.add_value(*arg);
                        }
                    }
                    InstructionInfo::Arithmetic { left, right, kind: _ } |
                    InstructionInfo::Comparison { left, right, kind: _ } => {
                        todo.add_value(*left);
                        todo.add_value(*right);
                    }
                    InstructionInfo::TupleFieldPtr { base, index: _, result_ty: _ } => {
                        todo.add_value(*base);
                    }
                }
            }

            terminator.for_each_successor(|succ| {
                todo.add_block(succ);
            });
        }
    }

    todo
}

pub fn gc(prog: &mut Program) -> bool {
    let visited = collect_used(prog);

    let before_count = prog.nodes.total_node_count();

    prog.nodes.funcs.retain(|n, _| visited.used_values.contains(&Value::Func(n)));
    prog.nodes.params.retain(|n, _| visited.used_values.contains(&Value::Param(n)));
    prog.nodes.slots.retain(|n, _| visited.used_values.contains(&Value::Slot(n)));
    prog.nodes.blocks.retain(|n, _| visited.used_blocks.contains(&n));
    prog.nodes.phis.retain(|n, _| visited.used_values.contains(&Value::Phi(n)));
    prog.nodes.instrs.retain(|n, _| visited.used_values.contains(&Value::Instr(n)));
    prog.nodes.exts.retain(|n, _| visited.used_values.contains(&Value::Extern(n)));
    prog.nodes.datas.retain(|n, _| visited.used_values.contains(&Value::Data(n)));

    let after_count = prog.nodes.total_node_count();

    println!("gc removed {}/{} nodes", before_count - after_count, before_count);
    before_count != after_count
}