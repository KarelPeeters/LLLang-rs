use std::collections::HashMap;

use crate::mid::ir::{Const, InstructionInfo, Program, StackSlot, Terminator, Value};

fn address_unwrap_slot(value: &Value) -> &StackSlot {
    if let Value::Slot(slot) = value {
        slot
    } else {
        panic!("only slot addresses supported for now")
    }
}

struct Emulator {
    memory: HashMap<Value, Const>,
}

impl Emulator {
    fn eval(&mut self, value: Value) -> Const {
        if let Value::Const(cst) = value {
            cst
        } else {
            if let Some(&cst) = self.memory.get(&value) {
                cst
            } else {
                panic!("attempt to use {:?} as value, not yet supported", value)
            }
        }
    }

    fn run(&mut self, prog: &Program) -> Const {
        let func = prog.get_func(prog.main);
        let block = prog.get_block(func.entry);

        for &instr in &block.instructions {
            let instr_info = prog.get_instr(instr);
            match instr_info {
                InstructionInfo::Load { addr } => {
                    let value = self.eval(*addr);
                    self.memory.insert(Value::Instr(instr), value);
                }
                InstructionInfo::Store { addr, value } => {
                    let value = self.eval(*value);
                    self.memory.insert(*addr, value);
                }
            }
        }

        match block.terminator {
            Terminator::Jump { .. } | Terminator::Branch { .. } =>
                todo!("control flow in emulator"),
            Terminator::Return { value } => return self.eval(value),
            Terminator::Unreachable => panic!("Reached Unreachable"),
        }
    }
}

pub fn run(prog: &Program) -> Const {
    let mut emulator = Emulator { memory: Default::default() };
    emulator.run(prog)
}
