use crate::mid::ir::{Program, Terminator, Value, TypeInfo, InstructionInfo, Instruction, StackSlot};
use std::collections::HashMap;

const HEADER: &str = r"
global _main
extern  _ExitProcess@4

section .text
_main:";

fn type_size_in_bytes(ty: &TypeInfo) -> i32 {
    match ty {
        TypeInfo::Integer { bits } => {
            assert_eq!(*bits, 32, "only 32 bit ints supported for now");
            4
        },
        TypeInfo::Pointer { .. } => 4, //TODO support non-32-bit later
        TypeInfo::Void => {
            //TODO this needs to be handled specially by load and store code
            //  maybe even remove the Void type from the IR? is it actually necessary?
            panic!("void type not supported")
        },
    }
}

#[derive(Default)]
struct AsmBuilder {
    string: String,
    slot_stack_positions: HashMap<StackSlot, i32>,
    instr_stack_positions: HashMap<Instruction, i32>,
}

impl AsmBuilder {
    fn line(&mut self, line: &str) {
        self.string.push_str(line);
        self.string.push('\n');
    }

    fn value_to_eax(&mut self, value: &Value) {
        match value {
            Value::Const(cst) => {
                self.line(&format!("mov eax, {}", cst.value))
            },
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.line(&format!("lea eax, [esp-{}]", slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.line(&format!("mov eax, [esp-{}]", instr_pos));
            },
        }
    }

    fn address_to_ebx(&mut self, addr: &Value){
        match addr {
            Value::Const(cst) => {
                self.line(&format!("mov ebx, {}", cst.value));
            },
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.line(&format!("lea ebx, [esp-{}]", slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.line(&format!("mov ebx, [esp-{}]", instr_pos));
            },
        }
    }

    pub fn lower(&mut self, prog: &Program) {
        self.line(HEADER);

        let main = prog.get_func(prog.main);
        let entry = prog.get_block(main.entry);

        //determine the stack position for each slot and value-returning instruction
        let mut stack_size = 0;

        for &slot in &main.slots {
            let ty = prog.get_type(prog.get_slot(slot).inner_ty);
            let size = type_size_in_bytes(ty);

            self.slot_stack_positions.insert(slot, stack_size);
            stack_size += size;
        }

        for &instr in &entry.instructions {
            match prog.get_instr(instr) {
                InstructionInfo::Load { addr } => {
                    let ty = prog.get_type(prog.get_type(prog.type_of_value(*addr)).unwrap_ptr());

                    self.instr_stack_positions.insert(instr, stack_size);
                    stack_size += type_size_in_bytes(ty);
                },
                InstructionInfo::Store { .. } => {},
            }
        }

        //write out instructions
        for &instr in &entry.instructions {
            match prog.get_instr(instr) {
                InstructionInfo::Store { addr, value } => {
                    self.line(";store");
                    self.value_to_eax(value);
                    self.address_to_ebx(addr);
                    self.line("mov [ebx], eax");
                },
                InstructionInfo::Load { addr } => {
                    self.line(";load");
                    self.address_to_ebx(addr);
                    self.line("mov eax, [ebx]");

                    let instr_pos = *self.instr_stack_positions.get(&instr).unwrap();
                    self.line(&format!("mov [esp-{}], eax", instr_pos));
                },
            }
        }

        self.line(";terminator");
        match &entry.terminator {
            Terminator::Return { value } => {
                self.value_to_eax(value);
                self.line("push eax");
                self.line("call _ExitProcess@4");
            }
            Terminator::Unreachable => {
                self.line("hlt");
            }
        }
    }
}

pub fn lower(prog: &Program) -> String {
    let mut asm: AsmBuilder = Default::default();
    asm.lower(prog);
    asm.string
}