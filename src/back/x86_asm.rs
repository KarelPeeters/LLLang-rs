use std::collections::HashMap;

use crate::mid::ir::{Block, Instruction, InstructionInfo, Program, StackSlot, Terminator, TypeInfo, Value};

const HEADER: &str = r"global _main
extern  _ExitProcess@4

section .text
_main:";

fn type_size_in_bytes(ty: &TypeInfo) -> i32 {
    match ty {
        TypeInfo::Integer { bits } => {
            assert!(*bits == 32 || *bits == 1, "only 32 bits int and bool supported for now");
            4
        },
        TypeInfo::Pointer { .. } | TypeInfo::Func { .. } => 4, //TODO support non-32-bit later
        TypeInfo::Void => {
            //TODO this needs to be handled specially by load and store code
            //  maybe even remove the Void type from the IR? is it actually necessary?
            panic!("void type not supported")
        },
    }
}

struct AsmBuilder<'p> {
    prog: &'p Program,
    string: String,
    slot_stack_positions: HashMap<StackSlot, i32>,
    instr_stack_positions: HashMap<Instruction, i32>,
    //TODO make these match the indices in the IR debug format
    block_numbers: HashMap<Block, usize>,
}

impl AsmBuilder<'_> {
    fn block_number(&mut self, block: Block) -> usize {
        let next_num = self.block_numbers.len();
        *self.block_numbers.entry(block).or_insert(next_num)
    }

    fn append_ln(&mut self, line: &str) {
        self.string.push_str(line);
        self.string.push('\n');
    }

    fn append_instr(&mut self, instr: &str) {
        self.string.push_str("    ");
        self.append_ln(instr);
    }

    fn append_value_to_eax(&mut self, value: &Value) {
        match value {
            Value::Undef(_) => {
                self.append_instr(";mov eax, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov eax, {}", cst.value))
            },
            Value::Func(_func) => {
                todo!("func as value in x86")
            }
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.append_instr(&format!("lea eax, [esp-{}]", slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.append_instr(&format!("mov eax, [esp-{}]", instr_pos));
            },
        }
    }

    fn append_address_to_ebx(&mut self, addr: &Value){
        match addr {
            //func as address isn't meaningful
            Value::Undef(_) | Value::Func(_) => {
                self.append_instr(";mov ebx, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov ebx, {}", cst.value));
            },
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.append_instr(&format!("lea ebx, [esp-{}]", slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.append_instr(&format!("mov ebx, [esp-{}]", instr_pos));
            },
        }
    }

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.block_number(block);
        self.append_ln(&format!("  block_{}: ", block_number));

        let block = self.prog.get_block(block);

        //write out instructions
        for &instr in &block.instructions {
            match self.prog.get_instr(instr) {
                InstructionInfo::Store { addr, value } => {
                    self.append_instr(";store");
                    self.append_value_to_eax(value);
                    self.append_address_to_ebx(addr);
                    self.append_instr("mov [ebx], eax");
                },
                InstructionInfo::Load { addr } => {
                    self.append_instr(";load");
                    self.append_address_to_ebx(addr);
                    self.append_instr("mov eax, [ebx]");

                    let instr_pos = *self.instr_stack_positions.get(&instr).unwrap();
                    self.append_instr(&format!("mov [esp-{}], eax", instr_pos));
                },
            }
        }

        self.append_instr(";terminator");
        match &block.terminator {
            Terminator::Jump { target} => {
                let block_number = self.block_number(*target);
                self.append_instr(&format!("jmp block_{}", block_number));
            },
            Terminator::Branch { cond, targets: [true_block, false_block] } => {
                let true_block_number = self.block_number(*true_block);
                let false_block_number = self.block_number(*false_block);

                self.append_value_to_eax(cond);

                self.append_instr("test eax, eax");
                self.append_instr(&format!("jnz block_{}", true_block_number));
                self.append_instr(&format!("jmp block_{}", false_block_number));
            },
            Terminator::Return { value } => {
                self.append_value_to_eax(value);
                self.append_instr("push eax");
                self.append_instr("call _ExitProcess@4");
            }
            Terminator::Unreachable => {
                self.append_instr("hlt");
            }
        }
    }

    pub fn lower(&mut self) {
        self.append_ln(HEADER);

        let func = self.prog.main;
        let func_info = self.prog.get_func(func);

        //determine the stack position for each slot and value-returning instruction
        let mut stack_size = 0;

        for &slot in &func_info.slots {
            let ty = self.prog.get_type(self.prog.get_slot(slot).inner_ty);
            let size = type_size_in_bytes(ty);

            self.slot_stack_positions.insert(slot, stack_size);
            stack_size += size;
        }

        self.prog.visit_blocks(func, |block| {
            for &instr in &self.prog.get_block(block).instructions {
                match self.prog.get_instr(instr) {
                    InstructionInfo::Load { addr } => {
                        let ty = self.prog.get_type(self.prog.get_type(self.prog.type_of_value(*addr))
                            .as_ptr().expect("address should have pointer type"));

                        self.instr_stack_positions.insert(instr, stack_size);
                        stack_size += type_size_in_bytes(ty);
                    },
                    InstructionInfo::Store { .. } => {},
                }
            }
        });

        //write out blocks
        self.prog.visit_blocks(func, |block| {
            self.append_block(block);
        });
    }
}

pub fn lower(prog: &Program) -> String {
    let mut asm = AsmBuilder {
        prog,
        string: "".to_string(),
        slot_stack_positions: Default::default(),
        instr_stack_positions: Default::default(),
        block_numbers: Default::default()
    };
    asm.lower();
    asm.string
}