use indexmap::map::{IndexMap};

use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Program, StackSlot, Terminator, TypeInfo, Value, Type, Parameter};

const HEADER: &str = r"global _main
extern  _ExitProcess@4

section .text";

#[derive(Default)]
struct StackInfo {
    size: i32,
    param_positions: IndexMap<Parameter, i32>,
    slot_positions: IndexMap<StackSlot, i32>,
    instr_positions: IndexMap<Instruction, i32>,
}

struct AsmBuilder<'p> {
    prog: &'p Program,
    string: String,

    stack: StackInfo,

    //TODO make these match the indices in the IR debug format
    block_numbers: IndexMap<Block, usize>,
    func_numbers: IndexMap<Function, usize>,
}

impl AsmBuilder<'_> {
    fn block_number(&mut self, block: Block) -> usize {
        let next_num = self.block_numbers.len();
        *self.block_numbers.entry(block).or_insert(next_num)
    }

    fn func_number(&mut self, func: Function) -> usize {
        let next_num = self.func_numbers.len();
        *self.func_numbers.entry(func).or_insert(next_num)
    }

    fn type_size_in_bytes(&self, ty: Type) -> i32 {
        match self.prog.get_type(ty) {
            TypeInfo::Integer { bits: 32 } => 4,
            //TODO maybe this can be made smaller, what is alignment anyway?
            TypeInfo::Integer { bits: 1 } => 4,
            TypeInfo::Integer { .. } => panic!("Only 32 bit integers and booleans supported for now"),
            TypeInfo::Pointer { .. } | TypeInfo::Func { .. } => 4,
            TypeInfo::Void => 0
        }
    }

    fn append_ln(&mut self, line: &str) {
        self.string.push_str(line);
        self.string.push('\n');
    }

    fn append_instr(&mut self, instr: &str) {
        self.string.push_str("    ");
        self.append_ln(instr);
    }

    fn append_value_to_eax(&mut self, value: Value) {
        match value {
            Value::Undef(_) => {
                self.append_instr(";mov eax, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov eax, {}", cst.value))
            },
            Value::Func(func) => {
                let func_number = self.func_number(func);
                self.append_instr(&format!("mov eax, func_{}", func_number));
            }
            Value::Param(param) => {
                let param_pos = *self.stack.param_positions.get(&param).unwrap();
                self.append_instr(&format!("mov eax, [esp+{}]", self.stack.size - param_pos));
            }
            Value::Slot(slot) => {
                let slot_pos = *self.stack.slot_positions.get(&slot).unwrap();
                self.append_instr(&format!("lea eax, [esp+{}]", self.stack.size - slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.stack.instr_positions.get(&instr).unwrap();
                self.append_instr(&format!("mov eax, [esp+{}]", self.stack.size - instr_pos));
            },
        }
    }

    fn append_stack_pos_to_ebx(&mut self, pos: i32) {
        self.append_instr(&format!("lea ebx, [esp+{}]", self.stack.size - pos));
    }

    fn append_address_to_ebx(&mut self, addr: Value){
        match addr {
            //func as address isn't meaningful
            Value::Undef(_) | Value::Func(_) => {
                self.append_instr(";mov ebx, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov ebx, {}", cst.value));
            },
            Value::Param(param) => {
                self.append_stack_pos_to_ebx(*self.stack.param_positions.get(&param).unwrap());
            }
            Value::Slot(slot) => {
                self.append_stack_pos_to_ebx(*self.stack.slot_positions.get(&slot).unwrap());
            },
            Value::Instr(_) => {
                panic!("this shouldn't happen, instructions are never used as addresses");
            },
        }
    }

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.block_number(block);
        self.append_ln(&format!("  block_{}: ", block_number));

        let block = self.prog.get_block(block);

        //write out instructions
        for &instr in &block.instructions {
            let instr_pos = *self.stack.instr_positions.get(&instr).unwrap();
            match self.prog.get_instr(instr) {
                InstructionInfo::Store { addr, value } => {
                    self.append_instr(";store");
                    self.append_value_to_eax(*value);
                    self.append_address_to_ebx(*addr);
                    self.append_instr("mov [ebx], eax");
                },
                InstructionInfo::Load { addr } => {
                    self.append_instr(";load");
                    self.append_address_to_ebx(*addr);
                    self.append_instr("mov eax, [ebx]");
                    self.append_instr(&format!("mov [esp+{}], eax", self.stack.size - instr_pos));
                },
                InstructionInfo::Call { target, args } => {
                    self.append_instr(";call");

                    //push arguments to stack


                    let mut stack_pos = 8;
                    for &arg in args {
                        self.append_value_to_eax(arg);
                        self.append_instr(&format!("mov [esp-{}], eax", stack_pos));

                        stack_pos += self.type_size_in_bytes(self.prog.type_of_value(arg));
                    }

                    self.append_value_to_eax(*target);
                    self.append_instr("call eax");
                    self.append_instr(&format!("mov [esp+{}], eax", self.stack.size - instr_pos));
                }
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

                self.append_value_to_eax(*cond);

                self.append_instr("test eax, eax");
                self.append_instr(&format!("jnz block_{}", true_block_number));
                self.append_instr(&format!("jmp block_{}", false_block_number));
            },
            Terminator::Return { value } => {
                self.append_value_to_eax(*value);
                //shrink stack
                self.append_instr(&format!("add esp, {}", self.stack.size));
                self.append_instr("ret");
            }
            Terminator::Unreachable => {
                self.append_instr("hlt");
            }
        }
    }

    /// calculate the stack position for each parameter, slot and instruction
    fn calc_stack_positions(&self, func: Function) -> StackInfo {
        let func_info = self.prog.get_func(func);

        let mut stack = StackInfo::default();
        //start at 8 to leave place for return address TODO why 8 and not 4?
        stack.size = 8;

        for &param in &func_info.params {
            stack.param_positions.insert(param, stack.size);
            stack.size += self.type_size_in_bytes(self.prog.get_param(param).ty);
        }

        for &slot in &func_info.slots {
            stack.slot_positions.insert(slot, stack.size);
            stack.size += self.type_size_in_bytes(self.prog.get_slot(slot).ty);
        }

        self.prog.visit_blocks(func, |block| {
            for &instr in &self.prog.get_block(block).instructions {
                stack.instr_positions.insert(instr, stack.size);
                stack.size += self.type_size_in_bytes(self.prog.type_of_value(Value::Instr(instr)));
            }
        });

        stack
    }

    fn append_func(&mut self, func: Function) {
        self.stack = self.calc_stack_positions(func);

        //function label
        let func_number = self.func_number(func);
        self.append_ln(&format!("func_{}:", func_number));

        //grow stack
        self.append_instr(&format!("sub esp, {}", self.stack.size));

        //append actual code
        self.prog.visit_blocks(func, |block| {
            self.append_block(block);
        });
    }

    pub fn lower(&mut self) {
        self.append_ln(HEADER);

        //call main function
        let main_func_number = self.func_number(self.prog.main);
        self.append_ln("_main:");
        self.append_instr(&format!("call func_{}", main_func_number));
        self.append_instr("push eax");
        self.append_instr("call _ExitProcess@4");

        //write out all of the functions
        self.prog.visit_funcs(|func| {
            self.append_func(func)
        });
    }
}

pub fn lower(prog: &Program) -> String {
    let mut asm = AsmBuilder {
        prog,
        string: Default::default(),
        stack: Default::default(),
        block_numbers: Default::default(),
        func_numbers: Default::default(),
    };
    asm.lower();
    asm.string
}