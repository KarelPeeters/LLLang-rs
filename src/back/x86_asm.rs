use indexmap::map::IndexMap;

use crate::mid::ir::{BinaryOp, Block, Function, Instruction, InstructionInfo, Program, StackSlot, Terminator, TypeInfo, Value, Parameter};

const HEADER: &str = r"global _main
extern  _ExitProcess@4

section .text";

fn type_size_in_bytes(ty: &TypeInfo) -> i32 {
    match ty {
        TypeInfo::Integer { bits: 32 } => 4,
        //TODO maybe this can be made smaller, what is alignment anyway?
        TypeInfo::Integer { bits: 1 } => 4,
        TypeInfo::Integer { .. } => panic!("Only 32 bit integers and booleans supported for now"),
        TypeInfo::Pointer { .. } | TypeInfo::Func { .. } => 4,
        TypeInfo::Void => 0
    }
}

struct AsmBuilder<'p> {
    prog: &'p Program,
    string: String,
    stack_size: i32,
    param_stack_positions: IndexMap<Parameter, i32>,
    slot_stack_positions: IndexMap<StackSlot, i32>,
    instr_stack_positions: IndexMap<Instruction, i32>,
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

    fn append_ln(&mut self, line: &str) {
        self.string.push_str(line);
        self.string.push('\n');
    }

    fn append_instr(&mut self, instr: &str) {
        self.string.push_str("    ");
        self.append_ln(instr);
    }

    /// ```
    /// eax = value
    /// ```
    fn append_value_to_eax(&mut self, value: &Value) {
        match value {
            Value::Undef(_) => {
                self.append_instr(";mov eax, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov eax, {}", cst.value))
            },
            Value::Func(func) => {
                let func_number = self.func_number(*func);
                self.append_instr(&format!("mov eax, func_{}", func_number));
            }
            Value::Param(param) => {
                let param_pos = *self.param_stack_positions.get(param).unwrap();
                self.append_instr(&format!("mov eax, [esp+{}]", self.stack_size + param_pos));
            }
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.append_instr(&format!("lea eax, [esp+{}]", self.stack_size - slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.append_instr(&format!("mov eax, [esp+{}]", self.stack_size - instr_pos));
            },
        }
    }

    /// ```
    /// ebx = addr
    /// ```
    fn append_address_to_ebx(&mut self, addr: &Value){
        match addr {
            //func as address isn't meaningful
            Value::Undef(_) | Value::Func(_) => {
                self.append_instr(";mov ebx, undef") //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov ebx, {}", cst.value));
            },
            Value::Param(_param) => {
                //TODO is this true?
                panic!("Parameters don't have an address")
            }
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.append_instr(&format!("lea ebx, [esp+{}]", self.stack_size - slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.append_instr(&format!("mov ebx, [esp+{}]", self.stack_size - instr_pos));
            },
        }
    }

    /// ```
    /// eax = eax / ebx
    /// edx = eax % ebx
    /// ```
    fn append_div(&mut self) {
        self.append_instr("xor edx, edx");
        self.append_instr("idiv ebx");
    }

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.block_number(block);
        self.append_ln(&format!("  block_{}: ", block_number));

        let block = self.prog.get_block(block);

        //write out instructions
        for &instr in &block.instructions {
            let instr_pos = *self.instr_stack_positions.get(&instr).unwrap();
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
                    self.append_instr(&format!("mov [esp+{}], eax", self.stack_size - instr_pos));
                },
                InstructionInfo::Call { target, args } => {
                    self.append_instr(";call");

                    //temporarily increase stack size for parameters
                    let arg_size: i32 = args.iter().map(|&arg|
                        type_size_in_bytes(self.prog.get_type(self.prog.type_of_value(arg)))).sum();
                    self.stack_size += arg_size;
                    self.append_instr(&format!("sub esp, {}", arg_size));

                    //write arguments to stack
                    let mut curr_pos = 0;
                    for arg in args {
                        self.append_value_to_eax(arg);
                        self.append_instr(&format!("mov [esp+{}], eax", curr_pos));
                        curr_pos += type_size_in_bytes(self.prog.get_type(self.prog.type_of_value(*arg)));
                    }

                    //actual call
                    self.append_value_to_eax(target);
                    self.append_instr("call eax");
                    self.append_instr(&format!("mov [esp+{}], eax", self.stack_size - instr_pos));

                    //restore stack
                    self.stack_size -= arg_size;
                    self.append_instr(&format!("add esp, {}", arg_size));
                }
                InstructionInfo::Binary { kind, left, right } => {
                    self.append_instr(";binop");
                    self.append_value_to_eax(right);
                    self.append_instr("mov ebx, eax");
                    self.append_value_to_eax(left);

                    //eax = op(eax, ebx)
                    match kind {
                        BinaryOp::Add => self.append_instr("add eax, ebx"),
                        BinaryOp::Sub => self.append_instr("sub eax, ebx"),
                        BinaryOp::Mul => self.append_instr("imul eax, ebx"),
                        BinaryOp::Div => self.append_div(),
                        BinaryOp::Mod => {
                            self.append_div();
                            self.append_instr("mov eax, edx");
                        }
                        BinaryOp::Eq => {
                            self.append_instr("xor ecx, ecx");
                            self.append_instr("cmp eax, ebx");
                            self.append_instr("sete cl");
                            self.append_instr("mov eax, ecx");
                        },
                        BinaryOp::Neq => {
                            self.append_instr("xor ecx, ecx");
                            self.append_instr("cmp eax, ebx");
                            self.append_instr("setne cl");
                            self.append_instr("mov eax, ecx");
                        },
                    }

                    self.append_instr(&format!("mov [esp+{}], eax", self.stack_size - instr_pos));
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
                //shrink stack
                self.append_instr(&format!("add esp, {}", self.stack_size));
                self.append_instr("ret");
            }
            Terminator::Unreachable => {
                self.append_instr("hlt");
            }
        }
    }

    fn append_func(&mut self, func: Function) {
        let func_info = self.prog.get_func(func);
        self.param_stack_positions.clear();
        self.slot_stack_positions.clear();
        self.instr_stack_positions.clear();

        //determine the stack position for each parameter
        //start at 4 to leave place for return address
        let mut curr_param_pos = 4;
        for &param in &func_info.params {
            self.param_stack_positions.insert(param, curr_param_pos);
            let size = type_size_in_bytes(self.prog.get_type(self.prog.type_of_value(Value::Param(param))));
            curr_param_pos += size
        }

        //determine the stack position for each slot and value-returning instruction
        //start at 4 to leave place for return address
        let mut stack_size = 4;

        for &slot in &func_info.slots {
            let ty = self.prog.get_type(self.prog.get_slot(slot).inner_ty);
            let size = type_size_in_bytes(ty);

            self.slot_stack_positions.insert(slot, stack_size);
            stack_size += size;
        }

        self.prog.visit_blocks(func, |block| {
            for &instr in &self.prog.get_block(block).instructions {
                let ty = self.prog.get_type(self.prog.type_of_value(Value::Instr(instr)));
                self.instr_stack_positions.insert(instr, stack_size);
                stack_size += type_size_in_bytes(ty);
            }
        });

        self.stack_size = stack_size;

        let func_number = self.func_number(func);
        self.append_ln(&format!("func_{}:", func_number));

        //grow stack
        self.append_instr(&format!("sub esp, {}", stack_size));

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
        stack_size: Default::default(),
        param_stack_positions: Default::default(),
        slot_stack_positions: Default::default(),
        instr_stack_positions: Default::default(),
        block_numbers: Default::default(),
        func_numbers: Default::default(),
    };
    asm.lower();
    asm.string
}