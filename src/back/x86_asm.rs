use indexmap::map::IndexMap;

use crate::mid::ir::{BinaryOp, Block, Function, Instruction, InstructionInfo, Program, StackSlot, Terminator, TypeInfo, Value, Parameter};

//TODO rethink what this means around alignment
fn type_size_in_bytes(ty: &TypeInfo) -> i32 {
    match ty {
        TypeInfo::Integer { bits: 32 } => 4,
        TypeInfo::Integer { bits: 1 } => 4,
        TypeInfo::Integer { bits: 8 } => 4,
        TypeInfo::Integer { .. } => panic!("Only 32 bit integers and booleans supported for now"),
        TypeInfo::Pointer { .. } | TypeInfo::Func { .. } => 4,
        //TODO change this back to 0, but then we need to check the type whenever we store
        TypeInfo::Void => 4
    }
}

struct AsmBuilder<'p> {
    prog: &'p Program,

    text: String,
    header: String,

    local_stack_size: i32,
    param_size: i32,

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
        self.text.push_str(line);
        self.text.push('\n');
    }

    fn append_instr(&mut self, instr: &str) {
        self.text.push_str("    ");
        self.append_ln(instr);
    }

    /// `reg = value`
    fn append_value_to_reg(&mut self, reg: &str, value: &Value, stack_offset: i32) {
        match value {
            Value::Undef(_) => {
                self.append_instr(&format!(";mov {}, undef", reg)) //easy
            },
            Value::Const(cst) => {
                self.append_instr(&format!("mov {}, {}", reg, cst.value))
            },
            Value::Func(func) => {
                let func_number = self.func_number(*func);
                self.append_instr(&format!("mov {}, func_{}", reg, func_number));
            }
            Value::Param(param) => {
                let param_pos = *self.param_stack_positions.get(param).unwrap();
                self.append_instr(&format!("mov {}, [esp+{}]", reg, stack_offset + param_pos));
            }
            Value::Slot(slot) => {
                let slot_pos = *self.slot_stack_positions.get(slot).unwrap();
                self.append_instr(&format!("lea {}, [esp+{}]", reg, stack_offset + slot_pos));
            },
            Value::Instr(instr) => {
                let instr_pos = *self.instr_stack_positions.get(instr).unwrap();
                self.append_instr(&format!("mov {}, [esp+{}]", reg, stack_offset + instr_pos));
            },
            Value::Extern(ext) => {
                let name = &self.prog.get_ext(*ext).name;
                self.append_instr(&format!("mov {}, {}", reg, name));
                self.header.push_str(&format!("extern {}\n", name))
            }
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
                    self.append_value_to_reg("eax", value, 0);
                    self.append_value_to_reg("ebx", addr, 0);
                    self.append_instr("mov [ebx], eax");
                },
                InstructionInfo::Load { addr } => {
                    self.append_instr(";load");
                    self.append_value_to_reg("ebx", addr, 0);
                    self.append_instr("mov eax, [ebx]");
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                },
                InstructionInfo::Call { target, args } => {
                    self.append_instr(";call");

                    let mut stack_offset = 0;
                    for arg in args.iter().rev() {
                        self.append_value_to_reg("eax", arg, stack_offset);
                        self.append_instr("push eax");
                        stack_offset += 4;
                    }

                    self.append_value_to_reg("eax", target, stack_offset);
                    self.append_instr("call eax");
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
                InstructionInfo::Binary { kind, left, right } => {
                    self.append_instr(";binop");
                    self.append_value_to_reg("eax", left, 0);
                    self.append_value_to_reg("ebx", right, 0);

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

                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
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

                self.append_value_to_reg("eax", cond, 0);

                self.append_instr("test eax, eax");
                self.append_instr(&format!("jnz block_{}", true_block_number));
                self.append_instr(&format!("jmp block_{}", false_block_number));
            },
            Terminator::Return { value } => {
                self.append_value_to_reg("eax", value, 0);
                self.append_instr(&format!("add esp, {}", self.local_stack_size));
                self.append_instr(&format!("ret {}", self.param_size));
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

        //determine the stack position for each slot and value-returning instruction
        let mut stack_size = 0;

        //TODO for stdcall we don't actually need to allocate slots, they already have an address on the stack
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

        //the local stack size is the stack size excluding the parameters and the isp
        self.local_stack_size = stack_size;

        //space for isp
        stack_size += 4;

        let mut param_size = 0;

        //determine the stack position for each parameter
        for &param in func_info.params.iter() {
            self.param_stack_positions.insert(param, stack_size);
            let size = type_size_in_bytes(self.prog.get_type(self.prog.type_of_value(Value::Param(param))));
            stack_size += size;
            param_size += size;
        }

        self.param_size = param_size;

        let func_number = self.func_number(func);
        self.append_ln(&format!("func_{}:", func_number));

        //grow stack
        self.append_instr(&format!("sub esp, {}", self.local_stack_size));

        self.prog.visit_blocks(func, |block| {
            self.append_block(block);
        });
    }

    pub fn lower(mut self) -> String {
        //call main function
        let main_func_number = self.func_number(self.prog.main);
        self.append_ln("_main:");
        self.append_instr(&format!("call func_{}", main_func_number));
        self.append_instr("push eax");
        self.append_instr("call _ExitProcess@4");

        //hardcode dependency TODO eventually remove this
        self.header.push_str("extern _ExitProcess@4\n");

        //write out all of the functions
        self.prog.visit_funcs(|func| {
            self.append_func(func)
        });

        //format everything together
        format!("global _main\n{}\nsection .text\n{}", self.header, self.text)
    }
}

pub fn lower(prog: &Program) -> String {
    AsmBuilder {
        prog,
        text: Default::default(),
        header: Default::default(),
        local_stack_size: Default::default(),
        param_size: Default::default(),
        param_stack_positions: Default::default(),
        slot_stack_positions: Default::default(),
        instr_stack_positions: Default::default(),
        block_numbers: Default::default(),
        func_numbers: Default::default(),
    }.lower()
}