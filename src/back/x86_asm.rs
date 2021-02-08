use indexmap::map::IndexMap;

use crate::mid::ir::{ArithmeticOp, Block, Data, Function, FunctionInfo, Instruction, InstructionInfo, LogicalOp, Parameter, Phi, Program, StackSlot, Target, Terminator, TypeInfo, Value};

//TODO rethink what this means around alignment
fn type_size_in_bytes(prog: &Program, ty: &TypeInfo) -> i32 {
    match ty {
        TypeInfo::Integer { bits: 32 } => 4,
        TypeInfo::Integer { bits: 1 } => 4,
        TypeInfo::Integer { bits: 8 } => 4,
        TypeInfo::Integer { .. } => panic!("Only 32 bit integers, booleans and bytes supported for now"),
        TypeInfo::Pointer { .. } | TypeInfo::Func(..) => 4,
        TypeInfo::Tuple(tuple_ty) => {
            tuple_ty.fields.iter()
                .map(|&field| type_size_in_bytes(prog, prog.get_type(field)))
                .sum()
        }
        //TODO change this back to 0, but then we need to check the type whenever we store
        TypeInfo::Void => 4
    }
}

#[derive(Default)]
struct Output {
    header: String,
    text: String,
}

impl Output {
    fn append_ln(&mut self, line: &str) {
        self.text.push_str(line);
        self.text.push('\n');
    }

    fn append_instr(&mut self, instr: &str) {
        self.text.push_str("    ");
        self.append_ln(instr);
    }
}

struct AsmBuilder<'p> {
    prog: &'p Program,
    next_label_number: usize,

    //TODO make these match the indices in the IR debug format
    block_numbers: IndexMap<Block, usize>,
    func_numbers: IndexMap<Function, usize>,
    data_numbers: IndexMap<Data, usize>,
}

struct AsmFuncBuilder<'p, 'o, 'r> {
    prog: &'p Program,
    output: &'o mut Output,
    parent: &'r mut AsmBuilder<'p>,

    local_stack_size: i32,
    param_size: i32,

    param_stack_positions: IndexMap<Parameter, i32>,
    slot_stack_positions: IndexMap<StackSlot, i32>,
    instr_stack_positions: IndexMap<Instruction, i32>,

    pre_phi_stack_positions: IndexMap<Phi, i32>,
    post_phi_stack_positions: IndexMap<Phi, i32>,
}

impl AsmBuilder<'_> {
    pub fn lower(mut self) -> String {
        let mut output = Output::default();

        //call main function
        let main_func_number = self.func_number(self.prog.main);
        output.append_ln("_main:");
        output.append_instr(&format!("call func_{}", main_func_number));
        output.append_instr("push eax");
        output.append_instr("call _ExitProcess@4");

        //hardcode dependency TODO eventually remove this
        output.header.push_str("extern _ExitProcess@4\n");

        //write out all of the functions
        for (func, func_info) in &self.prog.nodes.funcs {
            self.append_func(&mut output, func, func_info)
        };

        //write out all of the data
        //TODO maybe write this to the data section instead of the text section
        for (&data, &data_num) in &self.data_numbers {
            output.text.push_str(&format!("data_{}:\n  db ", data_num));

            let data_info = self.prog.get_data(data);
            for (i, b) in data_info.bytes.iter().enumerate() {
                if i != 0 { output.text.push_str(", ") }
                output.text.push_str(&format!("{}", b));
            }
            output.text.push('\n');
        }

        //format everything together
        format!("global _main\n{}\nsection .text\n{}", output.header, output.text)
    }

    fn append_func(&mut self, output: &mut Output, func: Function, func_info: &FunctionInfo) {
        let prog = self.prog;

        let mut param_stack_positions = IndexMap::new();
        let mut slot_stack_positions = IndexMap::new();
        let mut instr_stack_positions = IndexMap::new();

        let mut pre_phi_stack_positions = IndexMap::new();
        let mut post_phi_stack_positions = IndexMap::new();

        //determine the stack position for each slot and value-returning instruction
        let mut stack_size = 0;

        //TODO for stdcall we don't actually need to allocate slots, they already have an address on the stack
        for &slot in &func_info.slots {
            let ty = prog.get_type(prog.get_slot(slot).inner_ty);
            let size = type_size_in_bytes(prog, ty);

            slot_stack_positions.insert(slot, stack_size);
            stack_size += size;
        }

        prog.visit_blocks(func, |block| {
            let block_info = prog.get_block(block);

            for &phi in &block_info.phis {
                let ty = prog.get_phi(phi).ty;
                let ty_size = type_size_in_bytes(&prog, prog.get_type(ty));

                pre_phi_stack_positions.insert(phi, stack_size);
                stack_size += ty_size;
                post_phi_stack_positions.insert(phi, stack_size);
                stack_size += ty_size;
            }

            for &instr in &block_info.instructions {
                let ty = prog.get_type(prog.get_instr(instr).ty(prog));
                instr_stack_positions.insert(instr, stack_size);
                stack_size += type_size_in_bytes(&prog, ty);
            }
        });

        //the local stack size is the stack size excluding the parameters and the isp
        let local_stack_size = stack_size;

        //space for isp
        stack_size += 4;

        let mut param_size = 0;

        //determine the stack position for each parameter
        for &param in func_info.params.iter() {
            param_stack_positions.insert(param, stack_size);
            let size = type_size_in_bytes(prog, prog.get_type(prog.type_of_value(Value::Param(param))));
            stack_size += size;
            param_size += size;
        }


        let func_number = self.func_number(func);
        output.append_ln(&format!("func_{}:", func_number));

        //grow stack
        output.append_instr(&format!("sub esp, {}", local_stack_size));

        let mut func_builder = AsmFuncBuilder {
            prog,
            output,
            parent: self,
            local_stack_size,
            param_size,
            param_stack_positions,
            slot_stack_positions,
            instr_stack_positions,
            pre_phi_stack_positions,
            post_phi_stack_positions,
        };

        prog.visit_blocks(func, |block| {
            func_builder.append_block(block);
        });
    }
}

impl AsmBuilder<'_> {
    //returns a distinct number on each invocation
    fn label_number(&mut self) -> usize {
        let num = self.next_label_number;
        self.next_label_number += 1;
        num
    }

    fn block_number(&mut self, block: Block) -> usize {
        let next_num = self.block_numbers.len();
        *self.block_numbers.entry(block).or_insert(next_num)
    }

    fn func_number(&mut self, func: Function) -> usize {
        let next_num = self.func_numbers.len();
        *self.func_numbers.entry(func).or_insert(next_num)
    }

    fn data_number(&mut self, data: Data) -> usize {
        let next_num = self.data_numbers.len();
        *self.data_numbers.entry(data).or_insert(next_num)
    }
}

impl std::ops::Deref for AsmFuncBuilder<'_, '_, '_> {
    type Target = Output;

    fn deref(&self) -> &Self::Target {
        self.output
    }
}

impl std::ops::DerefMut for AsmFuncBuilder<'_, '_, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.output
    }
}

impl AsmFuncBuilder<'_, '_, '_> {
    /// `reg = value`
    fn append_value_to_reg(&mut self, reg: &str, value: &Value, stack_offset: i32) {
        match value {
            Value::Undef(_) => {
                //placeholder to make debugging easier
                self.append_instr(&format!("mov {}, 0xabcd ;undef", reg))
            }
            Value::Const(cst) => {
                self.append_instr(&format!("mov {}, {}", reg, cst.value))
            }
            Value::Func(func) => {
                let func_number = self.parent.func_number(*func);
                self.append_instr(&format!("mov {}, func_{}", reg, func_number));
            }
            Value::Param(param) => {
                let param_pos = self.param_stack_positions[param];
                self.append_instr(&format!("mov {}, [esp+{}]", reg, stack_offset + param_pos));
            }
            Value::Slot(slot) => {
                let slot_pos = self.slot_stack_positions[slot];
                self.append_instr(&format!("lea {}, [esp+{}]", reg, stack_offset + slot_pos));
            }
            Value::Phi(phi) => {
                let phi_pos = self.post_phi_stack_positions[phi];
                self.append_instr(&format!("mov {}, [esp+{}]", reg, stack_offset + phi_pos));
            }
            Value::Instr(instr) => {
                let instr_pos = self.instr_stack_positions[instr];
                self.append_instr(&format!("mov {}, [esp+{}]", reg, stack_offset + instr_pos));
            }
            Value::Extern(ext) => {
                let name = &self.prog.get_ext(*ext).name;
                self.append_instr(&format!("mov {}, {}", reg, name));
                self.header.push_str(&format!("extern {}\n", name))
            }
            Value::Data(data) => {
                let data_number = self.parent.data_number(*data);
                self.append_instr(&format!("mov {}, data_{}", reg, data_number));
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

    fn append_jump_to_target(&mut self, target: &Target) {
        let target_block_info = self.prog.get_block(target.block);

        for (phi, phi_value) in target_block_info.phis.iter().zip(&target.phi_values) {
            let pre_pos = self.pre_phi_stack_positions[phi];
            self.append_value_to_reg("eax", &phi_value, 0);
            self.append_instr(&format!("mov [esp+{}], eax", pre_pos));
        }

        let block_number = self.parent.block_number(target.block);
        self.append_instr(&format!("jmp block_{}", block_number));
    }

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.parent.block_number(block);
        self.append_ln(&format!("  block_{}: ", block_number));

        let block = self.prog.get_block(block);

        //copy phi values from pre to post
        if !block.phis.is_empty() {
            self.append_instr(";phi copy");
            for phi in &block.phis {
                let pre_pos = self.pre_phi_stack_positions[phi];
                let post_pos = self.post_phi_stack_positions[phi];
                self.append_instr(&format!("mov eax, [esp+{}]", pre_pos));
                self.append_instr(&format!("mov [esp+{}], eax", post_pos));
            }
        }

        //write out instructions
        for &instr in &block.instructions {
            let instr_pos = self.instr_stack_positions[&instr];
            match self.prog.get_instr(instr) {
                InstructionInfo::Store { addr, value } => {
                    self.append_instr(";store");
                    self.append_value_to_reg("eax", value, 0);
                    self.append_value_to_reg("ebx", addr, 0);
                    self.append_instr("mov [ebx], eax");
                }
                InstructionInfo::Load { addr } => {
                    self.append_instr(";load");
                    self.append_value_to_reg("ebx", addr, 0);
                    self.append_instr("mov eax, [ebx]");
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
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
                InstructionInfo::Arithmetic { kind, left, right } => {
                    self.append_instr(";arithmetic");
                    self.append_value_to_reg("eax", left, 0);
                    self.append_value_to_reg("ebx", right, 0);

                    //eax = op(eax, ebx)
                    match kind {
                        ArithmeticOp::Add => self.append_instr("add eax, ebx"),
                        ArithmeticOp::Sub => self.append_instr("sub eax, ebx"),
                        ArithmeticOp::Mul => self.append_instr("imul eax, ebx"),
                        ArithmeticOp::Div => self.append_div(),
                        ArithmeticOp::Mod => {
                            self.append_div();
                            self.append_instr("mov eax, edx");
                        }
                    }

                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
                InstructionInfo::Comparison { kind, left, right } => {
                    self.append_instr(";logical");
                    self.append_value_to_reg("eax", left, 0);
                    self.append_value_to_reg("ebx", right, 0);
                    self.append_instr("xor ecx, ecx");
                    self.append_instr("cmp eax, ebx");

                    match kind {
                        LogicalOp::Eq => self.append_instr("sete cl"),
                        LogicalOp::Neq => self.append_instr("setne cl"),
                        LogicalOp::Gte => self.append_instr("setae cl"),
                        LogicalOp::Gt => self.append_instr("seta cl"),
                        LogicalOp::Lte => self.append_instr("setbe cl"),
                        LogicalOp::Lt => self.append_instr("setb cl"),
                    }

                    self.append_instr(&format!("mov [esp+{}], ecx", instr_pos));
                }
                InstructionInfo::TupleFieldPtr { base, index, result_ty: _ } => {
                    let tuple_ty = self.prog.get_type(self.prog.type_of_value(*base)).unwrap_ptr()
                        .and_then(|ty| self.prog.get_type(ty).unwrap_tuple())
                        .expect("TupleFieldPtr target should have tuple pointer type");
                    let field_offset: i32 = tuple_ty.fields[0..*index as usize].iter()
                        .map(|&ty| type_size_in_bytes(self.prog, self.prog.get_type(ty)))
                        .sum();

                    self.append_instr(";TupleFieldPtr");
                    self.append_value_to_reg("eax", base, 0);
                    self.append_instr(&format!("add eax, {}", field_offset));
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
            }
        }

        self.append_instr(";terminator");
        match &block.terminator {
            Terminator::Jump { target } => {
                self.append_jump_to_target(target);
            }
            Terminator::Branch { cond, true_target, false_target } => {
                let label_number = self.parent.label_number();

                self.append_instr(";  cond");
                self.append_value_to_reg("eax", cond, 0);
                self.append_instr("test eax, eax");
                self.append_instr(&format!("jz label_{}", label_number));

                self.append_instr(";  true");
                self.append_jump_to_target(true_target);

                self.append_instr(";  false");
                self.append_ln(&format!("  label_{}:", label_number));
                self.append_jump_to_target(false_target);
            }
            Terminator::Return { value } => {
                let local_stack_size = self.local_stack_size;
                let param_size = self.param_size;

                self.append_value_to_reg("eax", value, 0);
                self.append_instr(&format!("add esp, {}", local_stack_size));
                self.append_instr(&format!("ret {}", param_size));
            }
            Terminator::Unreachable => {
                self.append_instr("hlt");
            }
        }
    }
}

pub fn lower(prog: &Program) -> String {
    AsmBuilder {
        prog,
        next_label_number: Default::default(),
        block_numbers: Default::default(),
        func_numbers: Default::default(),
        data_numbers: Default::default(),
    }.lower()
}