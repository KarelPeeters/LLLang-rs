use indexmap::map::IndexMap;

use crate::mid::ir::{BinaryOp, Block, Data, Function, Instruction, InstructionInfo, Parameter, Program, StackSlot, Terminator, Type, TypeInfo, Value};

const STACK_ALIGNMENT: i32 = 4;

struct Layout {
    size: i32,
    alignment: i32,
}

impl Layout {
    pub fn new(size: i32, alignment: i32) -> Self {
        assert!(alignment >= 1);
        assert!(size >= 0);
        Layout { size, alignment }
    }
}

fn type_layout(prog: &Program, ty: Type) -> Layout {
    match prog.get_type(ty) {
        TypeInfo::Integer { bits } => {
            //bool is one byte
            if *bits == 1 {
                return Layout::new(1, 1)
            }

            assert_eq!(bits % 8, 0, "only integers with size multiple of 8 supported for now");
            let bytes = bits / 8;
            Layout::new(bytes, bytes)
        }
        TypeInfo::Void => {
            //void doesn't actually occupy space
            Layout::new(0, 1)
        },
        TypeInfo::Pointer { .. } | TypeInfo::Func(_) => {
            //32 bit, pointers have size 4
            Layout::new(4, 4)
        },
        TypeInfo::Array { inner, length } => {
            let inner_layout = type_layout(prog, *inner);
            Layout::new(inner_layout.size * length, inner_layout.alignment)
        }
    }
}

fn type_layout_of_value(prog: &Program, value: Value) -> Layout {
    type_layout(prog, prog.type_of_value(value))
}

struct StackLayout<'p> {
    prog: &'p Program,
    next_index: i32,
}

impl StackLayout<'_> {
    fn allocate(&mut self, layout: Layout) -> i32 {
        let Layout { size, alignment } = layout;

        if alignment > STACK_ALIGNMENT {
            panic!("Cannot allocate items with alignment > STACK_ALIGNMENT on the stack")
        }

        let index = (self.next_index + alignment - 1) / alignment * alignment;
        self.next_index = index + size;

        index
    }

    fn allocate_value(&mut self, value: Value) -> i32 {
        self.allocate(type_layout(self.prog, self.prog.type_of_value(value)))
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RegSize {
    Byte,
    Word,
    DWord,
}

impl RegSize {
    fn from_bytes(bytes: i32) -> Option<Self> {
        match bytes {
            0 => None,
            1 => Some(RegSize::Byte),
            2 => Some(RegSize::Word),
            4 => Some(RegSize::DWord),
            _ => panic!("Invalid register size {}", bytes),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Reg {
    A,
    C,
    D,
    B,
}

impl Reg {
    fn name_for_size(self, size: RegSize) -> &'static str {
        let i = match size {
            RegSize::Byte => 0,
            RegSize::Word => 1,
            RegSize::DWord => 2,
        };

        let arr = match self {
            Reg::A => ["al", "ax", "eax"],
            Reg::C => ["cl", "cx", "ecx"],
            Reg::D => ["dl", "dx", "edx"],
            Reg::B => ["bl", "bx", "ebx"],
        };

        arr[i]
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
    data_numbers: IndexMap<Data, usize>,
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

    fn data_number(&mut self, data: Data) -> usize {
        let next_num = self.data_numbers.len();
        *self.data_numbers.entry(data).or_insert(next_num)
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
            Value::Data(data) => {
                let data_number = self.data_number(*data);
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

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.block_number(block);
        self.append_ln(&format!("  block_{}: ", block_number));

        let block = self.prog.get_block(block);

        //write out instructions
        //TODO fix all of them to actually store the correct size
        for &instr in &block.instructions {
            let instr_pos = *self.instr_stack_positions.get(&instr).unwrap();
            match self.prog.get_instr(instr) {
                InstructionInfo::Store { addr, value } => {
                    self.append_instr(";store");
                    let layout = type_layout(self.prog, self.prog.type_of_value(*value));
                    if let Some(size) = RegSize::from_bytes(layout.size) {
                        self.append_value_to_reg(Reg::A.name_for_size(size), value, 0);
                        self.append_value_to_reg("ebx", addr, 0);
                        self.append_instr("mov [ebx], eax");
                    }
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
        let mut stack_layout = StackLayout { prog: self.prog, next_index: 0 };

        //TODO for stdcall we don't actually need to allocate slots, they already have an address on the stack
        for &slot in &func_info.slots {
            let ty = self.prog.get_slot(slot).inner_ty;
            let layout = type_layout(self.prog, ty);
            self.slot_stack_positions.insert(slot, stack_layout.allocate(layout));
        }

        self.prog.visit_blocks(func, |block| {
            for &instr in &self.prog.get_block(block).instructions {
                let instr_pos = stack_layout.allocate_value(Value::Instr(instr));
                self.instr_stack_positions.insert(instr, instr_pos);
            }
        });

        //the local stack size is the stack size excluding the parameters and the isp
        self.local_stack_size = stack_layout.allocate(Layout::new(0, STACK_ALIGNMENT));

        //allocate space for ISP
        stack_layout.allocate(Layout::new(4, STACK_ALIGNMENT));

        //determine the stack position for each parameter
        for &param in func_info.params.iter() {
            let param_pos = stack_layout.allocate_value(Value::Param(param));
            self.param_stack_positions.insert(param, param_pos);
        }

        let params_end_pos = stack_layout.allocate(Layout::new(0, 4));
        self.param_size = params_end_pos - self.local_stack_size - 4;

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
        //TODO think abour how parameter alignment is supposed to work
        self.append_instr("push eax");
        self.append_instr("call _ExitProcess@4");

        //hardcode dependency TODO eventually remove this
        self.header.push_str("extern _ExitProcess@4\n");

        //write out all of the functions
        self.prog.visit_funcs(|func| {
            self.append_func(func)
        });

        //write out all of the data
        //TODO maybe write this to the data section instead of the text section
        for (&data, &data_num) in &self.data_numbers {
            self.text.push_str(&format!("data_{}:\n  db ", data_num));

            let data_info = self.prog.get_data(data);
            for b in &data_info.bytes {
                self.text.push_str(&format!("{}, ", b));
            }
            self.text.push('\n');
        }

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
        data_numbers: Default::default(),
    }.lower()
}