use std::cmp::max;

use indexmap::map::IndexMap;
use itertools::Itertools;

use crate::back::layout::{Layout, next_multiple, TupleLayout};
use crate::mid::ir::{ArithmeticOp, Block, Data, Function, FunctionInfo, Instruction, InstructionInfo, LogicalOp, Phi, Program, StackSlot, Target, Terminator, Value};
use crate::util::zip_eq;

pub fn lower(prog: &Program) -> String {
    AsmBuilder {
        prog,
        next_label_number: Default::default(),
        block_numbers: Default::default(),
        func_numbers: Default::default(),
        data_numbers: Default::default(),
    }.lower()
}

const STACK_ALIGNMENT: i32 = 4;

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
    func: Function,

    local_layout: TupleLayout,
    param_layout: TupleLayout,
    param_offset: i32,
    local_stack_size: i32,
    param_size: i32,

    slot_stack_indices: IndexMap<StackSlot, usize>,
    instr_stack_indices: IndexMap<Instruction, usize>,
    phi_stack_indices: IndexMap<Phi, PhiIndices>,
}

struct PhiIndices {
    pre: usize,
    post: usize,
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

        let param_types = func_info.params.iter()
            .map(|&param| self.prog.get_param(param).ty)
            .collect_vec();
        let param_layout = TupleLayout::for_types(&self.prog, param_types.iter().copied());

        //collect all of the values that need to be stored on the stack
        let mut slot_stack_indices = IndexMap::new();
        let mut instr_stack_indices = IndexMap::new();
        let mut phi_stack_indices = IndexMap::new();

        let mut local_types = Vec::new();

        for &slot in &func_info.slots {
            slot_stack_indices.insert(slot, local_types.len());
            local_types.push(prog.get_slot(slot).inner_ty);
        }

        //TODO maybe figure out the stack size required for the largest call here and then get rid of stack_delta?
        prog.visit_blocks(prog.get_func(func).entry.block, |block| {
            let block_info = prog.get_block(block);

            for &phi in &block_info.phis {
                let ty = prog.get_phi(phi).ty;
                phi_stack_indices.insert(phi, PhiIndices { pre: local_types.len(), post: local_types.len() + 1 });
                local_types.push(ty);
                local_types.push(ty);
            }

            for &instr in &block_info.instructions {
                let ty = prog.get_instr(instr).ty(prog);
                instr_stack_indices.insert(instr, local_types.len());
                local_types.push(ty);
            }
        });

        let local_layout = TupleLayout::for_types(&self.prog, local_types.iter().copied());

        let func_number = self.func_number(func);
        if let Some(debug_name) = &func_info.debug_name {
            output.append_ln(&format!("func_{}: ; {}: {}", func_number, debug_name, self.prog.format_type(func_info.ty)));
        } else {
            output.append_ln(&format!("func_{}: ; {}", func_number, self.prog.format_type(func_info.ty)));
        }

        //grow stack
        let required_stack_alignment = max(param_layout.layout.alignment, local_layout.layout.alignment);
        if required_stack_alignment > STACK_ALIGNMENT {
            panic!("Cannot store type with alignment {} on stack with alignment {}", required_stack_alignment, STACK_ALIGNMENT)
        }
        let param_size = next_multiple(param_layout.layout.size, STACK_ALIGNMENT);

        let local_stack_size = next_multiple(local_layout.layout.size, STACK_ALIGNMENT);
        if local_stack_size != 0 {
            output.append_instr(&format!("sub esp, {}", local_stack_size));
        }

        let mut func_builder = AsmFuncBuilder {
            prog,
            output,
            parent: self,
            func,
            param_layout,
            local_layout,
            param_offset: local_stack_size + 4,
            local_stack_size,
            param_size,
            slot_stack_indices,
            instr_stack_indices,
            phi_stack_indices,
        };

        //copy over initial phi values
        for (phi, phi_value) in zip_eq(&prog.get_block(func_info.entry.block).phis, &func_info.entry.phi_values) {
            let pre_pos = func_builder.local_layout.offsets[func_builder.phi_stack_indices[phi].pre];
            func_builder.append_value_to_mem(MemRegOffset::stack(pre_pos), phi_value, 0);
        }

        // generate the main code
        // the entry block is visited first so we don't even need to jump to it
        prog.visit_blocks(prog.get_func(func).entry.block, |block| {
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
    /// Copy a type with the given layout from `source` to `target`:
    /// `*target = *source`. Clobbers `eax`.
    fn append_mem_copy(&mut self, target: MemRegOffset, source: MemRegOffset, size: i32) {
        let mut left = size;

        while left >= 4 {
            left -= 4;
            self.append_instr(&format!("mov eax, dword {}", source + left));
            self.append_instr(&format!("mov {}, eax", target + left));
        }

        while left >= 2 {
            left -= 2;
            self.append_instr(&format!("movzx eax, word {}", source + left));
            self.append_instr(&format!("mov {}, ax", target + left));
        }

        while left >= 1 {
            left -= 1;
            self.append_instr(&format!("movzx eax, byte {}", source + left));
            self.append_instr(&format!("mov {}, al", target + left));
        }

        assert_eq!(left, 0);
    }

    /// Copy `value` into at `target`: `*target = value`. Clobbers `eax`.
    fn append_value_to_mem(&mut self, target: MemRegOffset, value: &Value, stack_delta: i32) {
        //TODO deduplicate this code with append_value_to_reg
        //TODO redesign this stack_delta stuff, the current implementation is just one big minefield

        let ty = self.prog.type_of_value(*value);
        let layout = Layout::for_type(&self.prog, ty);

        match value {
            Value::Undef(_) => {
                //do nothing, just a comment for clarity
                let str = format!("; {} = {}", target, self.prog.format_value(*value));
                self.append_instr(&str)
            }
            Value::Const(cst) => {
                match layout.size {
                    0 => {} //easy
                    1 => self.append_instr(&format!("mov {}, byte {}", target, cst.value)),
                    2 => self.append_instr(&format!("mov {}, word {}", target, cst.value)),
                    4 => self.append_instr(&format!("mov {}, dword {}", target, cst.value)),
                    _ => panic!("only constants with power of two size <= 4 supported for now"),
                }
            }
            Value::Func(func) => {
                assert_eq!(layout.size, 4);
                let func_number = self.parent.func_number(*func);
                self.append_instr(&format!("mov {}, dword func_{}", target, func_number));
            }
            Value::Param(param) => {
                let param_index = self.prog.get_func(self.func).params.iter()
                    .position(|x| x == param)
                    .expect("param does not belong to this function");

                let stack_pos = self.param_layout.offsets[param_index];
                let real_stack_pos = stack_delta + stack_pos + self.param_offset;
                self.append_mem_copy(target, MemRegOffset::stack(real_stack_pos), layout.size);
            }
            Value::Slot(slot) => {
                let stack_pos = self.local_layout.offsets[self.slot_stack_indices[slot]];
                self.append_instr(&format!("lea eax, [esp+{}]", stack_delta + stack_pos));
                self.append_instr(&format!("mov {}, eax", target));
            }
            Value::Phi(phi) => {
                let stack_pos = self.local_layout.offsets[self.phi_stack_indices[phi].post];
                self.append_mem_copy(target, MemRegOffset::stack(stack_delta + stack_pos), layout.size);
            }
            Value::Instr(instr) => {
                let stack_pos = self.local_layout.offsets[self.instr_stack_indices[instr]];
                self.append_mem_copy(target, MemRegOffset::stack(stack_delta + stack_pos), layout.size);
            }
            Value::Extern(ext) => {
                assert_eq!(layout.size, 4);
                let name = &self.prog.get_ext(*ext).name;
                self.append_instr(&format!("mov {}, dword {}", target, name));
                self.header.push_str(&format!("extern {}\n", name))
            }
            Value::Data(data) => {
                assert_eq!(layout.size, 4);
                let data_number = self.parent.data_number(*data);
                self.append_instr(&format!("mov {}, dword data_{}", target, data_number));
            }
        }
    }

    /// Copy `value` into `reg` with the appropriate size. Panics if `value` doesn't fit into a register.
    /// Does not clobber any additional registers.
    fn append_value_to_reg(&mut self, target: Register, value: &Value, stack_delta: i32) -> RegisterSize {
        //TODO this is a lot of code duplication, figure out a better system for this
        //  maybe a general append_copy(source: enum Source, target: enum Target) thing?
        //  where source can then have a function to_MemRegOffset and to_register? (or either of them)

        let ty = self.prog.type_of_value(*value);
        let layout = Layout::for_type(&self.prog, ty);

        let register_size = RegisterSize::for_size(layout.size)
            .unwrap_or_else(|()| panic!("Tried to put value {:?} with size {} into reg", value, layout.size))
            .unwrap_or_else(|| panic!("Tried to put zero-sized value {:?} into reg", value));
        let full_target = target.with_size(RegisterSize::S32);
        let target = target.with_size(register_size);

        match value {
            Value::Undef(_) => {
                //do nothing, just a comment for clarity
                let str = format!("; {} = {}", target, self.prog.format_value(*value));
                self.append_instr(&str)
            }
            Value::Const(cst) => {
                self.append_instr(&format!("mov {}, {}", target, cst.value))
            }
            Value::Func(func) => {
                assert_eq!(layout.size, 4);
                let func_number = self.parent.func_number(*func);
                self.append_instr(&format!("mov {}, func_{}", target, func_number));
            }
            Value::Param(param) => {
                let param_index = self.prog.get_func(self.func).params.iter()
                    .position(|x| x == param)
                    .expect("param does not belong to this function");

                let stack_pos = self.param_layout.offsets[param_index];
                let real_stack_pos = stack_delta + stack_pos + self.param_offset;
                self.append_instr(&format!("mov {}, [esp+{}]", target, real_stack_pos));
            }
            Value::Slot(slot) => {
                let stack_pos = self.local_layout.offsets[self.slot_stack_indices[slot]];
                self.append_instr(&format!("lea {}, [esp+{}]", target, stack_delta + stack_pos));
            }
            Value::Phi(phi) => {
                let stack_pos = self.local_layout.offsets[self.phi_stack_indices[phi].post];
                self.append_instr(&format!("mov {}, [esp+{}]", target, stack_delta + stack_pos));
            }
            Value::Instr(instr) => {
                let stack_pos = self.local_layout.offsets[self.instr_stack_indices[instr]];
                self.append_instr(&format!("mov {}, [esp+{}]", target, stack_delta + stack_pos));
            }
            Value::Extern(ext) => {
                assert_eq!(layout.size, 4);
                let name = &self.prog.get_ext(*ext).name;
                self.append_instr(&format!("mov {}, {}", target, name));
                self.header.push_str(&format!("extern {}\n", name))
            }
            Value::Data(data) => {
                assert_eq!(layout.size, 4);
                let data_number = self.parent.data_number(*data);
                self.append_instr(&format!("mov {}, dword data_{}", target, data_number));
            }
        }

        //clear upper bits
        if full_target != target {
            self.append_instr(&format!("movzx {}, {}", full_target, target));
        }

        register_size
    }

    /// ```
    /// A = A / B
    /// D = A % B
    /// ```
    fn append_div(&mut self, size: RegisterSize) {
        // the upper (unused) bits should be clear already, `append_value_to_reg` zero-extends,
        // so we don't need to clear them here
        match size {
            RegisterSize::S8 => {
                self.append_instr("cwd");
                self.append_instr("idiv bx");
                self.append_instr("mov edx, eax")
            }
            RegisterSize::S16 | RegisterSize::S32 => {
                self.append_instr(&format!("xor {d}, {d}", d = Register::D.with_size(size)));
                self.append_instr(&format!("idiv {}", Register::B.with_size(size)));
            }
        }
    }

    fn append_jump_to_target(&mut self, target: &Target) {
        let target_block_info = self.prog.get_block(target.block);

        for (phi, phi_value) in zip_eq(&target_block_info.phis, &target.phi_values) {
            let pre_pos = self.local_layout.offsets[self.phi_stack_indices[phi].pre];
            self.append_value_to_mem(MemRegOffset::stack(pre_pos), phi_value, 0);
        }

        let block_number = self.parent.block_number(target.block);
        self.append_instr(&format!("jmp block_{}", block_number));
    }

    pub fn append_block(&mut self, block: Block) {
        let block_number = self.parent.block_number(block);
        self.append_ln(&format!("  block_{}:", block_number));

        let block = self.prog.get_block(block);

        //copy phi values from pre to post
        if !block.phis.is_empty() {
            self.append_instr(";Phi copy");
            for phi in &block.phis {
                let size = Layout::for_type(&self.prog, self.prog.get_phi(*phi).ty).size;

                let PhiIndices { pre, post } = self.phi_stack_indices[phi];
                let pre_pos = self.local_layout.offsets[pre];
                let post_pos = self.local_layout.offsets[post];

                self.append_mem_copy(MemRegOffset::stack(post_pos), MemRegOffset::stack(pre_pos), size);
            }
        }

        //write out instructions
        for instr in &block.instructions {
            let instr_pos = self.local_layout.offsets[self.instr_stack_indices[instr]];

            match self.prog.get_instr(*instr) {
                InstructionInfo::Store { addr, ty, value } => {
                    assert_eq!(*ty, self.prog.type_of_value(*value));
                    self.append_instr(";Store");
                    self.append_value_to_reg(Register::B, addr, 0);
                    self.append_value_to_mem(Register::B.mem(), value, 0);
                }
                InstructionInfo::Load { addr, ty } => {
                    let result_layout = Layout::for_type(self.prog, *ty);

                    self.append_instr(";Load");
                    self.append_value_to_reg(Register::B, addr, 0);
                    self.append_mem_copy(MemRegOffset::stack(instr_pos), Register::B.mem(), result_layout.size);
                }
                InstructionInfo::Call { target, args } => {
                    self.append_instr(";Call");

                    let func_ty = self.prog.type_of_value(*target);
                    let func_ty = self.prog.get_type(func_ty).unwrap_func()
                        .expect("Call target must have function type");

                    //TODO check whether eg f(a: byte, b: byte) should indeed be packed in stdcall
                    let param_layout = TupleLayout::for_types(&self.prog, func_ty.params.iter().copied());
                    if param_layout.layout.alignment > STACK_ALIGNMENT {
                        panic!("Cannot use argument type with alignment {} on stack with alignment {}", param_layout.layout.alignment, STACK_ALIGNMENT)
                    }

                    // increment SP and push the arguments
                    let stack_delta = next_multiple(param_layout.layout.size, STACK_ALIGNMENT);
                    if stack_delta != 0 {
                        self.append_instr(&format!("sub esp, {}", stack_delta));
                    }

                    for (arg, offset) in zip_eq(args, param_layout.offsets).rev() {
                        self.append_value_to_mem(MemRegOffset::stack(offset), arg, stack_delta);
                    }

                    //the actual call
                    self.append_value_to_reg(Register::A, target, stack_delta);
                    self.append_instr("call eax");

                    //copy the return register to the stack
                    let return_layout = Layout::for_type(&self.prog, func_ty.ret);
                    let return_register_size = RegisterSize::for_size(return_layout.size)
                        .unwrap_or_else(|()| panic!("Return value for {:?} size {} does not fit in register", instr, return_layout.size));

                    if let Some(return_register_size) = return_register_size {
                        self.append_instr(
                            &format!("mov [esp+{}], {}", instr_pos, Register::A.with_size(return_register_size))
                        );
                    }
                }
                InstructionInfo::Arithmetic { kind, left, right } => {
                    self.append_instr(";Arithmetic");

                    let size = self.append_value_to_reg(Register::A, left, 0);
                    self.append_value_to_reg(Register::B, right, 0);

                    let a = Register::A.with_size(size);
                    let b = Register::B.with_size(size);
                    let d = Register::D.with_size(size);

                    //A = op(A, B)
                    match kind {
                        ArithmeticOp::Add => self.append_instr(&format!("add {}, {}", a, b)),
                        ArithmeticOp::Sub => self.append_instr(&format!("sub {}, {}", a, b)),
                        ArithmeticOp::Mul => {
                            if size == RegisterSize::S8 {
                                self.append_instr("imul bx");
                            } else {
                                self.append_instr(&format!("imul {}, {}", a, b));
                            }
                        }
                        ArithmeticOp::Div => self.append_div(size),
                        ArithmeticOp::Mod => {
                            self.append_div(size);
                            self.append_instr(&format!("mov {}, {}", a, d));
                        }
                    }

                    self.append_instr(&format!("mov [esp+{}], {}", instr_pos, a));
                }
                InstructionInfo::Comparison { kind, left, right } => {
                    self.append_instr(";Comparison");

                    let size = self.append_value_to_reg(Register::A, left, 0);
                    self.append_value_to_reg(Register::B, right, 0);

                    self.append_instr("xor ecx, ecx");
                    self.append_instr(&format!("cmp {}, {}", Register::A.with_size(size), Register::B.with_size(size)));

                    match kind {
                        LogicalOp::Eq => self.append_instr("sete cl"),
                        LogicalOp::Neq => self.append_instr("setne cl"),
                        LogicalOp::Gte => self.append_instr("setae cl"),
                        LogicalOp::Gt => self.append_instr("seta cl"),
                        LogicalOp::Lte => self.append_instr("setbe cl"),
                        LogicalOp::Lt => self.append_instr("setb cl"),
                    }

                    self.append_instr(&format!("mov [esp+{}], cl", instr_pos));
                }
                InstructionInfo::TupleFieldPtr { base, index, tuple_ty } => {
                    let tuple_ty = self.prog.get_type(*tuple_ty).unwrap_tuple()
                        .expect("TupleFieldPtr target should have tuple pointer type");
                    let layout = TupleLayout::for_types(self.prog, tuple_ty.fields.iter().copied());
                    let field_offset = layout.offsets[*index as usize];

                    self.append_instr(";TupleFieldPtr");
                    self.append_value_to_reg(Register::A, base, 0);
                    self.append_instr(&format!("add eax, {}", field_offset));
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
                InstructionInfo::PointerOffSet { base, index, ty } => {
                    let ty_layout = Layout::for_type(self.prog, *ty);

                    self.append_instr(";ArrayIndexPtr");
                    self.append_value_to_reg(Register::A, index, 0);
                    self.append_instr(&format!("imul eax, {}", ty_layout.size));

                    self.append_value_to_reg(Register::B, base, 0);
                    self.append_instr("add eax, ebx");
                    self.append_instr(&format!("mov [esp+{}], eax", instr_pos));
                }
            }
        }

        self.append_instr(";Terminator");
        match &block.terminator {
            Terminator::Jump { target } => {
                self.append_jump_to_target(target);
            }
            Terminator::Branch { cond, true_target, false_target } => {
                let label_number = self.parent.label_number();

                self.append_instr(";  cond");
                self.append_value_to_reg(Register::A, cond, 0);
                self.append_instr("test al, al");
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

                if Layout::for_type(&self.prog, self.prog.type_of_value(*value)).size != 0 {
                    self.append_value_to_reg(Register::A, value, 0);
                }

                if local_stack_size != 0 {
                    self.append_instr(&format!("add esp, {}", local_stack_size));
                }
                self.append_instr(&format!("ret {}", param_size));
            }
            Terminator::Unreachable => {
                self.append_instr("hlt");
            }
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RegisterSize {
    S8,
    S16,
    S32,
}

impl RegisterSize {
    fn for_size(size: i32) -> Result<Option<RegisterSize>, ()> {
        match size {
            0 => Ok(None),
            1 => Ok(Some(RegisterSize::S8)),
            2 => Ok(Some(RegisterSize::S16)),
            4 => Ok(Some(RegisterSize::S32)),
            _ => Err(())
        }
    }

    fn as_index(self) -> usize {
        match self {
            RegisterSize::S8 => 0,
            RegisterSize::S16 => 1,
            RegisterSize::S32 => 2,
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Register {
    A,
    C,
    D,
    B,
    SP,
    BP,
    SI,
    DI,
}

impl Register {
    fn mem(self) -> MemRegOffset {
        MemRegOffset { reg: self, offset: 0 }
    }

    fn with_size(self, size: RegisterSize) -> &'static str {
        use Register::*;

        let a = match self {
            A => ["al", "ax", "eax"],
            C => ["cl", "cx", "ecx"],
            D => ["dl", "dx", "edx"],
            B => ["bl", "bx", "ebx"],
            SP => ["spl", "sp", "esp"],
            BP => ["bpl", "bp", "ebp"],
            SI => ["sil", "si", "esi"],
            DI => ["dil", "di", "edi"],
        };

        a[size.as_index()]
    }
}

#[derive(Debug, Copy, Clone)]
struct MemRegOffset {
    reg: Register,
    offset: i32,
}

impl MemRegOffset {
    fn stack(offset: i32) -> Self {
        MemRegOffset { reg: Register::SP, offset }
    }
}

impl std::ops::Add<i32> for MemRegOffset {
    type Output = MemRegOffset;

    fn add(self, rhs: i32) -> Self::Output {
        MemRegOffset { reg: self.reg, offset: self.offset + rhs }
    }
}

impl std::ops::Sub<i32> for MemRegOffset {
    type Output = MemRegOffset;

    fn sub(self, rhs: i32) -> Self::Output {
        MemRegOffset { reg: self.reg, offset: self.offset - rhs }
    }
}

impl std::fmt::Display for MemRegOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let reg = self.reg.with_size(RegisterSize::S32);
        match self.offset {
            off if off > 0 => write!(f, "[{}+{}]", reg, off),
            off if off < 0 => write!(f, "[{}-{}]", reg, -off),
            _ => write!(f, "[{}]", reg),
        }
    }
}
