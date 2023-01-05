use std::collections::HashMap;
use std::fmt::{Display, Write};
use std::iter::zip;

use env_logger::Builder;
use itertools::Itertools;
use log::LevelFilter;
use regalloc2::{Allocation, Edit, Inst, InstOrEdit, InstRange, MachineEnv, Operand, PReg, PRegSet, RegallocOptions, RegClass};
use regalloc2 as r2;
use regalloc2::Function as _;
use regalloc2::VReg;

use crate::back::vcode::{InstInfo, preg_to_asm, VConst, VInstruction, VMem, VopRC, VopRCM, VSymbol, VTarget};
use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{ArithmeticOp, Block, BlockInfo, ComparisonOp, Expression, ExpressionInfo, Global, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Signed, Target, Terminator, Value};
use crate::mid::normalize::split_critical_edges::split_critical_edges;
use crate::mid::util::verify::verify;
use crate::util::{Never, NeverExt};

pub fn lower_new(prog: &mut Program) -> String {
    split_critical_edges(prog);
    verify(prog).unwrap();

    std::fs::write("pre_alloc.ir", format!("{}", prog)).unwrap();

    let mut output = Output::default();

    let use_info = UseInfo::new(prog);
    let mut symbols = Symbols::default();

    for (func, _) in &prog.nodes.funcs {
        println!("Func {:?}", func);

        let func_info = prog.get_func(func);
        let mut mapper = VRegMapper::default();

        let mut blocks = vec![];
        let mut v_instructions = vec![];

        // map blocks in-order
        let mut blocks_ordered = vec![];
        prog.try_visit_blocks(func_info.entry, |block| {
            symbols.define_block(block, blocks_ordered.len());
            blocks_ordered.push(block);
            Never::UNIT
        }).no_err();

        for &block in &blocks_ordered {
            println!("  Block {:?} -> {:?}", block, symbols.map_block(block).0);
            let BlockInfo { params, instructions, terminator } = prog.get_block(block);

            // setup builder
            let params = params.iter().map(|&param| mapper.map_param(param)).collect_vec();
            println!("    params {:?}", params);

            let range_start = v_instructions.len();
            let mut builder = VBuilder {
                prog,
                instructions: &mut v_instructions,
                vregs: &mut mapper,
                expr_cache: &mut Default::default(),
                symbols: &mut symbols,
            };

            // convert instructions to vcode
            for &instr in instructions {
                builder.append_instr(instr);
            }
            builder.append_terminator(terminator);

            // construct block
            let range_end = v_instructions.len();
            let inst_range = InstRange::forward(Inst::new(range_start), Inst::new(range_end));

            let mut succs = vec![];
            terminator.for_each_successor(|succ| succs.push(symbols.map_block(succ).1));
            let preds = use_info[block].iter().filter_map(|usage| {
                match usage {
                    BlockUsage::FuncEntry(_) => None,
                    BlockUsage::Target { pos, kind: _ } => Some(symbols.map_block(pos.block).1)
                }
            }).collect();

            println!("  succs: {:?}", succs);

            blocks.push(R2BlockInfo { inst_range, succs, preds, params });
        };

        let inst_infos = v_instructions.iter().map(|inst| inst.to_inst_info()).collect();

        let func_wrapper = FuncWrapper {
            entry_block: symbols.map_block(func_info.entry).1,
            blocks,
            v_instructions,
            inst_infos,
            vregs: mapper.next_vreg,
        };

        let env = build_env(4);
        let options = RegallocOptions {
            verbose_log: true,
            validate_ssa: true,
        };

        Builder::new().filter_level(LevelFilter::Trace).init();
        println!();
        println!();
        println!();
        let result = r2::run(&func_wrapper, &env, &options).unwrap();
        println!("{:?}", result);

        // recover register allocation in a more convenient format
        let mut vreg_allocs = vec![Allocation::none(); func_wrapper.vregs];
        for inst in 0..func_wrapper.num_insts() {
            let inst = Inst::new(inst);

            let inst_operands = func_wrapper.inst_operands(inst);
            let inst_allocs = result.inst_allocs(inst);

            assert_eq!(inst_operands.len(), inst_allocs.len());
            for (operand, &alloc) in zip(inst_operands, inst_allocs) {
                vreg_allocs[operand.vreg().vreg()] = alloc;
            }
        }

        // actually generate code
        output.appendln(format_args!("{}:", symbols.map_global(func)));

        for &block in &blocks_ordered {
            let block_mapped = symbols.map_block(block);
            output.appendln(format_args!("  {}:", block_mapped.0));

            for inst in result.block_insts_and_edits(&func_wrapper, block_mapped.1) {
                match inst {
                    InstOrEdit::Inst(inst) => {
                        let v_inst = &func_wrapper.v_instructions[inst.index()];
                        output.append_v_inst(v_inst, &vreg_allocs, result.inst_allocs(inst));
                    }
                    InstOrEdit::Edit(edit) => {
                        let Edit::Move { from, to } = edit;
                        let to = preg_to_asm(to.as_reg().unwrap());
                        let from = preg_to_asm(from.as_reg().unwrap());
                        output.appendln(format_args!("    ; {:?}", edit));
                        output.appendln(format_args!("    mov {}, {}", to, from));
                    }
                }
            }
        }

        output.appendln("\n");
    }

    output.finish()
}

#[derive(Default)]
struct Output {
    header: String,
    text: String,
}

impl Output {
    fn appendln(&mut self, f: impl Display) {
        writeln!(&mut self.text, "{}", f).unwrap();
    }

    fn append_v_inst(&mut self, v_inst: &VInstruction, allocs: &[Allocation], inst_allocs: &[Allocation]) {
        let result = v_inst.to_asm(allocs);
        self.appendln(format_args!("    ; {:?} {:?}", v_inst, inst_allocs));
        self.appendln(format_args!("    {}", result));
    }

    fn finish(self) -> String {
        format!("global _main\n{}\n\nsection .text\n{}", self.header, self.text)
    }
}

fn build_env(reg_count: usize) -> MachineEnv {
    let regs = (0..reg_count).map(|i| PReg::new(i, RegClass::Int)).collect();

    MachineEnv {
        preferred_regs_by_class: [regs, vec![]],
        non_preferred_regs_by_class: [vec![], vec![]],
        // TODO use fixed stack slots for params and return values
        fixed_stack_slots: vec![],
    }
}

struct VBlock {
    instructions: Vec<VInstruction>,
}

#[derive(Default)]
struct Symbols {
    globals: HashMap<Global, usize>,
    next_func: usize,
    next_ext: usize,
    next_data: usize,

    blocks: HashMap<Block, usize>,
    next_label: usize,
}

impl Symbols {
    fn map_global(&mut self, value: impl Into<Global>) -> VSymbol {
        let value = value.into();

        let (build, next): (fn(usize) -> VSymbol, &mut usize) = match value {
            Global::Func(_) => (VSymbol::Func, &mut self.next_func),
            Global::Extern(_) => (VSymbol::Ext, &mut self.next_ext),
            Global::Data(_) => (VSymbol::Data, &mut self.next_data),
        };

        let id = *self.globals.entry(value).or_insert_with(|| {
            let curr = *next;
            *next += 1;
            curr
        });

        build(id)
    }

    fn define_block(&mut self, block: Block, index: usize) {
        println!("      Defining {:?} -> {:?}", block, index);
        let prev = self.blocks.insert(block, index);
        assert!(prev.is_none());
    }

    fn map_block(&mut self, block: Block) -> (VSymbol, r2::Block) {
        let id = *self.blocks.get(&block).unwrap();
        let result = (VSymbol::Block(id), r2::Block(id as u32));
        println!("      Mapping {:?} -> {:?}", block, result);
        result
    }

    fn new_label(&mut self) -> VSymbol {
        let id = self.next_label;
        self.next_label += 1;
        VSymbol::Label(id)
    }
}

struct VBuilder<'a> {
    instructions: &'a mut Vec<VInstruction>,
    vregs: &'a mut VRegMapper,
    expr_cache: &'a mut HashMap<Expression, VReg>,
    prog: &'a Program,
    symbols: &'a mut Symbols,
}

#[derive(Debug)]
struct Void;

impl VBuilder<'_> {
    fn push(&mut self, instr: VInstruction) {
        println!("    push {:?}", instr);
        let info = instr.to_inst_info();
        println!("      as    {:?}", Inst::new(self.instructions.len()));
        println!("      args {:?}  {:?}", info.operands, info.branch_block_params);
        println!("      info {:?}", info);
        self.instructions.push(instr);
    }

    fn dummy_reg(&mut self) -> VReg {
        let vreg = self.vregs.new_vreg();
        self.push(VInstruction::DummyDef(vreg));
        vreg
    }

    fn append_instr(&mut self, instr: Instruction) {
        // TODO only invalidate expressions modified by this instruction instead of all of them?
        // TODO even better, properly schedule expressions in advance with dom_info and use_info
        self.expr_cache.clear();
        println!("    appending {:?}", instr);

        match *self.prog.get_instr(instr) {
            InstructionInfo::Load { addr, ty: _ } => {
                let addr = self.append_value_to_reg(addr);
                let result = self.vregs.map_instr(instr);
                self.push(VInstruction::MovReg(result, VMem::at(addr).into()));
            }
            InstructionInfo::Store { addr, ty: _, value } => {
                let addr = self.append_value_to_reg(addr);
                let value = self.append_value_to_rc(value);
                self.push(VInstruction::MovMem(VMem::at(addr), value.into()));
            }
            InstructionInfo::Call { .. } => todo!("call"),
            InstructionInfo::BlackBox { value } => {
                let _ = self.append_value_to_reg(value);
            }
        }
    }

    fn append_terminator(&mut self, term: &Terminator) {
        let prog = self.prog;

        match *term {
            Terminator::Jump { ref target } => {
                let target = self.append_target(target);
                self.push(VInstruction::Jump(target))
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                let cond = self.append_value_to_reg(cond);
                let label = self.symbols.new_label();
                let true_target = self.append_target(true_target);
                let false_target = self.append_target(false_target);
                self.push(VInstruction::Branch(cond, label, true_target, false_target));
            }
            Terminator::Return { value } => {
                let value = if prog.type_of_value(value) == prog.ty_void() {
                    None
                } else {
                    Some(self.append_value_to_reg(value))
                };

                self.push(VInstruction::Return(value));
            }
            Terminator::Unreachable => {
                self.push(VInstruction::Unreachable);
            }
            Terminator::LoopForever => todo!("loop forever"),
        }
    }

    fn append_target(&mut self, target: &Target) -> VTarget {
        let &Target { block, ref args } = target;
        let args = args.iter().map(|&arg| self.append_value_to_reg(arg)).collect();

        let block_mapped = self.symbols.map_block(block).0;
        println!("    target to {:?} -> {:?} args {:?}", block, block_mapped, args);

        VTarget {
            block: block_mapped,
            args,
        }
    }

    #[must_use]
    fn append_expr(&mut self, expr: Expression) -> VReg {
        if let Some(&result) = self.expr_cache.get(&expr) {
            return result;
        }

        let result = match *self.prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { kind, left, right } => {
                let instr = match kind {
                    ArithmeticOp::Add => "add",
                    ArithmeticOp::Sub => "sub",
                    ArithmeticOp::Mul => "mul",
                    ArithmeticOp::Div(_) => todo!("Arithmetic div"),
                    ArithmeticOp::Mod(_) => todo!("Arithmetic mod"),
                    ArithmeticOp::And => "and",
                    ArithmeticOp::Or => "or",
                    ArithmeticOp::Xor => "xor",
                };

                let result = self.vregs.new_vreg();
                let left = self.append_value_to_reg(left);
                let right = self.append_value_to_rcm(right);
                self.push(VInstruction::Binary(instr, result, left, right));
                left
            }
            ExpressionInfo::Comparison { kind, left, right } => {
                // TODO use "test" when comparing with zero
                //   see https://stackoverflow.com/questions/33721204/test-whether-a-register-is-zero-with-cmp-reg-0-vs-or-reg-reg/33724806#33724806
                let set_instr = match kind {
                    ComparisonOp::Eq => "sete",
                    ComparisonOp::Neq => "setne",

                    ComparisonOp::Gt(Signed::Signed) => "setg",
                    ComparisonOp::Lt(Signed::Signed) => "setl",
                    ComparisonOp::Gte(Signed::Signed) => "setge",
                    ComparisonOp::Lte(Signed::Signed) => "setle",

                    ComparisonOp::Gt(Signed::Unsigned) => "seta",
                    ComparisonOp::Lt(Signed::Unsigned) => "setb",
                    ComparisonOp::Gte(Signed::Unsigned) => "setae",
                    ComparisonOp::Lte(Signed::Unsigned) => "setbe",
                };

                let result = self.vregs.new_vreg();
                let left = self.append_value_to_reg(left);
                let right = self.append_value_to_rcm(right);

                // the second instr uses the flags set by the first
                // the register allocator can insert moves between them, but those don't affect the flags
                self.push(VInstruction::Cmp(left, right));
                self.push(VInstruction::Setcc(set_instr, result.into()));

                result
            }
            ExpressionInfo::TupleFieldPtr { .. } => todo!("TupleFieldPtr"),
            ExpressionInfo::PointerOffSet { .. } => todo!("PointerOffSet"),
            ExpressionInfo::Cast { .. } => todo!("Cast"),
        };

        self.expr_cache.insert(expr, result);
        result
    }

    fn append_value_to_rcm(&mut self, value: Value) -> VopRCM {
        match value {
            Value::Immediate(value) => match value {
                Immediate::Void => todo!("void to operand"),
                Immediate::Undef(_) => todo!("undef to operand"),
                Immediate::Const(cst) => VConst::Const(cst).into(),
            },
            Value::Global(value) => {
                let symbol = self.symbols.map_global(value);
                VConst::Symbol(symbol).into()
            }
            Value::Scoped(value) => match value {
                Scoped::Slot(_) => todo!("slot to operand"),
                Scoped::Param(param) => self.vregs.map_param(param).into(),
                Scoped::Instr(instr) => self.vregs.map_instr(instr).into(),
            },
            Value::Expr(expr) => self.append_expr(expr).into(),
        }
    }

    #[must_use]
    fn append_value_to_rc(&mut self, value: Value) -> VopRC {
        let operand = self.append_value_to_rcm(value);
        self.force_rc(operand)
    }

    #[must_use]
    fn append_value_to_reg(&mut self, value: Value) -> VReg {
        let operand = self.append_value_to_rcm(value);
        self.force_reg(operand)
    }

    #[must_use]
    fn force_rc(&mut self, value: VopRCM) -> VopRC {
        match value {
            VopRCM::Reg(reg) => reg.into(),
            VopRCM::Const(cst) => cst.into(),
            VopRCM::Mem(mem) => self.force_reg(mem.into()).into(),
        }
    }

    #[must_use]
    fn force_reg(&mut self, value: VopRCM) -> VReg {
        match value {
            VopRCM::Reg(reg) => reg,
            VopRCM::Mem(_) | VopRCM::Const(_) => {
                let reg = self.vregs.new_vreg();
                self.push(VInstruction::MovReg(reg, value));
                reg
            }
        }
    }
}

struct FuncWrapper {
    entry_block: r2::Block,
    blocks: Vec<R2BlockInfo>,
    v_instructions: Vec<VInstruction>,
    inst_infos: Vec<InstInfo>,
    vregs: usize,
}

struct R2BlockInfo {
    inst_range: InstRange,
    succs: Vec<r2::Block>,
    preds: Vec<r2::Block>,
    params: Vec<VReg>,
}

impl r2::Function for FuncWrapper {
    fn num_insts(&self) -> usize {
        self.inst_infos.len()
    }

    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    fn entry_block(&self) -> r2::Block {
        self.entry_block
    }

    fn block_insns(&self, block: r2::Block) -> InstRange {
        self.blocks[block.0 as usize].inst_range
    }

    fn block_succs(&self, block: r2::Block) -> &[r2::Block] {
        &self.blocks[block.0 as usize].succs
    }

    fn block_preds(&self, block: r2::Block) -> &[r2::Block] {
        &self.blocks[block.0 as usize].preds
    }

    fn block_params(&self, block: r2::Block) -> &[VReg] {
        &self.blocks[block.0 as usize].params
    }

    fn is_ret(&self, inst: Inst) -> bool {
        self.inst_infos[inst.0 as usize].is_ret
    }

    fn is_branch(&self, inst: Inst) -> bool {
        self.inst_infos[inst.0 as usize].is_branch
    }

    fn branch_blockparams(&self, _: r2::Block, inst: Inst, succ_idx: usize) -> &[VReg] {
        let info = &self.inst_infos[inst.0 as usize];
        assert!(info.is_branch);
        &info.branch_block_params[succ_idx]
    }

    fn is_move(&self, inst: Inst) -> Option<(Operand, Operand)> {
        self.inst_infos[inst.0 as usize].is_move
    }

    fn inst_operands(&self, inst: Inst) -> &[Operand] {
        &self.inst_infos[inst.0 as usize].operands
    }

    fn inst_clobbers(&self, inst: Inst) -> PRegSet {
        self.inst_infos[inst.0 as usize].clobbers
    }

    fn num_vregs(&self) -> usize {
        self.vregs
    }

    fn spillslot_size(&self, _: RegClass) -> usize {
        // TODO figure out what this is
        1
    }
}

#[derive(Default)]
pub struct VRegMapper {
    next_vreg: usize,
    value_map: HashMap<Value, VReg>,
}

impl VRegMapper {
    fn new_vreg(&mut self) -> VReg {
        let index = self.next_vreg;
        self.next_vreg += 1;
        VReg::new(index, RegClass::Int)
    }

    fn get_or_new(&mut self, value: Value) -> VReg {
        let next_vreg = &mut self.next_vreg;
        *self.value_map.entry(value).or_insert_with(|| {
            let index = *next_vreg;
            *next_vreg += 1;
            let reg = VReg::new(index, RegClass::Int);

            println!("      Mapping {:?} to {:?}", value, reg);
            reg
        })
    }

    fn map_param(&mut self, param: Parameter) -> VReg {
        self.get_or_new(param.into())
    }

    fn map_instr(&mut self, instr: Instruction) -> VReg {
        self.get_or_new(instr.into())
    }
}
