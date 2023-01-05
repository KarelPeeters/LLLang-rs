use std::collections::HashMap;

use regalloc2::{Inst, InstRange, Operand, PRegSet, RegClass};
use regalloc2 as r2;
use regalloc2::VReg;

use crate::back::vcode::{InstInfo, VConst, VInstruction, VMem, VopRC, VopRCM, VSymbol, VTarget};
use crate::mid::ir::{ArithmeticOp, Block, BlockInfo, ComparisonOp, Expression, ExpressionInfo, Global, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Signed, Target, Terminator, Value};
use crate::util::{Never, NeverExt};

pub fn lower_new(prog: &Program) -> String {
    let mut symbols = Symbols::default();

    for (func, _) in &prog.nodes.funcs {
        println!("Func {:?}", func);

        let func_info = prog.get_func(func);
        let mut mapper = VRegMapper::default();

        prog.try_visit_blocks(func_info.entry, |block| {
            println!("  Block {:?}", block);

            let BlockInfo { params, instructions, terminator } = prog.get_block(block);

            let mut builder = VBuilder {
                prog,
                instructions: vec![],
                vregs: &mut mapper,
                expr_cache: &mut Default::default(),
                symbols: &mut symbols,
            };

            for &instr in instructions {
                builder.append_instr(instr);
            }

            builder.append_terminator(terminator);

            Never::UNIT
        }).no_err();
    }

    println!("Exiting process");
    std::process::exit(0);
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
}

impl Symbols {
    fn map_global(&mut self, value: Global) -> VSymbol {
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

    fn map_block(&mut self, block: Block) -> VSymbol {
        let next = self.blocks.len();
        let id = *self.blocks.entry(block).or_insert(next);
        VSymbol::Block(id)
    }
}

struct VBuilder<'a> {
    instructions: Vec<VInstruction>,
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
        println!("      {:?}  {:?}", info.operands, info.branch_block_params);
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
                let true_target = self.append_target(true_target);
                let false_target = self.append_target(false_target);
                self.push(VInstruction::Branch(cond, true_target, false_target));
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

        VTarget {
            block: self.symbols.map_block(block),
            args: args.iter().map(|&arg| self.append_value_to_reg(arg)).collect(),
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
    insts: Vec<InstInfo>,
    vregs: usize,

    block_map: HashMap<Block, r2::Block>,
    _mapper: VRegMapper,
}

struct R2BlockInfo {
    inst_range: InstRange,
    succs: Vec<r2::Block>,
    preds: Vec<r2::Block>,
    params: Vec<VReg>,
}

impl r2::Function for FuncWrapper {
    fn num_insts(&self) -> usize {
        self.insts.len()
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
        self.insts[inst.0 as usize].is_ret
    }

    fn is_branch(&self, inst: Inst) -> bool {
        self.insts[inst.0 as usize].is_branch
    }

    fn branch_blockparams(&self, _: r2::Block, inst: Inst, succ_idx: usize) -> &[VReg] {
        &self.insts[inst.0 as usize].branch_block_params[succ_idx]
    }

    fn is_move(&self, inst: Inst) -> Option<(Operand, Operand)> {
        self.insts[inst.0 as usize].is_move
    }

    fn inst_operands(&self, inst: Inst) -> &[Operand] {
        &self.insts[inst.0 as usize].operands
    }

    fn inst_clobbers(&self, inst: Inst) -> PRegSet {
        self.insts[inst.0 as usize].clobbers
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