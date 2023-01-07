use std::collections::HashMap;

use regalloc2::{Inst, RegClass, VReg};
use regalloc2 as r2;

use crate::back::vcode::{VConst, VInstruction, VMem, VopRC, VopRCM, VSymbol, VTarget};
use crate::mid::ir::{ArithmeticOp, Block, ComparisonOp, Expression, ExpressionInfo, Global, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Signed, Target, Terminator, Value};

#[derive(Default)]
pub struct Symbols {
    globals: HashMap<Global, usize>,
    next_func: usize,
    next_ext: usize,
    next_data: usize,

    blocks: HashMap<Block, usize>,
    next_label: usize,
}

impl Symbols {
    pub fn map_global(&mut self, value: impl Into<Global>) -> VSymbol {
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

    pub fn define_block(&mut self, block: Block, index: usize) {
        println!("  Defining {:?} -> {:?}", block, index);
        let prev = self.blocks.insert(block, index);
        assert!(prev.is_none());
    }

    pub fn map_block(&mut self, block: Block) -> (VSymbol, r2::Block) {
        let id = *self.blocks.get(&block).unwrap();
        let result = (VSymbol::Block(id), r2::Block(id as u32));
        result
    }

    #[allow(dead_code)]
    pub fn new_label(&mut self) -> VSymbol {
        let id = self.next_label;
        self.next_label += 1;
        VSymbol::Label(id)
    }
}

#[derive(Default)]
pub struct VRegMapper {
    next_vreg: usize,
    value_map: HashMap<Value, VReg>,
}

impl VRegMapper {
    pub fn new_vreg(&mut self) -> VReg {
        let index = self.next_vreg;
        self.next_vreg += 1;
        VReg::new(index, RegClass::Int)
    }

    pub fn get_or_new(&mut self, value: Value) -> VReg {
        let next_vreg = &mut self.next_vreg;
        *self.value_map.entry(value).or_insert_with(|| {
            let index = *next_vreg;
            *next_vreg += 1;
            let reg = VReg::new(index, RegClass::Int);

            println!("      Mapping {:?} to {:?}", value, reg);
            reg
        })
    }

    pub fn map_param(&mut self, param: Parameter) -> VReg {
        self.get_or_new(param.into())
    }

    pub fn map_instr(&mut self, instr: Instruction) -> VReg {
        self.get_or_new(instr.into())
    }

    pub fn vreg_count(&self) -> usize {
        self.next_vreg
    }
}

pub struct Selector<'a> {
    pub prog: &'a Program,

    pub symbols: &'a mut Symbols,
    pub vregs: &'a mut VRegMapper,

    pub instructions: &'a mut Vec<VInstruction>,
    pub expr_cache: &'a mut HashMap<Expression, VReg>,
}

impl Selector<'_> {
    fn push(&mut self, instr: VInstruction) {
        let info = instr.to_inst_info();
        println!("    push {:?}", instr);
        println!("      as    {:?}", Inst::new(self.instructions.len()));
        println!("      args {:?}  {:?}", info.operands, info.branch_block_params);
        println!("      info {:?}", info);
        self.instructions.push(instr);
    }

    #[allow(dead_code)]
    fn dummy_reg(&mut self) -> VReg {
        let vreg = self.vregs.new_vreg();
        self.push(VInstruction::DummyDef(vreg));
        vreg
    }

    pub fn append_instr(&mut self, instr: Instruction) {
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
                self.push(VInstruction::MovMem(VMem::at(addr), value));
            }
            InstructionInfo::Call { .. } => todo!("call"),
            InstructionInfo::BlackBox { value } => {
                let value = self.append_value_to_reg(value);
                let result = self.vregs.map_instr(instr);
                self.push(VInstruction::MovReg(result, value.into()))
            }
        }
    }

    pub fn append_terminator(&mut self, term: &Terminator) {
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
            Terminator::LoopForever => {
                let label = self.symbols.new_label();
                self.push(VInstruction::LoopForever(label));
            },
        }
    }

    fn append_target(&mut self, target: &Target) -> VTarget {
        let &Target { block, ref args } = target;
        let args = args.iter().map(|&arg| self.append_value_to_reg(arg)).collect();

        let block_mapped = self.symbols.map_block(block).0;

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
                result
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

                let before = self.vregs.new_vreg();
                let after = self.vregs.new_vreg();
                let left = self.append_value_to_reg(left);
                let right = self.append_value_to_rcm(right);

                // moves potentially inserted by register allocation can't change the flags
                self.push(VInstruction::Clear(before));
                self.push(VInstruction::Cmp(left, right));
                self.push(VInstruction::Setcc(set_instr, after, before));

                after
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
