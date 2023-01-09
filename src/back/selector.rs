use std::collections::HashMap;

use itertools::Itertools;
use regalloc2::{Inst, RegClass, VReg};
use regalloc2 as r2;

use crate::back::vcode::{Size, VConst, VInstruction, VMem, VopRC, VopRCM, VopRM, VSymbol, VTarget};
use crate::mid::ir::{ArithmeticOp, Block, ComparisonOp, Expression, ExpressionInfo, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Signed, StackSlot, Target, Terminator, Type, TypeInfo, Value};

#[derive(Default)]
pub struct Symbols {
    blocks: HashMap<Block, r2::Block>,
    next_label: usize,
}

impl Symbols {
    pub fn define_block(&mut self, block: Block, func_index: usize) {
        println!("  Defining {:?} -> {:?}", block, func_index);
        let prev = self.blocks.insert(block, r2::Block(func_index as u32));
        assert!(prev.is_none());
    }

    pub fn map_block(&mut self, block: Block) -> r2::Block {
        *self.blocks.get(&block).unwrap()
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
    pub slots: &'a HashMap<StackSlot, usize>,

    pub instructions: &'a mut Vec<VInstruction>,
    pub expr_cache: &'a mut HashMap<Expression, VReg>,
}

impl Selector<'_> {
    pub fn push(&mut self, instr: VInstruction) {
        let info = instr.to_inst_info();
        println!("    push {:?}", instr);
        println!("      as    {:?}", Inst::new(self.instructions.len()));
        println!("      args {:?}  {:?}", info.operands, info.branch_block_params);
        println!("      info {:?}", info);
        self.instructions.push(instr);
    }

    #[allow(dead_code)]
    fn dummy_reg(&mut self) -> VReg {
        let reg = self.vregs.new_vreg();
        self.push(VInstruction::DefAnyReg(reg));
        reg
    }

    pub fn append_instr(&mut self, instr: Instruction) {
        // TODO only invalidate expressions modified by this instruction instead of all of them?
        // TODO even better, properly schedule expressions in advance with dom_info and use_info
        self.expr_cache.clear();
        println!("    appending {:?}", instr);

        match *self.prog.get_instr(instr) {
            InstructionInfo::Load { addr, ty } => {
                let size = self.size_of_ty(ty);
                let addr = self.append_value_to_reg(addr);
                let result = self.vregs.map_instr(instr);
                self.push(VInstruction::MovReg(size, result, VMem::at(addr).into()));
            }
            InstructionInfo::Store { addr, ty, value } => {
                let addr = self.append_value_to_reg(addr);
                let value = self.append_value_to_rc(value);
                let size = self.size_of_ty(ty);
                self.push(VInstruction::MovMem(size, VMem::at(addr), value));
            }
            InstructionInfo::Call { target, ref args } => {
                let args = args.iter().map(|&arg| self.append_value_to_reg(arg)).collect_vec();
                let target = self.append_value_to_rcm(target);
                let result = self.vregs.map_instr(instr);
                self.push(VInstruction::Call(result, target, args));
            }
            InstructionInfo::BlackBox { value } => {
                let size = self.size_of_value(value);
                let value = self.append_value_to_reg(value);
                let result = self.vregs.map_instr(instr);
                self.push(VInstruction::MovReg(size, result, value.into()))
            }
        }
    }

    pub fn append_terminator(&mut self, term: &Terminator) {
        self.expr_cache.clear();
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

                self.push(VInstruction::ReturnAndStackFree(value));
            }
            Terminator::Unreachable => {
                self.push(VInstruction::Unreachable);
            }
            Terminator::LoopForever => {
                let label = self.symbols.new_label();
                self.push(VInstruction::LoopForever(label));
            }
        }
    }

    fn append_target(&mut self, target: &Target) -> VTarget {
        self.expr_cache.clear();
        let &Target { block, ref args } = target;
        let args = args.iter().map(|&arg| self.append_value_to_reg(arg)).collect();

        VTarget { block, args }
    }

    fn append_div_mod(&mut self, signed: Signed, left: Value, right: Value) -> (VReg, VReg) {
        let size = self.size_of_value(left);

        // TODO handle this case, the registers are different and annoying
        assert!(size != Size::S8, "Div for byte not implemented yet");

        let low = self.append_value_to_reg(left);
        let div = self.append_value_to_rm(right);

        let high = self.vregs.new_vreg();
        let quot = self.vregs.new_vreg();
        let rem = self.vregs.new_vreg();

        self.push(VInstruction::Clear(high));
        self.push(VInstruction::DivMod(size, signed, high, low, div, quot, rem));

        (quot, rem)
    }

    fn append_arithmetic(&mut self, kind: ArithmeticOp, left: Value, right: Value) -> VReg {
        let instr = match kind {
            ArithmeticOp::Add => "add",
            ArithmeticOp::Sub => "sub",
            ArithmeticOp::Mul => "mul",
            ArithmeticOp::And => "and",
            ArithmeticOp::Or => "or",
            ArithmeticOp::Xor => "xor",

            ArithmeticOp::Div(signed) => return self.append_div_mod(signed, left, right).0,
            ArithmeticOp::Mod(signed) => return self.append_div_mod(signed, left, right).1,
        };

        let size = self.size_of_value(left);
        let result = self.vregs.new_vreg();
        let left = self.append_value_to_reg(left);
        let right = self.append_value_to_rcm(right);
        self.push(VInstruction::Binary(size, instr, result, left, right));
        result
    }

    #[must_use]
    fn append_expr(&mut self, expr: Expression) -> VReg {
        if let Some(&result) = self.expr_cache.get(&expr) {
            return result;
        }

        let result = match *self.prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { kind, left, right } => {
                self.append_arithmetic(kind, left, right)
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

                let size = self.size_of_value(left);
                let before = self.vregs.new_vreg();
                let after = self.vregs.new_vreg();
                let left = self.append_value_to_reg(left);
                let right = self.append_value_to_rcm(right);

                // moves potentially inserted by register allocation can't change the flags
                self.push(VInstruction::Clear(before));
                self.push(VInstruction::Cmp(size, left, right));
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
                Immediate::Undef(_) => VopRCM::Undef,
                Immediate::Const(cst) => VConst::Const(cst.value).into(),
            },
            Value::Global(value) => {
                VConst::Symbol(VSymbol::Global(value)).into()
            }
            Value::Scoped(value) => match value {
                Scoped::Slot(slot) => {
                    let index = self.map_slot_to_index(slot);
                    VopRCM::Slot(index)
                }
                Scoped::Param(param) => self.vregs.map_param(param).into(),
                Scoped::Instr(instr) => self.vregs.map_instr(instr).into(),
            },
            Value::Expr(expr) => self.append_expr(expr).into(),
        }
    }

    #[must_use]
    fn append_value_to_rc(&mut self, value: Value) -> VopRC {
        let operand = self.append_value_to_rcm(value);
        let size = self.size_of_value(value);
        self.force_rc(operand, size)
    }

    #[must_use]
    fn append_value_to_rm(&mut self, value: Value) -> VopRM {
        let operand = self.append_value_to_rcm(value);
        let size = self.size_of_value(value);
        self.force_rm(operand, size)
    }

    #[must_use]
    fn append_value_to_reg(&mut self, value: Value) -> VReg {
        let size = self.size_of_value(value);
        let operand = self.append_value_to_rcm(value);
        self.force_reg(operand, size)
    }

    #[must_use]
    fn force_rc(&mut self, value: VopRCM, size: Size) -> VopRC {
        match value {
            VopRCM::Undef => VopRC::Undef,
            VopRCM::Reg(reg) => reg.into(),
            VopRCM::Const(cst) => cst.into(),
            VopRCM::Slot(_) | VopRCM::Mem(_) => self.force_reg(value, size).into(),
        }
    }

    #[must_use]
    fn force_rm(&mut self, value: VopRCM, size: Size) -> VopRM {
        match value {
            VopRCM::Undef => VopRM::Undef,
            VopRCM::Reg(reg) => reg.into(),
            VopRCM::Mem(mem) => mem.into(),
            VopRCM::Slot(_) | VopRCM::Const(_) => self.force_reg(value, size).into(),
        }
    }

    #[must_use]
    fn force_reg(&mut self, value: VopRCM, size: Size) -> VReg {
        match value {
            VopRCM::Undef => self.dummy_reg(),
            VopRCM::Reg(reg) => reg,
            VopRCM::Slot(index) => {
                assert!(size == Size::FULL);
                let reg = self.vregs.new_vreg();
                self.push(VInstruction::SlotPtr(reg, index));
                reg
            }
            VopRCM::Mem(_) | VopRCM::Const(_) => {
                let reg = self.vregs.new_vreg();
                self.push(VInstruction::MovReg(size, reg, value));
                reg
            }
        }
    }

    fn map_slot_to_index(&mut self, slot: StackSlot) -> usize {
        *self.slots.get(&slot).unwrap()
    }

    fn size_of_value(&self, value: Value) -> Size {
        self.size_of_ty(self.prog.type_of_value(value))
    }

    fn size_of_ty(&self, ty: Type) -> Size {
        match *self.prog.get_type(ty) {
            TypeInfo::Void => panic!("void type not supported"),
            TypeInfo::Integer { bits } => {
                match bits {
                    // TODO bool size? when stored 8bits, but when doing other stuff FULL?
                    1 => Size::FULL,
                    8 => Size::S8,
                    16 => Size::S16,
                    32 => Size::S32,
                    _ => panic!("integer type with {} bits not supported", bits),
                }
            }
            TypeInfo::Pointer => Size::FULL,
            TypeInfo::Func(_) => Size::FULL,
            TypeInfo::Tuple(_) => panic!("tuple type not supported"),
            TypeInfo::Array(_) => panic!("array type not supported"),
        }
    }
}
