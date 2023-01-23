use std::collections::HashMap;
use std::iter::zip;

use regalloc2::{Inst, PReg, PRegSet, RegClass, VReg};
use regalloc2 as r2;

use crate::back::abi::{FunctionAbi, PassPosition};
use crate::back::layout::{Layout, TupleLayout};
use crate::back::register::RSize;
use crate::back::vcode::{AsmContext, VConst, VInstruction, VMem, VopLarge, VopRC, VopRCM, VopRM, VSymbol, VTarget};
use crate::mid::ir::{ArithmeticOp, Block, CastKind, ComparisonOp, Expression, ExpressionInfo, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Signed, StackSlot, Target, Terminator, Type, Value};
use crate::mid::util::bit_int::{BitInt, UStorage};

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

pub type MappedValue = VValue<VReg, StackPosition>;

pub struct ValueMapper<'p> {
    next_vreg: usize,
    prog: &'p Program,
    map_param_or_instr: HashMap<Value, MappedValue>,
}

#[derive(Debug, Copy, Clone)]
pub enum StackPosition {
    /// Proper IR slot.
    Slot(StackSlot),
    /// Either a function or block parameter.
    Param(Parameter),
    /// Used for instruction outputs.
    Instr(Instruction),
}

impl StackPosition {
    pub fn to_offset(&self, _: &AsmContext) -> usize {
        todo!()
    }
}

impl<'p> ValueMapper<'p> {
    pub fn new(prog: &'p Program) -> Self {
        ValueMapper {
            prog,
            next_vreg: 0,
            map_param_or_instr: Default::default(),
        }
    }

    pub fn new_vreg(&mut self) -> VReg {
        let index = self.next_vreg;
        self.next_vreg += 1;
        VReg::new(index, RegClass::Int)
    }

    fn map_param_or_instr(&mut self, value: Value, stack_pos: impl FnOnce() -> StackPosition) -> MappedValue {
        if let Some(&result) = self.map_param_or_instr.get(&value) {
            return result;
        }

        let layout = Layout::for_value(self.prog, value);
        let result = if layout.reg_size().is_some() {
            VValue::Small(self.new_vreg())
        } else {
            VValue::Large(stack_pos())
        };

        self.map_param_or_instr.insert(value, result);
        result
    }

    pub fn map_param(&mut self, param: Parameter) -> MappedValue {
        self.map_param_or_instr(param.into(), || StackPosition::Param(param))
    }

    pub fn map_instr(&mut self, instr: Instruction) -> MappedValue {
        self.map_param_or_instr(instr.into(), || StackPosition::Instr(instr))
    }

    pub fn vreg_count(&self) -> usize {
        self.next_vreg
    }

    pub fn stack_positions(&self) -> impl Iterator<Item=StackPosition> + '_ {
        self.map_param_or_instr.values()
            .filter_map(|value| option_match!(value, &VValue::Large(pos) => pos))
    }
}

pub struct Selector<'a, 'p> {
    pub prog: &'p Program,
    pub curr_func_abi: &'a FunctionAbi,

    pub symbols: &'a mut Symbols,
    pub values: &'a mut ValueMapper<'p>,

    pub instructions: &'a mut Vec<VInstruction>,
    pub expr_cache: &'a mut HashMap<Expression, VReg>,
}

// TODO make distinction between LValue and RValue like in front?
#[derive(Debug, Copy, Clone)]
pub enum VValue<S, L> {
    Small(S),
    Large(L),
}

impl<S: Copy, L: Copy> VValue<S, L> {
    pub fn as_small(&self) -> Option<S> {
        option_match!(self, &VValue::Small(inner) => inner)
    }

    pub fn as_large(&self) -> Option<L> {
        option_match!(self, &VValue::Large(inner) => inner)
    }
}

impl<S, L> VValue<S, L> {
    // unfortunately we can't implement the From/Into traits
    //   because they would conflict with the default identity impl
    fn into<SF: From<S>, LF: From<L>>(self) -> VValue<SF, LF> {
        match self {
            VValue::Small(s) => VValue::Small(SF::from(s)),
            VValue::Large(l) => VValue::Large(LF::from(l)),
        }
    }
}

impl Selector<'_, '_> {
    pub fn push(&mut self, instr: VInstruction) {
        let info = instr.to_inst_info();
        println!("    push {:?}", instr);
        println!("      as    {:?}", Inst::new(self.instructions.len()));
        println!("      args {:?}  {:?}", info.operands, info.branch_block_params);
        println!("      info {:?}", info);
        self.instructions.push(instr);
    }

    pub fn append_instr(&mut self, instr: Instruction) {
        let prog = self.prog;

        // TODO only invalidate expressions modified by this instruction instead of all of them?
        // TODO even better, properly schedule expressions in advance with dom_info and use_info
        self.expr_cache.clear();
        println!("    appending {:?}", instr);

        match *self.prog.get_instr(instr) {
            InstructionInfo::Load { addr, ty } => {
                let layout = Layout::for_type(prog, ty);

                let src = VMem::at(self.append_value_to_reg(addr));
                let dest = self.values.map_instr(instr);

                match dest {
                    VValue::Small(dest) => {
                        // TODO ensure we generate full size moves for reg->reg
                        let size = layout.reg_size().unwrap();
                        self.push(VInstruction::MovReg { size, dest, src: src.into() });
                    }
                    VValue::Large(dest) => {
                        let tmp = self.values.new_vreg();
                        self.push(VInstruction::MovLarge {
                            layout,
                            dest: dest.into(),
                            src: src.into(),
                            tmp,
                        });
                    }
                }
            }
            InstructionInfo::Store { addr, ty, value } => {
                let layout = Layout::for_type(prog, ty);

                // TODO ensure we can generate "store [esp+8], eax" if addr is stack slot
                let src = self.append_value(value);
                let dest = VMem::at(self.append_value_to_reg(addr));

                match src {
                    // TODO ensure we can generate "store [rax], 17" if value is const
                    VValue::Small(src) => {
                        let size = layout.reg_size().unwrap();
                        let src = self.force_rc(src, size);
                        self.push(VInstruction::MovMem { size, dest, src })
                    }
                    VValue::Large(src) => {
                        let tmp = self.values.new_vreg();
                        self.push(VInstruction::MovLarge {
                            layout,
                            dest: dest.into(),
                            src,
                            tmp,
                        });
                    }
                }
            }
            InstructionInfo::Call { target, ref args, conv: _ } => {
                let target_ty = prog.get_type(prog.type_of_value(target)).unwrap_func().unwrap();
                let abi = FunctionAbi::for_type(prog, target_ty);

                let reg_result = match abi.pass_ret.pos {
                    PassPosition::Reg(reg) => Some((self.values.new_vreg(), reg)),
                    PassPosition::StackSlot(_) => {
                        todo!("copy return value to correct stack position");
                    }
                };
                let target = self.append_value_to_rcm_new(target);

                // TODO re-order args to minimize register usage?
                let mut reg_args = vec![];
                for (&arg_value, param_abi) in zip(args, &abi.pass_params) {
                    match param_abi.pos {
                        PassPosition::Reg(arg_reg) => {
                            let arg = self.append_value_to_reg(arg_value);
                            reg_args.push((arg, arg_reg))
                        }
                        PassPosition::StackSlot(_) => {
                            todo!("copy stack param to correct stack position")
                        }
                    }
                }

                let mut clobbers = PRegSet::empty();
                for reg in &abi.volatile_registers {
                    clobbers.add(PReg::new(reg.index(), RegClass::Int));
                }

                self.push(VInstruction::Call { target, result: reg_result, reg_args, clobbers });
            }
            InstructionInfo::BlackBox { value } => {
                let layout = self.layout_of_value(value);

                let src = self.append_value(value);
                let dest = self.values.map_instr(instr);

                match dest {
                    VValue::Small(dest) => {
                        let src = src.as_small().unwrap();
                        let size = layout.reg_size().unwrap();
                        self.push(VInstruction::MovReg { size, dest, src });
                    }
                    VValue::Large(dest) => {
                        let src = src.as_large().unwrap();
                        let dest = dest.into();
                        let tmp = self.values.new_vreg();
                        self.push(VInstruction::MovLarge { layout, dest, src, tmp });
                    }
                }
            }
        }
    }

    pub fn append_terminator(&mut self, term: &Terminator) {
        self.expr_cache.clear();

        match *term {
            Terminator::Jump { ref target } => {
                let target = self.append_target(target);
                self.push(VInstruction::Jump { target })
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                let cond = self.append_value_to_reg(cond);
                let true_target = self.append_target(true_target);
                let false_target = self.append_target(false_target);
                self.push(VInstruction::Branch { cond, true_target, false_target });
            }
            Terminator::Return { value } => {
                // TODO ensure we don't do any useless stuff for void


                let value = match self.curr_func_abi.pass_ret.pos {
                    PassPosition::Reg(value_reg) => {
                        let value = self.append_value_to_reg(value);
                        Some((value, value_reg))
                    }
                    PassPosition::StackSlot(_) => {
                        todo!("write the return value to the right stack position");
                    }
                };

                self.push(VInstruction::ReturnAndStackFree { value });
            }
            Terminator::Unreachable => {
                self.push(VInstruction::Unreachable);
            }
            Terminator::LoopForever => {
                let label = self.symbols.new_label();
                self.push(VInstruction::LoopForever { label });
            }
        }
    }

    fn append_target(&mut self, target: &Target) -> VTarget {
        self.expr_cache.clear();
        let &Target { block, ref args } = target;
        let args = args.iter().map(|&arg| self.append_value_to_reg(arg)).collect();

        VTarget { block, args }
    }

    fn append_mul(&mut self, left: Value, right: Value) -> VReg {
        let size = self.reg_size_of_value(left).unwrap();
        // TODO handle this case, the registers are different and annoying
        assert!(size != RSize::S8, "Mul for byte not implemented yet");

        let result_high = self.values.new_vreg();
        let result_low = self.values.new_vreg();
        let left = self.append_value_to_reg(left);
        let right = self.append_value_to_rm(right);

        self.push(VInstruction::Mul {
            size,
            dest_high: result_high,
            dest_low: result_low,
            left,
            right,
        });

        result_low
    }

    fn append_div_mod(&mut self, signed: Signed, left: Value, right: Value) -> (VReg, VReg) {
        let size = self.reg_size_of_value(left).unwrap();

        // TODO handle this case, the registers are different and annoying
        assert!(size != RSize::S8, "Div for byte not implemented yet");

        let low = self.append_value_to_reg(left);
        let div = self.append_value_to_rm(right);

        let high = self.values.new_vreg();
        let quot = self.values.new_vreg();
        let rem = self.values.new_vreg();

        self.push(VInstruction::Clear(high));
        self.push(VInstruction::DivMod {
            size,
            signed,
            left_high: high,
            left_low: low,
            right: div,
            dest_quot: quot,
            dest_rem: rem,
        });

        (quot, rem)
    }

    fn append_arithmetic(&mut self, kind: ArithmeticOp, left: Value, right: Value) -> VReg {
        let size = self.reg_size_of_value(left).unwrap();

        let instr = match kind {
            ArithmeticOp::Add => "add",
            ArithmeticOp::Sub => "sub",
            ArithmeticOp::Mul => return self.append_mul(left, right),
            ArithmeticOp::And => "and",
            ArithmeticOp::Or => "or",
            ArithmeticOp::Xor => "xor",

            ArithmeticOp::Div(signed) => return self.append_div_mod(signed, left, right).0,
            ArithmeticOp::Mod(signed) => return self.append_div_mod(signed, left, right).1,
        };

        let result = self.values.new_vreg();
        let left = self.append_value_to_reg(left);
        let right = self.append_value_to_rcm_new(right);
        self.push(VInstruction::Binary {
            size,
            op: instr,
            dest: result,
            left,
            right,
        });
        result
    }

    #[must_use]
    fn append_expr(&mut self, expr: Expression) -> VReg {
        if let Some(&result) = self.expr_cache.get(&expr) {
            return result;
        }

        let prog = self.prog;

        let result = match *prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { kind, left, right } => {
                self.append_arithmetic(kind, left, right)
            }
            ExpressionInfo::Comparison { kind, left, right } => {
                let size = self.reg_size_of_value(left).unwrap();

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

                let before = self.values.new_vreg();
                let after = self.values.new_vreg();
                let left = self.append_value_to_reg(left);
                let right = self.append_value_to_rcm_new(right);

                // moves potentially inserted by register allocation can't change the flags
                self.push(VInstruction::Clear(before));
                self.push(VInstruction::Cmp { size, left, right, });
                self.push(VInstruction::Setcc {
                    cc: set_instr,
                    dest: after,
                    dest_before: before,
                });

                after
            }
            ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } => {
                let tuple_ty = prog.get_type(tuple_ty).unwrap_tuple().unwrap();
                let layout = TupleLayout::for_types(prog, tuple_ty.fields.iter().copied());

                let offset = layout.offsets[index as usize];
                let offset = BitInt::from_unsigned(RSize::FULL.bits(), offset as UStorage).unwrap();
                let offset = VConst::Const(offset).into();

                let base = self.append_value_to_reg(base);
                let dest = self.values.new_vreg();

                // TODO can we use LEA here as well?
                self.push(VInstruction::Binary {
                    size: RSize::FULL,
                    op: "add",
                    dest,
                    left: base,
                    right: offset,
                });
                dest
            }
            ExpressionInfo::PointerOffSet { ty, base, index } => {
                // TODO add fallback for non-reg sized types
                let size = self.reg_size_of_ty(ty).unwrap();
                let dest = self.values.new_vreg();
                let base = self.append_value_to_rc(base);
                let index = self.append_value_to_reg(index);
                self.push(VInstruction::Lea { dest, base, index, size });
                dest
            }
            ExpressionInfo::Cast { ty, kind, value } => {
                let size_before = self.reg_size_of_value(value).unwrap();
                let size_after = self.reg_size_of_ty(ty).unwrap();

                match kind {
                    CastKind::IntTruncate => {
                        // nothing to do, just return value
                        self.append_value_to_reg(value)
                    }
                    CastKind::IntExtend(signed) => {
                        let before = self.append_value_to_reg(value);
                        let after = self.values.new_vreg();
                        self.push(VInstruction::Extend {
                            signed,
                            size_after,
                            size_before,
                            dest: after,
                            src: before,
                        });
                        after
                    }
                }
            }
        };

        self.expr_cache.insert(expr, result);
        result
    }

    #[must_use]
    fn append_value(&mut self, value: Value) -> VValue<VopRCM, VopLarge> {
        let layout = self.layout_of_value(value);
        let is_large = layout.size_bytes > RSize::FULL.bytes();

        match value {
            Value::Immediate(value) => match value {
                Immediate::Void => VValue::Small(VopRCM::Undef),
                Immediate::Undef(_) => if is_large {
                    VValue::Large(VopLarge::Undef)
                } else {
                    VValue::Small(VopRCM::Undef)
                },
                Immediate::Const(cst) => {
                    assert!(!is_large, "Large consts not yet supported");
                    VValue::Small(VConst::Const(cst.value).into())
                }
            },
            Value::Global(value) => {
                assert!(!is_large, "Global values should be small");
                VValue::Small(VConst::Symbol(VSymbol::Global(value)).into())
            }
            Value::Scoped(value) => match value {
                Scoped::Slot(slot) => {
                    // TODO add Vop version of slots so we can inline them into load/store instructions
                    let dest = self.values.new_vreg();
                    let pos = StackPosition::Slot(slot);
                    self.push(VInstruction::StackPtr { dest, pos });
                    VValue::Small(dest.into())
                }
                Scoped::Param(param) => self.values.map_param(param).into(),
                Scoped::Instr(instr) => self.values.map_instr(instr).into(),
            },
            Value::Expr(expr) => {
                assert!(!is_large, "Large expressions not yet supported");
                VValue::Small(self.append_expr(expr).into())
            }
        }
    }

    // TODO remove new from name
    #[must_use]
    fn append_value_to_rcm_new(&mut self, value: Value) -> VopRCM {
        let value = self.append_value(value);
        value.as_small().unwrap_or_else(|| panic!("Expected small VopRCM, got {:?}", value))
    }

    #[must_use]
    fn append_value_to_rc(&mut self, value: Value) -> VopRC {
        let operand = self.append_value_to_rcm_new(value);
        let size = self.reg_size_of_value(value).unwrap();
        self.force_rc(operand, size)
    }

    #[must_use]
    fn append_value_to_rm(&mut self, value: Value) -> VopRM {
        let operand = self.append_value_to_rcm_new(value);
        let size = self.reg_size_of_value(value).unwrap();
        self.force_rm(operand, size)
    }

    #[must_use]
    fn append_value_to_reg(&mut self, value: Value) -> VReg {
        let operand = self.append_value_to_rcm_new(value);
        let size = self.reg_size_of_value(value).unwrap();
        self.force_reg(operand, size)
    }

    #[must_use]
    fn force_rc(&mut self, value: VopRCM, size: RSize) -> VopRC {
        match value {
            VopRCM::Undef => VopRC::Undef,
            VopRCM::Reg(reg) => reg.into(),
            VopRCM::Const(cst) => cst.into(),
            VopRCM::Mem(_) => self.force_reg(value, size).into(),
        }
    }

    #[must_use]
    fn force_rm(&mut self, value: VopRCM, size: RSize) -> VopRM {
        match value {
            VopRCM::Undef => VopRM::Undef,
            VopRCM::Reg(reg) => reg.into(),
            VopRCM::Mem(mem) => mem.into(),
            VopRCM::Const(_) => self.force_reg(value, size).into(),
        }
    }

    #[must_use]
    fn force_reg(&mut self, value: VopRCM, size: RSize) -> VReg {
        match value {
            VopRCM::Undef => {
                let dest = self.values.new_vreg();
                self.push(VInstruction::DefAnyReg(dest));
                dest
            }
            VopRCM::Reg(reg) => reg,
            VopRCM::Mem(_) | VopRCM::Const(_) => {
                let src = value;
                let dest = self.values.new_vreg();
                self.push(VInstruction::MovReg { size, dest, src });
                dest
            }
        }
    }

    fn layout_of_value(&self, value: impl Into<Value>) -> Layout {
        Layout::for_value(self.prog, value)
    }

    fn reg_size_of_value(&self, value: impl Into<Value>) -> Option<RSize> {
        self.layout_of_value(value).reg_size()
    }

    fn reg_size_of_ty(&self, ty: Type) -> Option<RSize> {
        Layout::for_type(self.prog, ty).reg_size()
    }
}
