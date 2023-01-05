use std::fmt::{Display, Formatter};

use derive_more::From;
use regalloc2::{Operand, PRegSet, VReg};

use crate::mid::ir::Const;

// TODO find proper names for these instructions, especially "binary" sucks
#[derive(Debug)]
pub enum VInstruction {
    DummyDef(VReg),

    // read as "move into .. from .."
    MovReg(VReg, VopRCM),
    MovMem(VMem, VopRC),

    // args are "target = left (+) right"
    // target and left must be the same register, this is handled with a register allocation constraint
    Binary(&'static str, VReg, VReg, VopRCM),

    Cmp(VReg, VopRCM),
    Test(VReg, VopRCM),

    Setcc(&'static str, VopRM),

    Jump(VTarget),

    // TODO make sure we end up generating good branch code
    Branch(VReg, VTarget, VTarget),
    Return(Option<VReg>),
    Unreachable,
}

pub enum RegOperand {
    Adaptive(VReg),
    Use(VReg),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRCM {
    Reg(VReg),
    Const(VConst),
    Mem(VMem),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRC {
    Reg(VReg),
    Const(VConst),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRM {
    Reg(VReg),
    Mem(VMem),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VConst {
    Const(Const),
    Symbol(VSymbol),
}

#[derive(Debug, Copy, Clone)]
pub enum VSymbol {
    Func(usize),
    Ext(usize),
    Data(usize),
    Block(usize),
}

#[derive(Debug, Copy, Clone)]
pub struct VMem {
    reg: VReg,
    offset: isize,
}

#[derive(Debug)]
pub struct VTarget {
    pub block: VSymbol,
    pub args: Vec<VReg>,
}

impl VMem {
    pub fn at_offset(reg: VReg, offset: isize) -> Self {
        VMem { reg, offset }
    }

    pub fn at(reg: VReg) -> Self {
        VMem { reg, offset: 0 }
    }
}

impl From<VopRM> for VopRCM {
    fn from(value: VopRM) -> Self {
        match value {
            VopRM::Reg(reg) => VopRCM::Reg(reg),
            VopRM::Mem(mem) => VopRCM::Mem(mem),
        }
    }
}

impl From<VopRC> for VopRCM {
    fn from(value: VopRC) -> Self {
        match value {
            VopRC::Reg(reg) => VopRCM::Reg(reg),
            VopRC::Const(cst) => VopRCM::Const(cst),
        }
    }
}

pub trait VOperand {
    fn for_each_reg(&self, f: impl FnMut(RegOperand));
}

impl VOperand for VMem {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        f(RegOperand::Use(self.reg));
    }
}

impl VOperand for VopRCM {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match *self {
            VopRCM::Reg(reg) => f(RegOperand::Adaptive(reg)),
            VopRCM::Const(_) => {}
            VopRCM::Mem(mem) => mem.for_each_reg(f)
        }
    }
}

macro_rules! impl_vop_for {
    ($vop:ty) => {
        impl VOperand for $vop {
            fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
                VopRCM::from(*self).for_each_reg(f)
            }
        }
    };
}

impl_vop_for!(VopRC);
impl_vop_for!(VopRM);
impl_vop_for!(VReg);

impl VInstruction {
    pub fn to_inst_info(&self) -> InstInfo {
        let mut operands = Operands::default();

        match *self {
            VInstruction::DummyDef(result) => {
                operands.push_def(result);
            }
            VInstruction::MovReg(target, source) => {
                operands.push_use(source);
                operands.push_def(target);
            }
            VInstruction::MovMem(target, source) => {
                operands.push_use(source);
                operands.push_def(target);
            }
            VInstruction::Binary(_instr, result, left, right) => {
                operands.push_use(left);
                operands.push_use(right);
                operands.push(Operand::reg_reuse_def(result, 0));
            }
            VInstruction::Cmp(left, right) | VInstruction::Test(left, right) => {
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Setcc(_instr, result) => {
                operands.push_def(result);
            }

            VInstruction::Jump(ref target) => {
                return InstInfo::branch(operands, vec![target.args.clone()]);
            }
            VInstruction::Branch(cond, ref true_target, ref false_target) => {
                operands.push_use(cond);
                let params = vec![true_target.args.clone(), false_target.args.clone()];
                return InstInfo::branch(operands, params);
            }
            VInstruction::Return(value) => {
                if let Some(value) = value {
                    operands.push_use(value);
                }
                return InstInfo::ret(operands);
            }
            VInstruction::Unreachable => {
                return InstInfo::ret(operands);
            }
        }

        InstInfo::simple(operands)
    }
}

#[derive(Default)]
struct Operands {
    operands: Vec<Operand>,
    clobbers: PRegSet,
}

impl Operands {
    pub fn finish(self) -> (Vec<Operand>, PRegSet) {
        let Operands { operands, clobbers } = self;
        (operands, clobbers)
    }

    fn push(&mut self, operand: Operand) {
        self.operands.push(operand)
    }

    fn push_use(&mut self, vop: impl VOperand) {
        vop.for_each_reg(|reg| match reg {
            RegOperand::Adaptive(reg) => self.push(Operand::reg_use(reg)),
            RegOperand::Use(reg) => self.push(Operand::reg_use(reg)),
        });
    }

    fn push_def(&mut self, vop: impl VOperand) {
        vop.for_each_reg(|reg| match reg {
            RegOperand::Adaptive(reg) => self.push(Operand::reg_def(reg)),
            RegOperand::Use(reg) => self.push(Operand::reg_use(reg)),
        });
    }
}

pub struct InstInfo {
    // ret/unreachable -> ret
    pub is_ret: bool,
    // jump/branch -> branch
    pub is_branch: bool,

    // TODO figure out when this should be set, maybe for stack loads/stores?
    pub is_move: Option<(Operand, Operand)>,
    pub operands: Vec<Operand>,
    pub clobbers: PRegSet,

    pub branch_block_params: Vec<Vec<VReg>>,
}

impl InstInfo {
    fn simple(operands: Operands) -> Self {
        let (operands, clobbers) = operands.finish();
        InstInfo {
            is_ret: false,
            is_branch: false,
            is_move: None,
            operands,
            clobbers,
            branch_block_params: vec![],
        }
    }

    fn branch(operands: Operands, block_params: Vec<Vec<VReg>>) -> Self {
        let (operands, clobbers) = operands.finish();
        InstInfo {
            is_ret: false,
            is_branch: true,
            is_move: None,
            operands,
            clobbers,
            branch_block_params: block_params,
        }
    }

    fn ret(operands: Operands) -> Self {
        let (operands, clobbers) = operands.finish();
        InstInfo {
            is_ret: true,
            is_branch: false,
            is_move: None,
            operands,
            clobbers,
            branch_block_params: vec![],
        }
    }
}

impl Display for VSymbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            VSymbol::Func(id) => write!(f, "func_{}", id),
            VSymbol::Ext(id) => write!(f, "ext_{}", id),
            VSymbol::Data(id) => write!(f, "data_{}", id),
            VSymbol::Block(id) => write!(f, "block_{}", id),
        }
    }
}
