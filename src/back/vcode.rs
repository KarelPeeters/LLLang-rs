use std::cmp::min_by_key;
use std::fmt::{Display, Formatter};
use std::fmt::Write;

use derive_more::From;
use regalloc2::{Operand, PReg, PRegSet, RegClass, VReg};

use crate::back::x86_asm_select::Allocs;
use crate::mid::ir::Const;

// TODO find proper names for these instructions, especially "binary" sucks
#[derive(Debug)]
pub enum VInstruction {
    DummyDef(VReg),

    // set the given register to zero
    Clear(VReg),

    // read as "move into .. from .."
    MovReg(VReg, VopRCM),
    MovMem(VMem, VopRC),

    // args are "target = left (+) right"
    // target and left must be the same register, this is handled with a register allocation constraint
    Binary(&'static str, VReg, VReg, VopRCM),

    Cmp(VReg, VopRCM),
    Test(VReg, VopRCM),

    // TODO allow mem operand here
    Setcc(&'static str, VReg, VReg),

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

impl VConst {
    pub fn to_asm(&self) -> String {
        match self {
            VConst::Const(cst) => min_by_key(
                format!("{}", cst.value.unsigned()),
                format!("{}", cst.value.signed()),
                |s| s.len(),
            ),
            VConst::Symbol(symbol) => format!("{}", symbol),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum VSymbol {
    Func(usize),
    Ext(usize),
    Data(usize),
    Block(usize),
    Label(usize),
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
    fn to_asm(&self, allocs: &Allocs) -> String;
}

impl VOperand for VMem {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        f(RegOperand::Use(self.reg));
    }

    fn to_asm(&self, allocs: &Allocs) -> String {
        let &VMem { reg, offset } = self;

        let reg = reg.to_asm(allocs);
        if offset == 0 {
            format!("[{}]", reg)
        } else {
            format!("[{}{:+}]", reg, offset)
        }
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

    fn to_asm(&self, allocs: &Allocs) -> String {
        match *self {
            VopRCM::Reg(reg) => {
                let preg = allocs.map_reg(reg);
                preg_to_asm(preg).to_string()
            }
            VopRCM::Const(cst) => cst.to_asm(),
            VopRCM::Mem(mem) => mem.to_asm(allocs),
        }
    }
}

const REG_NAMES: &[&str] = &["eax", "ebx", "ecx", "edx"];
const REG_NAMES_BYTE: &[&str] = &["al", "bl", "cl", "dl"];

pub fn preg_to_asm(preg: PReg) -> &'static str {
    REG_NAMES[preg.index()]
}

macro_rules! impl_vop_for {
    ($vop:ty) => {
        impl VOperand for $vop {
            fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
                VopRCM::from(*self).for_each_reg(f)
            }
            fn to_asm(&self, allocs: &Allocs) -> String {
                VopRCM::from(*self).to_asm(allocs)
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
            VInstruction::DummyDef(dest) => {
                operands.push_def(dest);
            }
            VInstruction::Clear(dest) => {
                operands.push_def(dest);
            }
            VInstruction::MovReg(dest, source) => {
                if let VopRCM::Reg(source) = source {
                    return InstInfo::mov(Operand::reg_def(dest), Operand::reg_use(source));
                }

                operands.push_use(source);
                operands.push_def(dest);
            }
            VInstruction::MovMem(dest, source) => {
                operands.push_use(source);
                operands.push_def(dest);
            }
            VInstruction::Binary(_instr, dest, left, right) => {
                operands.push(Operand::reg_reuse_def(dest, 1));
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Cmp(left, right) | VInstruction::Test(left, right) => {
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Setcc(_instr, dest, src) => {
                // setcc doesn't modify the upper bits of the register, so just adding a def is not enough
                operands.push(Operand::reg_reuse_def(dest, 1));
                operands.push_use(src);
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
                    let eax = PReg::new(0, RegClass::Int);
                    operands.push(Operand::reg_fixed_use(value, eax));
                }
                return InstInfo::ret(operands);
            }
            VInstruction::Unreachable => {
                return InstInfo::ret(operands);
            }
        }

        InstInfo::simple(operands)
    }

    pub fn to_asm(&self, allocs: &Allocs) -> String {
        match *self {
            VInstruction::DummyDef(reg) =>
                format!("; dummy {:?}", reg.to_asm(allocs)),
            VInstruction::Clear(dest) => {
                let dest = dest.to_asm(allocs);
                format!("xor {}, {}", dest, dest)
            }
            VInstruction::MovReg(dest, source) =>
                format!("mov {}, {}", dest.to_asm(allocs), source.to_asm(allocs)),
            VInstruction::MovMem(dest, source) =>
                format!("mov {}, {}", dest.to_asm(allocs), source.to_asm(allocs)),
            VInstruction::Binary(instr, dest, left, right) => {
                assert_eq!(allocs.map_reg(dest), allocs.map_reg(left));
                format!("{} {}, {}", instr, left.to_asm(allocs), right.to_asm(allocs))
            }
            VInstruction::Cmp(left, right) =>
                format!("cmp {}, {}", left.to_asm(allocs), right.to_asm(allocs)),
            VInstruction::Test(left, right) =>
                format!("test {}, {}", left.to_asm(allocs), right.to_asm(allocs)),
            VInstruction::Setcc(instr, dest, source) => {
                assert_eq!(allocs.map_reg(dest), allocs.map_reg(source));
                format!("{} {}", instr, REG_NAMES_BYTE[allocs.map_reg(dest).index()])
            }
            VInstruction::Jump(ref target) =>
                format!("jmp {}", target.block),
            VInstruction::Branch(cond, ref true_target, ref false_target) => {
                let cond = cond.to_asm(allocs);

                let mut s = String::new();
                let f = &mut s;
                writeln!(f, "test {}, {}", cond, cond).unwrap();
                writeln!(f, "jnz {}", true_target.block).unwrap();
                writeln!(f, "jmp {}", false_target.block).unwrap();

                s
            }
            VInstruction::Return(_value) => {
                format!("ret 0")
            }
            VInstruction::Unreachable => {
                format!("hlt")
            }
        }
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

#[derive(Debug)]
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

    fn mov(dest: Operand, source: Operand) -> Self {
        InstInfo {
            is_ret: false,
            is_branch: false,
            // order is source,dest
            is_move: Some((source, dest)),
            operands: vec![dest, source],
            clobbers: PRegSet::default(),
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
            VSymbol::Label(id) => write!(f, "label_{}", id),
        }
    }
}
