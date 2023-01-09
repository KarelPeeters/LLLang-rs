use std::cmp::min_by_key;
use std::fmt::Write;

use derive_more::From;
use indexmap::IndexMap;
use regalloc2::{Allocation, AllocationKind, Operand, PReg, PRegSet, RegClass, VReg};

use crate::mid::ir::{Block, Global, Program, Signed};
use crate::mid::util::bit_int::BitInt;
use crate::util::arena::IndexType;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Size {
    S8,
    S16,
    S32,
}

impl Size {
    pub const FULL: Size = Size::S32;

    pub fn bits(self) -> u32 {
        self.bytes() * 8
    }

    pub fn bytes(self) -> u32 {
        match self {
            Size::S8 => 1,
            Size::S16 => 2,
            Size::S32 => 4,
        }
    }

    pub fn index(self) -> usize {
        match self {
            Size::S8 => 0,
            Size::S16 => 1,
            Size::S32 => 2,
        }
    }

    pub fn keyword(self) -> &'static str {
        match self {
            Size::S8 => "byte",
            Size::S16 => "word",
            Size::S32 => "dword",
        }
    }
}

// TODO find proper names for these instructions, especially "binary" sucks
#[derive(Debug)]
pub enum VInstruction {
    // utilities for marking registers as defined
    DefAnyReg(VReg),
    DefFixedReg(VReg, PReg),

    /// set the given register to zero
    Clear(VReg),

    // read as "move into .. from .."
    MovReg(Size, VReg, VopRCM),
    MovMem(Size, VMem, VopRC),

    /// target = base + index * size
    Lea(VReg, VopRC, VReg, Size),

    /// args are "target = left (+) right"
    /// target and left must be the same register, this is handled with a register allocation constraint
    Binary(Size, &'static str, VReg, VReg, VopRCM),

    /// result_high, result_low, left, right
    Mul(Size, VReg, VReg, VReg, VopRM),
    /// signed, high, low, div, quot, rem
    DivMod(Size, Signed, VReg, VReg, VopRM, VReg, VReg),

    /// signed, size after, size before, after, before
    Extend(Signed, Size, Size, VReg, VReg),

    /// result, target, args
    Call(VReg, VopRCM, Vec<VReg>),

    // compare instructions
    Cmp(Size, VReg, VopRCM),
    Test(Size, VReg, VopRCM),
    // TODO allow mem operand here
    Setcc(&'static str, VReg, VReg),

    // terminators
    Jump(VTarget),
    // TODO make sure we end up generating good branch code
    Branch(VReg, VTarget, VTarget),
    ReturnAndStackFree(Option<VReg>),
    Unreachable,
    LoopForever(VSymbol),

    /// increase the stack size at the start of the function
    StackAlloc,

    SlotPtr(VReg, usize),
}

pub enum RegOperand {
    Adaptive(VReg),
    Use(VReg),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRCM {
    Undef,
    Slot(usize),
    Reg(VReg),
    Const(VConst),
    Mem(VMem),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRC {
    Undef,
    Reg(VReg),
    Const(VConst),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRM {
    Undef,
    Reg(VReg),
    Mem(VMem),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VConst {
    Const(BitInt),
    Symbol(VSymbol),
}

// TODO merge this with VopRM? it's the same except it has a PReg instead of VReg
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum VRegPos {
    PReg(PReg),
    Slot(usize),
}

impl VConst {
    pub fn to_asm(&self, ctx: &AsmContext, size: Size) -> String {
        match self {
            VConst::Const(value) => {
                assert_eq!(value.bits(), size.bits(), "Tried to store {:?} in {:?}", value, size);
                min_by_key(
                    format!("{}", value.unsigned()),
                    format!("{}", value.signed()),
                    |s| s.len(),
                )
            }
            VConst::Symbol(symbol) => symbol.to_asm(ctx),
        }
    }
}

impl From<Allocation> for VRegPos {
    fn from(value: Allocation) -> Self {
        match value.kind() {
            AllocationKind::None => unreachable!(),
            AllocationKind::Reg => VRegPos::PReg(value.as_reg().unwrap()),
            AllocationKind::Stack => {
                let slot = value.as_stack().unwrap();
                assert!(slot.is_valid());
                VRegPos::Slot(slot.index())
            }
        }
    }
}

impl VRegPos {
    fn is_preg(self, preg: PReg) -> bool {
        self == VRegPos::PReg(preg)
    }

    fn as_preg(self) -> Option<PReg> {
        option_match!(self, VRegPos::PReg(preg) => preg)
    }

    pub fn to_asm(self, size: Size) -> String {
        match self {
            VRegPos::PReg(preg) => preg_to_asm(preg, size).to_string(),
            // TODO change this 4 when moving to x64
            VRegPos::Slot(index) => format!("[esp+{}]", 4 * index + 4),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum VSymbol {
    Global(Global),
    Block(Block),
    Label(usize),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VPReg {
    V(VReg),
    // PReg should not be part of the normally allocated registers
    P(PReg),
}

#[derive(Debug, Copy, Clone)]
pub struct VMem {
    reg: VPReg,
    offset: isize,
}

#[derive(Debug)]
pub struct VTarget {
    pub block: Block,
    pub args: Vec<VReg>,
}

impl VPReg {
    fn to_asm(self, ctx: &AsmContext, size: Size) -> String {
        match self {
            VPReg::V(vreg) => vreg.to_asm(ctx, size),
            VPReg::P(preg) => preg_to_asm(preg, size).to_string(),
        }
    }
}

impl VMem {
    pub fn at_offset(reg: impl Into<VPReg>, offset: isize) -> Self {
        VMem { reg: reg.into(), offset }
    }

    pub fn at(reg: impl Into<VPReg>) -> Self {
        VMem { reg: reg.into(), offset: 0 }
    }
}

impl From<VopRM> for VopRCM {
    fn from(value: VopRM) -> Self {
        match value {
            VopRM::Undef => VopRCM::Undef,
            VopRM::Reg(reg) => VopRCM::Reg(reg),
            VopRM::Mem(mem) => VopRCM::Mem(mem),
        }
    }
}

impl From<VopRC> for VopRCM {
    fn from(value: VopRC) -> Self {
        match value {
            VopRC::Undef => VopRCM::Undef,
            VopRC::Reg(reg) => VopRCM::Reg(reg),
            VopRC::Const(cst) => VopRCM::Const(cst),
        }
    }
}

pub trait VOperand {
    fn for_each_reg(&self, f: impl FnMut(RegOperand));
    fn to_asm(&self, ctx: &AsmContext, size: Size) -> String;
    fn is_const_zero(&self) -> bool;
}

impl VOperand for VMem {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match self.reg {
            VPReg::V(reg) => f(RegOperand::Use(reg)),
            VPReg::P(_) => {}
        }
    }

    fn to_asm(&self, ctx: &AsmContext, _: Size) -> String {
        let &VMem { reg, offset } = self;

        // pointer are full-sized, not the result size
        let reg = reg.to_asm(ctx, Size::FULL);
        if offset == 0 {
            format!("[{}]", reg)
        } else {
            format!("[{}{:+}]", reg, offset)
        }
    }

    fn is_const_zero(&self) -> bool {
        false
    }
}

impl VOperand for VopRCM {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match *self {
            VopRCM::Undef => {}
            VopRCM::Slot(_) => {}
            VopRCM::Reg(reg) => f(RegOperand::Adaptive(reg)),
            VopRCM::Const(_) => {}
            VopRCM::Mem(mem) => mem.for_each_reg(f)
        }
    }

    fn to_asm(&self, ctx: &AsmContext, size: Size) -> String {
        match *self {
            // TODO this only works because all Vops accept a register, which is kind of brittle
            VopRCM::Undef => preg_to_asm(PREG_A, size).to_string(),
            VopRCM::Slot(index) => {
                let offset = ctx.stack_layout.slot_offset(index);
                format!("[esp+{}]", offset)
            }
            VopRCM::Reg(reg) => ctx.map_reg(reg).to_asm(size),
            VopRCM::Const(cst) => cst.to_asm(ctx, size),
            VopRCM::Mem(mem) => mem.to_asm(ctx, size),
        }
    }

    fn is_const_zero(&self) -> bool {
        match self {
            VopRCM::Undef => false,
            VopRCM::Reg(_) => false,
            VopRCM::Slot(_) => false,
            VopRCM::Const(VConst::Const(cst)) => cst.is_zero(),
            VopRCM::Const(VConst::Symbol(_)) => false,
            VopRCM::Mem(_) => false,
        }
    }
}

// TODO this is not really the right order, but do we care?
pub const PREG_A: PReg = PReg::new(0, RegClass::Int);
pub const PREG_B: PReg = PReg::new(1, RegClass::Int);
pub const PREG_C: PReg = PReg::new(2, RegClass::Int);
pub const PREG_D: PReg = PReg::new(3, RegClass::Int);
pub const PREG_SI: PReg = PReg::new(4, RegClass::Int);
pub const PREG_DI: PReg = PReg::new(5, RegClass::Int);

pub const GENERAL_PREGS: &[PReg] = &[PREG_A, PREG_B, PREG_C, PREG_D, PREG_SI, PREG_DI];

pub const PREG_BASE_PTR: PReg = PReg::new(6, RegClass::Int);
pub const PREG_STACK_PTR: PReg = PReg::new(7, RegClass::Int);

const PREG_NAMES: &[[&str; 3]] = &[
    ["eax", "ax", "al"],
    ["ebx", "bx", "bl"],
    ["ecx", "cx", "cl"],
    ["edx", "dx", "dl"],
    ["esi", "si", "sil"],
    ["edi", "di", "dil"],
];

// TODO use some proper ABI settings, maybe depending on the platform?
pub const ABI_PARAM_REGS: &[PReg] = &[PREG_A, PREG_B, PREG_C, PREG_D, PREG_SI, PREG_DI];
pub const ABI_RETURN_REG: PReg = PREG_A;

pub fn preg_to_asm(preg: PReg, size: Size) -> &'static str {
    let slice = PREG_NAMES[preg.index()];
    slice[slice.len() - 1 - size.index()]
}

macro_rules! impl_vop_for {
    ($vop:ty) => {
        impl VOperand for $vop {
            fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
                VopRCM::from(*self).for_each_reg(f)
            }
            fn to_asm(&self, ctx: &AsmContext, size: Size) -> String {
                VopRCM::from(*self).to_asm(ctx, size)
            }
            fn is_const_zero(&self) -> bool {
                VopRCM::from(*self).is_const_zero()
            }
        }
    };
}
impl_vop_for!(VopRC);
impl_vop_for!(VopRM);
impl_vop_for!(VReg);

#[derive(Debug, Clone)]
pub struct AsmContext<'a> {
    pub prog: &'a Program,
    // TODO maybe change this to be a vec, it's tiny anyways
    pub allocs: IndexMap<VReg, Allocation>,
    pub stack_layout: StackLayout,
}

impl AsmContext<'_> {
    pub fn map_reg(&self, reg: VReg) -> VRegPos {
        (*self.allocs.get(&reg).unwrap()).into()
    }
}

#[derive(Debug, Clone)]
pub struct StackLayout {
    pub slot_bytes: usize,
    pub spill_bytes: usize,
    pub param_bytes: usize,
}

impl StackLayout {
    // TODO this depends on the calling convention
    pub fn alloc_bytes(&self) -> usize {
        self.slot_bytes + self.spill_bytes
    }

    pub fn free_bytes(&self) -> usize {
        self.param_bytes + self.slot_bytes + self.spill_bytes
    }

    pub fn spill_offset(&self, index: usize) -> usize {
        index * 4
    }

    pub fn slot_offset(&self, index: usize) -> usize {
        index * 4 + self.spill_bytes
    }
}

impl VInstruction {
    pub fn to_inst_info(&self) -> InstInfo {
        let mut operands = Operands::default();

        match *self {
            VInstruction::DefAnyReg(dest) => {
                operands.push_def(dest);
            }
            VInstruction::DefFixedReg(dest, preg) => {
                operands.push(Operand::reg_fixed_def(dest, preg));
            }
            VInstruction::Clear(dest) => {
                operands.push_def(dest);
            }
            VInstruction::MovReg(_size, dest, source) => {
                if let VopRCM::Reg(source) = source {
                    return InstInfo::mov(Operand::reg_def(dest), Operand::reg_use(source));
                }

                operands.push_use(source);
                operands.push_def(dest);
            }
            VInstruction::MovMem(_size, dest, source) => {
                operands.push_use(source);
                operands.push_def(dest);
            }
            VInstruction::Lea(dest, base, index, _scale) => {
                operands.push_def(dest);
                operands.push_use(base);
                operands.push_use(index);
            }
            VInstruction::Binary(_size, _instr, dest, left, right) => {
                operands.push(Operand::reg_reuse_def(dest, 1));
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Mul(_size, result_high, result_low, left, right) => {
                operands.push(Operand::reg_fixed_use(left, PREG_A));
                operands.push_use(right);
                operands.push(Operand::reg_fixed_def(result_high, PREG_D));
                operands.push(Operand::reg_fixed_def(result_low, PREG_A));
            }
            VInstruction::DivMod(_size, _signed, high, low, div, quot, rem) => {
                operands.push(Operand::reg_fixed_use(high, PREG_D));
                operands.push(Operand::reg_fixed_use(low, PREG_A));
                operands.push_use(div);
                operands.push(Operand::reg_fixed_def(quot, PREG_A));
                operands.push(Operand::reg_fixed_def(rem, PREG_D));
            }
            VInstruction::Extend(_signed, _size_after, _size_before, after, before) => {
                operands.push_def(after);
                operands.push_use(before);
            }
            VInstruction::Call(result, target, ref args) => {
                for (index, &arg) in args.iter().enumerate() {
                    let preg = ABI_PARAM_REGS[index];
                    operands.push(Operand::reg_fixed_use(arg, preg));
                }
                operands.push_use(target);
                operands.push(Operand::reg_fixed_def(result, ABI_RETURN_REG));
            }
            VInstruction::Cmp(_size, left, right) | VInstruction::Test(_size, left, right) => {
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Setcc(_instr, dest, src) => {
                // setcc doesn't modify the upper bits of the register, so just adding a def is not enough
                operands.push(Operand::reg_reuse_def(dest, 1));

                // in x86 we can only use the first 4 registers for setcc
                // regalloc2 only supports either all regs or a single one, so we have to pick the latter
                // TODO remove this limitation once we switch to x64
                operands.push(Operand::reg_fixed_use(src, PREG_A));
            }

            VInstruction::Jump(ref target) => {
                return InstInfo::branch(operands, vec![target.args.clone()]);
            }
            VInstruction::Branch(cond, ref true_target, ref false_target) => {
                operands.push_use(cond);
                let params = vec![true_target.args.clone(), false_target.args.clone()];
                return InstInfo::branch(operands, params);
            }
            VInstruction::ReturnAndStackFree(value) => {
                if let Some(value) = value {
                    operands.push(Operand::reg_fixed_use(value, ABI_RETURN_REG));
                }
                return InstInfo::ret(operands);
            }
            VInstruction::Unreachable => {
                return InstInfo::ret(operands);
            }
            VInstruction::LoopForever(_label) => {
                return InstInfo::ret(operands);
            }
            VInstruction::StackAlloc => {}
            VInstruction::SlotPtr(dest, _index) => {
                operands.push_def(dest);
            }
        }

        InstInfo::simple(operands)
    }

    pub fn to_asm(&self, ctx: &AsmContext) -> String {
        match *self {
            VInstruction::DefAnyReg(dest) =>
                format!("; def any {}", dest.to_asm(ctx, Size::FULL)),
            VInstruction::DefFixedReg(dest, preg) => {
                assert!(ctx.map_reg(dest).is_preg(preg));
                format!("; def fixed {}", dest.to_asm(ctx, Size::FULL))
            }
            VInstruction::Clear(dest) => {
                let dest = dest.to_asm(ctx, Size::FULL);
                format!("xor {}, {}", dest, dest)
            }
            VInstruction::MovReg(size, dest, source) => {
                let dest = dest.to_asm(ctx, size);
                if source.is_const_zero() {
                    format!("xor {}, {}", dest, dest)
                } else {
                    format!("mov {}, {}", dest, source.to_asm(ctx, size))
                }
            }
            VInstruction::MovMem(size, dest, source) => {
                let dest_str = dest.to_asm(ctx, size);
                let source_str = source.to_asm(ctx, size);

                if let VopRC::Reg(_) = source {
                    format!("mov {}, {}", dest_str, source_str)
                } else {
                    format!("mov {} {}, {}", size.keyword(), dest_str, source_str)
                }
            }
            VInstruction::Lea(dest, base, index, scale) => {
                let dest = dest.to_asm(ctx, Size::FULL);
                let base = base.to_asm(ctx, Size::FULL);
                let index = index.to_asm(ctx, Size::FULL);
                let scale = scale.bytes();

                if scale == 1 {
                    format!("lea {dest}, [{base} + {index}]")
                } else {
                    format!("lea {dest}, [{base} + {index} * {scale}]")
                }
            }
            VInstruction::Binary(size, instr, dest, left, right) => {
                assert_eq!(ctx.map_reg(dest), ctx.map_reg(left));
                format!("{} {}, {}", instr, left.to_asm(ctx, size), right.to_asm(ctx, size))
            }
            VInstruction::Mul(size, result_high, result_low, left, right) => {
                assert!(size != Size::S8);
                assert!(ctx.map_reg(result_high).is_preg(PREG_D));
                assert!(ctx.map_reg(result_low).is_preg(PREG_A));
                assert!(ctx.map_reg(left).is_preg(PREG_A));

                if let VopRM::Reg(_) = right {
                    format!("mul {}", right.to_asm(ctx, size))
                } else {
                    format!("mul {} {}", size.keyword(), right.to_asm(ctx, size))
                }
            }
            VInstruction::DivMod(size, signed, high, low, div, quot, rem) => {
                assert!(size != Size::S8);
                assert!(ctx.map_reg(high).is_preg(PREG_D));
                assert!(ctx.map_reg(low).is_preg(PREG_A));
                assert!(ctx.map_reg(quot).is_preg(PREG_A));
                assert!(ctx.map_reg(rem).is_preg(PREG_D));

                let instr = match signed {
                    Signed::Signed => "idiv",
                    Signed::Unsigned => "div",
                };

                let div_str = div.to_asm(ctx, size);
                if let VopRM::Reg(_) = div {
                    format!("{} {}", instr, div_str)
                } else {
                    format!("{} {} {}", instr, size.keyword(), div_str)
                }
            }
            VInstruction::Extend(signed, size_after, size_before, after, before) => {
                let instr = match signed {
                    Signed::Signed => "movsx",
                    Signed::Unsigned => "movzx",
                };
                format!("{} {}, {}", instr, after.to_asm(ctx, size_after), before.to_asm(ctx, size_before))
            }
            VInstruction::Call(_result, target, ref _args) => {
                format!("call {}", target.to_asm(ctx, Size::FULL))
            }
            VInstruction::Cmp(size, left, right) =>
                format!("cmp {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Test(size, left, right) =>
                format!("test {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Setcc(instr, dest, source) => {
                assert_eq!(ctx.map_reg(dest), ctx.map_reg(source));
                let preg = ctx.map_reg(dest).as_preg().unwrap();
                format!("{} {}", instr, preg_to_asm(preg, Size::S8))
            }
            VInstruction::Jump(ref target) =>
                format!("jmp {}", VSymbol::Block(target.block).to_asm(ctx)),
            VInstruction::Branch(cond, ref true_target, ref false_target) => {
                let cond = cond.to_asm(ctx, Size::FULL);

                let mut s = String::new();
                let f = &mut s;
                writeln!(f, "test {}, {}", cond, cond).unwrap();
                writeln!(f, "jnz {}", VSymbol::Block(true_target.block).to_asm(ctx)).unwrap();
                writeln!(f, "jmp {}", VSymbol::Block(false_target.block).to_asm(ctx)).unwrap();

                s
            }
            VInstruction::ReturnAndStackFree(_value) => {
                let bytes = ctx.stack_layout.free_bytes();
                if bytes != 0 {
                    format!("add esp, {}\nret 0", bytes)
                } else {
                    "ret 0".to_owned()
                }
            }
            VInstruction::Unreachable => "hlt".to_string(),
            VInstruction::LoopForever(label) => {
                format!("{}: jmp {}", label.to_asm(ctx), label.to_asm(ctx))
            }
            VInstruction::StackAlloc => {
                let bytes = ctx.stack_layout.alloc_bytes();
                if bytes != 0 {
                    format!("sub esp, {}", bytes)
                } else {
                    "".to_owned()
                }
            }
            VInstruction::SlotPtr(dest, index) => {
                let dest = ctx.map_reg(dest).to_asm(Size::FULL);
                let offset = ctx.stack_layout.slot_offset(index);

                if offset == 0 {
                    format!("mov {}, esp", dest)
                } else {
                    format!("lea {}, [esp+{}]", dest, offset)
                }
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

impl VSymbol {
    pub fn to_asm(&self, ctx: &AsmContext) -> String {
        match *self {
            VSymbol::Global(global) => match global {
                Global::Func(func) => format!("func_{}", func.index()),
                Global::Extern(ext) => ctx.prog.get_ext(ext).name.clone(),
                Global::Data(data) => format!("data_{}", data.index()),
            }
            VSymbol::Block(block) => format!("block_{}", block.index()),
            VSymbol::Label(index) => format!("label_{}", index),
        }
    }
}
