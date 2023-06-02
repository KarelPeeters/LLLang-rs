use std::cmp::min_by_key;
use std::fmt::Write;

use derive_more::From;
use indexmap::IndexMap;
use regalloc2::{Allocation, AllocationKind, Operand, PReg, PRegSet, RegClass, VReg};
use crate::back::abi::{ABI_PARAM_REGS, ABI_RETURN_REG, ABI_VOLATILE_REGS};
use crate::back::layout::next_multiple;

use crate::back::register::{Register, RSize};
use crate::mid::ir::{Block, Global, Program, Signed};
use crate::mid::util::bit_int::BitInt;
use crate::util::arena::IndexType;

// TODO find proper names for these instructions, especially "binary" sucks
#[derive(Debug)]
pub enum VInstruction {
    // utilities for marking registers as defined
    DefAnyReg(VReg),
    DefFixedReg(VReg, Register),

    /// set the given register to zero
    Clear(VReg),

    // TODO remove size from reg<-reg/reg<-const moves?
    //   maybe make size a property of mem instead
    // read as "move into .. from .."
    MovReg(RSize, VReg, VopRCM),
    MovMem(RSize, VMem, VopRC),

    /// target = base + index * size
    Lea(VReg, VopRC, VReg, RSize),

    /// args are "target = left (+) right"
    /// target and left must be the same register, this is handled with a register allocation constraint
    Binary(RSize, &'static str, VReg, VReg, VopRCM),

    /// result_high, result_low, left, right
    Mul(RSize, VReg, VReg, VReg, VopRM),
    /// signed, high, low, div, quot, rem
    DivMod(RSize, Signed, VReg, VReg, VopRM, VReg, VReg),

    /// signed, size after, size before, after, before
    Extend(Signed, RSize, RSize, VReg, VReg),

    /// result, target, args
    Call(VReg, VopRCM, Vec<VReg>),

    // compare instructions
    Cmp(RSize, VReg, VopRCM),
    Test(RSize, VReg, VopRCM),
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
pub enum AllocPos {
    Reg(Register),
    Slot(usize),
}

impl VConst {
    pub fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String {
        match self {
            VConst::Const(value) => {
                let value_bits = if value.bits() == 1 { 64 } else { value.bits() };
                assert_eq!(value_bits, size.bits(), "Tried to store {:?} in {:?}", value, size);

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

impl From<Allocation> for AllocPos {
    fn from(value: Allocation) -> Self {
        match value.kind() {
            AllocationKind::None => unreachable!(),
            AllocationKind::Reg =>
                AllocPos::Reg(Register::from_index(value.as_reg().unwrap().index())),
            AllocationKind::Stack => {
                let slot = value.as_stack().unwrap();
                assert!(slot.is_valid());
                AllocPos::Slot(slot.index())
            }
        }
    }
}

impl AllocPos {
    fn is_reg(self, reg: Register) -> bool {
        self == AllocPos::Reg(reg)
    }

    fn as_reg(self) -> Option<Register> {
        option_match!(self, AllocPos::Reg(preg) => preg)
    }

    pub fn to_asm(self, size: RSize) -> String {
        match self {
            AllocPos::Reg(reg) => reg.to_symbol(size).to_string(),
            // TODO is this really the right expression?
            AllocPos::Slot(index) => format!("[rsp+{}]", 8 * index + 8),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum VSymbol {
    Global(Global),
    Block(Block),
    Label(usize),
}

// TODO replace this with just VReg?
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
    fn to_asm(self, ctx: &AsmContext, size: RSize) -> String {
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
    fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String;
    fn is_const_zero(&self) -> bool;
}

impl VOperand for VMem {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match self.reg {
            VPReg::V(reg) => f(RegOperand::Use(reg)),
            VPReg::P(_) => {}
        }
    }

    fn to_asm(&self, ctx: &AsmContext, _: RSize) -> String {
        let &VMem { reg, offset } = self;

        // pointer are full-sized, not the result size
        let reg = reg.to_asm(ctx, RSize::FULL);
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

    fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String {
        match *self {
            // TODO this only works because all Vops accept a register, which is kind of brittle
            VopRCM::Undef => Register::A.to_symbol(size).to_string(),
            VopRCM::Slot(index) => {
                let offset = ctx.stack_layout.slot_offset(index);
                format!("[rsp+{}]", offset)
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

pub fn preg_to_asm(preg: PReg, size: RSize) -> &'static str {
    let register = Register::from_index(preg.index());
    register.to_symbol(size)
}

macro_rules! impl_vop_for {
    ($vop:ty) => {
        impl VOperand for $vop {
            fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
                VopRCM::from(*self).for_each_reg(f)
            }
            fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String {
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
    pub fn map_reg(&self, reg: VReg) -> AllocPos {
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
                operands.push_fixed_def(dest, preg);
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
                operands.push_fixed_use(left, Register::A);
                operands.push_use(right);
                operands.push_fixed_def(result_high, Register::D);
                operands.push_fixed_def(result_low, Register::A);
            }
            VInstruction::DivMod(_size, _signed, high, low, div, quot, rem) => {
                operands.push_fixed_use(high, Register::D);
                operands.push_fixed_use(low, Register::A);
                operands.push_use(div);
                operands.push_fixed_def(quot, Register::A);
                operands.push_fixed_def(rem, Register::D);
            }
            VInstruction::Extend(_signed, _size_after, _size_before, after, before) => {
                operands.push_def(after);
                operands.push_use(before);
            }
            VInstruction::Call(result, target, ref args) => {
                for (index, &arg) in args.iter().enumerate() {
                    let preg = ABI_PARAM_REGS[index];
                    operands.push_fixed_use(arg, preg);
                }
                operands.push_use(target);
                operands.push_fixed_def(result, ABI_RETURN_REG);

                for &clobber in ABI_VOLATILE_REGS {
                    if clobber != ABI_RETURN_REG {
                        operands.push_clobber(clobber);
                    }
                }
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
                operands.push_fixed_use(src, Register::A);
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
                    operands.push_fixed_use(value, ABI_RETURN_REG);
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
                format!("; def any {}", dest.to_asm(ctx, RSize::FULL)),
            VInstruction::DefFixedReg(dest, preg) => {
                assert!(ctx.map_reg(dest).is_reg(preg));
                format!("; def fixed {}", dest.to_asm(ctx, RSize::FULL))
            }
            VInstruction::Clear(dest) => {
                let dest = dest.to_asm(ctx, RSize::FULL);
                format!("xor {}, {}", dest, dest)
            }
            VInstruction::MovReg(size, dest, source) => {
                // TODO always zero- or sign-extend?
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
                let dest = dest.to_asm(ctx, RSize::FULL);
                let base = base.to_asm(ctx, RSize::FULL);
                let index = index.to_asm(ctx, RSize::FULL);
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
                assert!(size != RSize::S8);
                assert!(ctx.map_reg(result_high).is_reg(Register::D));
                assert!(ctx.map_reg(result_low).is_reg(Register::A));
                assert!(ctx.map_reg(left).is_reg(Register::A));

                if let VopRM::Reg(_) = right {
                    format!("mul {}", right.to_asm(ctx, size))
                } else {
                    format!("mul {} {}", size.keyword(), right.to_asm(ctx, size))
                }
            }
            VInstruction::DivMod(size, signed, high, low, div, quot, rem) => {
                assert!(size != RSize::S8);
                assert!(ctx.map_reg(high).is_reg(Register::D));
                assert!(ctx.map_reg(low).is_reg(Register::A));
                assert!(ctx.map_reg(quot).is_reg(Register::A));
                assert!(ctx.map_reg(rem).is_reg(Register::D));

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
                format!("call {}", target.to_asm(ctx, RSize::FULL))
            }
            VInstruction::Cmp(size, left, right) =>
                format!("cmp {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Test(size, left, right) =>
                format!("test {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Setcc(instr, dest, source) => {
                let dest = ctx.map_reg(dest);
                assert_eq!(dest, ctx.map_reg(source));
                format!("{} {}", instr, dest.to_asm(RSize::S8))
            }
            VInstruction::Jump(ref target) =>
                format!("jmp {}", VSymbol::Block(target.block).to_asm(ctx)),
            VInstruction::Branch(cond, ref true_target, ref false_target) => {
                let cond = cond.to_asm(ctx, RSize::FULL);

                let mut s = String::new();
                let f = &mut s;
                writeln!(f, "test {}, {}", cond, cond).unwrap();
                writeln!(f, "jnz {}", VSymbol::Block(true_target.block).to_asm(ctx)).unwrap();
                writeln!(f, "jmp {}", VSymbol::Block(false_target.block).to_asm(ctx)).unwrap();

                s
            }
            VInstruction::ReturnAndStackFree(_value) => {
                let bytes = ctx.stack_layout.free_bytes();
                let bytes = next_multiple(bytes as u32 + 4*8 + 8, 16) - 8;

                if bytes != 0 {
                    format!("add rsp, {}\nret 0", bytes)
                } else {
                    "ret 0".to_owned()
                }
            }
            VInstruction::Unreachable => "hlt".to_string(),
            VInstruction::LoopForever(label) => {
                format!("{}: jmp {}", label.to_asm(ctx), label.to_asm(ctx))
            }
            VInstruction::StackAlloc => {
                // TODO properly fix this

                let bytes = ctx.stack_layout.alloc_bytes();
                let bytes = next_multiple(bytes as u32 + 4*8 + 8, 16) - 8;

                if bytes != 0 {
                    format!("sub rsp, {}", bytes)
                } else {
                    "".to_owned()
                }
            }
            VInstruction::SlotPtr(dest, index) => {
                let dest = ctx.map_reg(dest).to_asm(RSize::FULL);
                let offset = ctx.stack_layout.slot_offset(index);

                if offset == 0 {
                    format!("mov {}, rsp", dest)
                } else {
                    format!("lea {}, [rsp+{}]", dest, offset)
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

    fn push_fixed_use(&mut self, vreg: VReg, reg: Register) {
        self.push(Operand::reg_fixed_use(vreg, PReg::new(reg.index(), RegClass::Int)))
    }

    fn push_fixed_def(&mut self, vreg: VReg, reg: Register) {
        self.push(Operand::reg_fixed_def(vreg, PReg::new(reg.index(), RegClass::Int)))
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

    fn push_clobber(&mut self, reg: Register) {
        self.clobbers.add(PReg::new(reg.index(), RegClass::Int));
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
