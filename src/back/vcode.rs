use std::cmp::min_by_key;
use std::collections::HashMap;
use std::fmt::Write;

use derive_more::From;
use indexmap::IndexMap;
use regalloc2::{Allocation, AllocationKind, Operand, PReg, PRegSet, RegClass, VReg};

use crate::back::layout::Layout;
use crate::back::register::{Register, RSize};
use crate::back::selector::StackPosition;
use crate::mid::ir::{Block, Global, Instruction, Parameter, Program, Signed, StackSlot};
use crate::mid::util::bit_int::BitInt;
use crate::util::arena::IndexType;

// TODO find proper names for these instructions, especially "binary" sucks
#[derive(Debug)]
pub enum VInstruction {
    /// Mark the given register as defined.
    DefAnyReg(VReg),
    /// Mark the given register as defined.
    DefFixedReg(VReg, Register),

    /// Set the given register to zero.
    Clear(VReg),

    /// `dest = src`
    MovReg { size: RSize, dest: VReg, src: VopRCM },
    /// `dest = src`
    MovMem { size: RSize, dest: VMem, src: VopRC },

    /// `dest = src`
    MovLarge {
        layout: Layout,
        dest: VopLarge,
        src: VopLarge,
        tmp: VReg,
    },

    /// `dest = base + index * size`
    Lea { dest: VReg, base: VopRC, index: VReg, size: RSize },

    // TODO replace this instruction with an inline operand that can be used in load/store
    /// `dest = eval(pos)`
    StackPtr { dest: VReg, pos: StackPosition },

    /// `dest = op(left, right)`
    /// `left` and `right` must be the same physical register, this this handled via an operand constraint
    Binary { size: RSize, op: &'static str, dest: VReg, left: VReg, right: VopRCM },

    /// `[dest_high, dest_low] = left * right`
    Mul {
        size: RSize,
        dest_high: VReg,
        dest_low: VReg,
        left: VReg,
        right: VopRM,
    },
    /// ```text
    /// dest_quot = [left_high, left_low] / div
    /// dest_rem  = [left_high, left_low] % div
    /// ```
    DivMod {
        size: RSize,
        signed: Signed,
        left_high: VReg,
        left_low: VReg,
        right: VopRM,
        dest_quot: VReg,
        dest_rem: VReg,
    },

    Extend {
        signed: Signed,
        size_after: RSize,
        size_before: RSize,
        dest: VReg,
        src: VReg,
    },

    Call {
        target: VopRCM,
        result: Option<(VReg, Register)>,
        reg_args: Vec<(VReg, Register)>,
        clobbers: PRegSet,
    },

    /// `flags = cmp(left, right)`
    Cmp { size: RSize, left: VReg, right: VopRCM },
    /// `flags = test(left, right)`
    Test { size: RSize, left: VReg, right: VopRCM },

    // TODO allow mem operand here
    /// `dest = cc(flags)`, but the upper bits of `dest` are kept from `dest_before`
    Setcc { cc: &'static str, dest: VReg, dest_before: VReg },

    // terminators
    // TODO insert moves for phis somewhere?
    //   for jumps right before the jump, for branches right at the start of each target?
    //   ... yikes
    Jump { target: VTarget },
    // TODO make sure we end up generating good branch code
    Branch { cond: VReg, true_target: VTarget, false_target: VTarget },
    ReturnAndStackFree { value: Option<(VReg, Register)> },
    Unreachable,
    LoopForever { label: VSymbol },

    /// allocate the stack at the function entry
    StackAlloc,
}

pub enum RegOperand {
    Adaptive(VReg),
    Use(VReg),
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopLarge {
    Undef,
    Stack(StackPosition),
    Mem(VMem),
}

impl VOperand for VopLarge {
    fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
        match self {
            VopLarge::Undef => {}
            VopLarge::Stack(_) => {}
            VopLarge::Mem(mem) => mem.for_each_reg(f),
        }
    }
}

#[derive(Debug)]
struct VopLargeUndef;

struct StackOffset(pub u32);

impl StackOffset {
    fn to_asm(&self) -> String {
        let offset = self.0;
        if offset == 0 {
            "[esp]".to_string()
        } else {
            format!("[esp + {}]", offset)
        }
    }
}

impl VopLarge {
    fn is_undef(&self) -> bool {
        matches!(self, VopLarge::Undef)
    }

    fn to_asm_offset(self, ctx: &AsmContext, offset: u32) -> Result<String, VopLargeUndef> {
        match self {
            VopLarge::Undef => Err(VopLargeUndef),
            VopLarge::Stack(position) => {
                let base = position.to_offset(ctx);
                // TODO stronger that check that uses the size of this value instead of only the stack pos?
                assert!(base >= offset, "Offset out of bounds");
                let total = base - offset;
                Ok(StackOffset(total).to_asm())
            }
            VopLarge::Mem(mem) => {
                let mem_offset = VMem::at_offset(mem.reg, mem.offset + offset as isize);
                Ok(mem_offset.to_asm_unsized(ctx))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, From)]
pub enum VopRCM {
    Undef,
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

    fn to_asm_unsized(self, ctx: &AsmContext) -> String {
        let VMem { reg, offset } = self;

        // pointer are full-sized, not the result size
        let reg = reg.to_asm(ctx, RSize::FULL);
        if offset == 0 {
            format!("[{}]", reg)
        } else {
            format!("[{}{:+}]", reg, offset)
        }
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
}

impl VOperand for VMem {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match self.reg {
            VPReg::V(reg) => f(RegOperand::Use(reg)),
            VPReg::P(_) => {}
        }
    }
}

impl VOperandExt for VMem {
    fn to_asm(&self, ctx: &AsmContext, _: RSize) -> String {
        self.to_asm_unsized(ctx)
    }

    fn is_const_zero(&self) -> bool {
        false
    }
}

impl VOperand for VopRCM {
    fn for_each_reg(&self, mut f: impl FnMut(RegOperand)) {
        match *self {
            VopRCM::Undef => {}
            VopRCM::Reg(reg) => f(RegOperand::Adaptive(reg)),
            VopRCM::Const(_) => {}
            VopRCM::Mem(mem) => mem.for_each_reg(f)
        }
    }
}

impl VOperandExt for VopRCM {
    fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String {
        match *self {
            VopRCM::Undef => {
                // TODO this only works because all Vops accept a register, which is kind of brittle
                Register::A.to_symbol(size).to_string()
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

// TODO merge with VOperand again?
pub trait VOperandExt {
    fn to_asm(&self, ctx: &AsmContext, size: RSize) -> String;
    fn is_const_zero(&self) -> bool;
}

macro_rules! impl_vop_for {
    ($vop:ty) => {
        impl VOperand for $vop {
            fn for_each_reg(&self, f: impl FnMut(RegOperand)) {
                VopRCM::from(*self).for_each_reg(f)
            }
        }
        impl VOperandExt for $vop {
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
pub struct AsmContext<'p> {
    pub prog: &'p Program,
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
    /// allocated at the entry of the function.
    pub alloc_bytes: u32,
    /// freed just before returning from the function
    pub free_bytes: u32,

    pub slot_offsets: HashMap<StackSlot, u32>,
    pub param_offsets: HashMap<Parameter, u32>,
    pub instr_offsets: HashMap<Instruction, u32>,

    // TODO call and return offsets, per calling conv
}

impl VInstruction {
    pub fn to_inst_info(&self) -> InstInfo {
        let mut operands = Operands::default();

        match *self {
            VInstruction::DefAnyReg(dest) => {
                operands.push_def(dest);
            }
            VInstruction::DefFixedReg(dest, dest_reg) => {
                operands.push_fixed_def(dest, dest_reg);
            }
            VInstruction::Clear(dest) => {
                operands.push_def(dest);
            }

            VInstruction::MovReg { size: _, dest, src } => {
                if let VopRCM::Reg(src) = src {
                    return InstInfo::mov(Operand::reg_def(dest), Operand::reg_use(src));
                }

                operands.push_use(src);
                operands.push_def(dest);
            }
            VInstruction::MovMem { size: _, dest, src } => {
                operands.push_use(src);
                operands.push_def(dest);
            }

            VInstruction::MovLarge { layout: _, dest, src, tmp } => {
                // TODO add better way to skip useless instructions
                if !dest.is_undef() && !src.is_undef() {
                    operands.push_def(dest);
                    operands.push_use(src);
                    operands.push(Operand::reg_temp(tmp));
                }
            }

            VInstruction::Lea { dest, base, index, size: _scale } => {
                operands.push_def(dest);
                operands.push_use(base);
                operands.push_use(index);
            }
            VInstruction::StackPtr { dest, pos: _ } => {
                operands.push_def(dest);
            }

            VInstruction::Binary { size: _size, op: _instr, dest, left, right } => {
                operands.push(Operand::reg_reuse_def(dest, 1));
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Mul { size: _size, dest_high: result_high, dest_low: result_low, left, right } => {
                operands.push_fixed_use(left, Register::A);
                operands.push_use(right);
                operands.push_fixed_def(result_high, Register::D);
                operands.push_fixed_def(result_low, Register::A);
            }
            VInstruction::DivMod { size: _size, signed: _signed, left_high: high, left_low: low, right: div, dest_quot: quot, dest_rem: rem } => {
                operands.push_fixed_use(high, Register::D);
                operands.push_fixed_use(low, Register::A);
                operands.push_use(div);
                operands.push_fixed_def(quot, Register::A);
                operands.push_fixed_def(rem, Register::D);
            }
            VInstruction::Extend { signed: _signed, size_after: _size_after, size_before: _size_before, dest: after, src: before } => {
                operands.push_def(after);
                operands.push_use(before);
            }

            VInstruction::Call { target, result, ref reg_args, clobbers } => {
                operands.push_use(target);
                for &(arg, arg_reg) in reg_args {
                    operands.push_fixed_use(arg, arg_reg);
                }
                if let Some((result, result_reg)) = result {
                    operands.push_fixed_def(result, result_reg);
                }
                operands.clobbers.union_from(clobbers);
            }

            VInstruction::Cmp { size: _, left, right } | VInstruction::Test { size: _, left, right } => {
                operands.push_use(left);
                operands.push_use(right);
            }
            VInstruction::Setcc { cc: _instr, dest, dest_before } => {
                // setcc doesn't modify the upper bits of the register, so just adding a def is not enough
                //   (mostly we can't clobber between the preceding clear and this instruction)
                operands.push(Operand::reg_reuse_def(dest, 1));
                operands.push_use(dest_before);
            }

            VInstruction::Jump { ref target } => {
                return InstInfo::branch(operands, vec![target.args.clone()]);
            }
            VInstruction::Branch { cond, ref true_target, ref false_target } => {
                operands.push_use(cond);
                let params = vec![true_target.args.clone(), false_target.args.clone()];
                return InstInfo::branch(operands, params);
            }
            VInstruction::ReturnAndStackFree { value } => {
                if let Some((value, value_reg)) = value {
                    operands.push_fixed_use(value, value_reg);
                }
                return InstInfo::ret(operands);
            }
            VInstruction::Unreachable => {
                return InstInfo::ret(operands);
            }
            VInstruction::LoopForever { label: _label } => {
                return InstInfo::ret(operands);
            }

            VInstruction::StackAlloc => {}
        }

        InstInfo::simple(operands)
    }

    pub fn to_asm(&self, ctx: &AsmContext) -> String {
        match *self {
            VInstruction::DefAnyReg(dest) =>
                format!("; def any {}", dest.to_asm(ctx, RSize::FULL)),
            VInstruction::DefFixedReg(dest, dest_reg) => {
                assert!(ctx.map_reg(dest).is_reg(dest_reg));
                format!("; def fixed {}", dest.to_asm(ctx, RSize::FULL))
            }
            VInstruction::Clear(dest) => {
                let dest = dest.to_asm(ctx, RSize::FULL);
                format!("xor {}, {}", dest, dest)
            }
            VInstruction::MovReg { size, dest, src } => {
                // TODO always zero- or sign-extend?
                let dest = dest.to_asm(ctx, size);
                if src.is_const_zero() {
                    format!("xor {}, {}", dest, dest)
                } else {
                    format!("mov {}, {}", dest, src.to_asm(ctx, size))
                }
            }
            VInstruction::MovMem { size, dest, src } => {
                let dest_str = dest.to_asm(ctx, size);
                let source_str = src.to_asm(ctx, size);

                if let VopRC::Reg(_) = src {
                    format!("mov {}, {}", dest_str, source_str)
                } else {
                    format!("mov {} {}, {}", size.keyword(), dest_str, source_str)
                }
            }
            VInstruction::MovLarge { layout, dest, src, tmp } => {
                // TODO add better way to skip useless instructions
                if dest.is_undef() || src.is_undef() {
                    return "".to_owned();
                }

                let mut bytes_left = layout.size_bytes;
                let mut result = String::new();

                for &size in RSize::ALL_DECREASING {
                    while bytes_left >= size.bytes() {
                        let offset = layout.size_bytes - bytes_left;
                        bytes_left -= size.bytes();

                        let dest_str = dest.to_asm_offset(ctx, offset).unwrap();
                        let src_str = src.to_asm_offset(ctx, offset).unwrap();
                        let tmp_str = tmp.to_asm(ctx, size);

                        write!(&mut result, "mov {}, {}\nmov {}, {}", tmp_str, src_str, dest_str, tmp_str).unwrap();
                    }
                }

                assert!(bytes_left == 0);
                result
            }
            VInstruction::Lea { dest, base, index, size: scale } => {
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
            VInstruction::StackPtr { dest, pos } => {
                let dest = dest.to_asm(ctx, RSize::FULL);
                let sp_str = Register::SP.to_symbol(RSize::FULL);
                let offset = pos.to_offset(ctx);

                if offset == 0 {
                    format!("mov {dest}, {sp_str}")
                } else {
                    format!("lea {dest}, [{sp_str} + {offset}]")
                }
            }
            VInstruction::Binary { size, op: instr, dest, left, right } => {
                assert_eq!(ctx.map_reg(dest), ctx.map_reg(left));
                format!("{} {}, {}", instr, left.to_asm(ctx, size), right.to_asm(ctx, size))
            }
            VInstruction::Mul { size, dest_high, dest_low, left, right } => {
                assert!(size != RSize::S8);
                assert!(ctx.map_reg(dest_high).is_reg(Register::D));
                assert!(ctx.map_reg(dest_low).is_reg(Register::A));
                assert!(ctx.map_reg(left).is_reg(Register::A));

                if let VopRM::Reg(_) = right {
                    format!("mul {}", right.to_asm(ctx, size))
                } else {
                    format!("mul {} {}", size.keyword(), right.to_asm(ctx, size))
                }
            }
            VInstruction::DivMod { size, signed, left_high, left_low, right, dest_quot, dest_rem } => {
                assert!(size != RSize::S8);
                assert!(ctx.map_reg(left_high).is_reg(Register::D));
                assert!(ctx.map_reg(left_low).is_reg(Register::A));
                assert!(ctx.map_reg(dest_quot).is_reg(Register::A));
                assert!(ctx.map_reg(dest_rem).is_reg(Register::D));

                let instr = match signed {
                    Signed::Signed => "idiv",
                    Signed::Unsigned => "div",
                };

                let div_str = right.to_asm(ctx, size);
                if let VopRM::Reg(_) = right {
                    format!("{} {}", instr, div_str)
                } else {
                    format!("{} {} {}", instr, size.keyword(), div_str)
                }
            }
            VInstruction::Extend { signed, size_after, size_before, dest, src } => {
                let instr = match signed {
                    Signed::Signed => "movsx",
                    Signed::Unsigned => "movzx",
                };
                format!("{} {}, {}", instr, dest.to_asm(ctx, size_after), src.to_asm(ctx, size_before))
            }
            VInstruction::Call { target, result: _, reg_args: _, clobbers: _ } => {
                format!("call {}", target.to_asm(ctx, RSize::FULL))
            }
            VInstruction::Cmp { size, left, right } =>
                format!("cmp {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Test { size, left, right } =>
                format!("test {}, {}", left.to_asm(ctx, size), right.to_asm(ctx, size)),
            VInstruction::Setcc { cc: instr, dest, dest_before } => {
                let dest = ctx.map_reg(dest);
                assert_eq!(dest, ctx.map_reg(dest_before));
                format!("{} {}", instr, dest.to_asm(RSize::S8))
            }
            VInstruction::Jump { ref target } =>
                format!("jmp {}", VSymbol::Block(target.block).to_asm(ctx)),
            VInstruction::Branch { cond, ref true_target, ref false_target } => {
                let cond = cond.to_asm(ctx, RSize::FULL);

                let mut s = String::new();
                let f = &mut s;
                writeln!(f, "test {}, {}", cond, cond).unwrap();
                writeln!(f, "jnz {}", VSymbol::Block(true_target.block).to_asm(ctx)).unwrap();
                writeln!(f, "jmp {}", VSymbol::Block(false_target.block).to_asm(ctx)).unwrap();

                s
            }
            VInstruction::ReturnAndStackFree { value: _value } => {
                let bytes = ctx.stack_layout.free_bytes;
                if bytes != 0 {
                    format!("add rsp, {}\nret 0", bytes)
                } else {
                    "ret 0".to_owned()
                }
            }
            VInstruction::Unreachable => "hlt".to_string(),
            VInstruction::LoopForever { label } => {
                format!("{}: jmp {}", label.to_asm(ctx), label.to_asm(ctx))
            }
            VInstruction::StackAlloc => {
                let bytes = ctx.stack_layout.alloc_bytes;
                if bytes != 0 {
                    format!("sub rsp, {}", bytes)
                } else {
                    "".to_owned()
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
