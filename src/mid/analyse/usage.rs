use crate::mid::analyse::dom_info::{DomPosition, InBlockPos};
use crate::mid::ir::{Block, Expression, ExpressionInfo, Function, Instruction, InstructionInfo, Program, Target, Terminator, Value};

#[derive(Debug, Clone)]
pub enum Usage {
    RootFunction(String),
    InstrOperand {
        pos: InstructionPos,
        usage: InstrOperand,
    },
    ExprOperand {
        expr: Expression,
        usage: ExprOperand,
    },
    TermOperand {
        pos: BlockPos,
        usage: TermOperand,
    },
    TargetBlockArg {
        usage: TargetPos,
        index: usize,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum InstrOperand {
    LoadAddr,
    StoreAddr,
    StoreValue,

    CallTarget,
    CallArgument(usize),

    BlackBoxValue,
}

#[derive(Debug, Copy, Clone)]
pub enum ExprOperand {
    BinaryOperandLeft,
    BinaryOperandRight,

    TupleFieldPtrBase,
    PointerOffSetBase,
    PointerOffSetIndex,

    CastValue,
}

#[derive(Debug, Copy, Clone)]
pub enum TermOperand {
    BranchCond,
    ReturnValue,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BlockUsage {
    FuncEntry(Function),
    Target(TargetPos),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct TargetPos {
    pub pos: BlockPos,
    pub kind: TargetKind,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TargetKind {
    Jump,
    BranchTrue,
    BranchFalse,
}

// TODO is this only ever used for terminators? If so, rename and implement `as_dom_pos`.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BlockPos {
    pub func: Function,
    pub block: Block,
}

#[derive(Debug, Copy, Clone)]
pub struct InstructionPos {
    pub func: Function,
    pub block: Block,
    pub instr: Instruction,
    pub instr_index: usize,
}

pub fn for_each_usage_in_instr(instr_info: &InstructionInfo, mut f: impl FnMut(Value, InstrOperand)) {
    try_for_each_usage_in_instr::<()>(instr_info, |value, usage| {
        f(value, usage);
        Ok(())
    }).unwrap();
}

pub fn try_for_each_usage_in_instr<E>(
    instr_info: &InstructionInfo,
    mut f: impl FnMut(Value, InstrOperand) -> Result<(), E>,
) -> Result<(), E> {
    match *instr_info {
        InstructionInfo::Load { addr, ty: _ } => {
            f(addr, InstrOperand::LoadAddr)?;
        }
        InstructionInfo::Store { addr, value, ty: _ } => {
            f(addr, InstrOperand::StoreAddr)?;
            f(value, InstrOperand::StoreValue)?;
        }
        InstructionInfo::Call { target, ref args } => {
            f(target, InstrOperand::CallTarget)?;
            for (index, &arg) in args.iter().enumerate() {
                f(arg, InstrOperand::CallArgument(index))?;
            }
        }
        InstructionInfo::BlackBox { value } => {
            f(value, InstrOperand::BlackBoxValue)?;
        }
    }
    Ok(())
}

pub fn for_each_usage_in_expr(
    expr_info: &ExpressionInfo,
    mut f: impl FnMut(Value, ExprOperand),
) {
    try_for_each_usage_in_expr::<()>(expr_info, |value, usage| {
        f(value, usage);
        Ok(())
    }).unwrap();
}

pub fn try_for_each_usage_in_expr<E>(
    expr_info: &ExpressionInfo,
    mut f: impl FnMut(Value, ExprOperand) -> Result<(), E>,
) -> Result<(), E> {
    match expr_info {
        &ExpressionInfo::Arithmetic { kind: _, left, right } |
        &ExpressionInfo::Comparison { kind: _, left, right } => {
            f(left, ExprOperand::BinaryOperandLeft)?;
            f(right, ExprOperand::BinaryOperandRight)?;
        }
        &ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
            f(base, ExprOperand::TupleFieldPtrBase)?;
        }
        &ExpressionInfo::PointerOffSet { base, index, ty: _ } => {
            f(base, ExprOperand::PointerOffSetBase)?;
            f(index, ExprOperand::PointerOffSetIndex)?;
        }
        &ExpressionInfo::Cast { ty: _, kind: _, value } => {
            f(value, ExprOperand::CastValue)?;
        }
    }
    Ok(())
}

/// Visit all non-expression values used as part of the expression tree starting from `expr`.
pub fn try_for_each_expr_leaf_value<E, F: FnMut(Value) -> Result<(), E>>(prog: &Program, expr: Expression, mut f: F) -> Result<(), E> {
    // inner function to deal with getting an "&mut F" without a recursive type
    fn inner_impl<E, F: FnMut(Value) -> Result<(), E>>(prog: &Program, expr: Expression, f: &mut F) -> Result<(), E> {
        try_for_each_usage_in_expr(prog.get_expr(expr), |value, _| {
            match value {
                Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => f(value),
                Value::Expr(inner) => inner_impl(prog, inner, f),
            }
        })
    }
    inner_impl(prog, expr, &mut f)
}

impl Usage {
    // TODO is this ever actually used?
    pub fn as_dom_pos(&self) -> Result<DomPosition, Expression> {
        match *self {
            Usage::RootFunction(_) => Ok(DomPosition::Global),
            Usage::InstrOperand { pos, usage: _ } => Ok(pos.as_dom_pos()),
            Usage::ExprOperand { expr, usage: _ } => Err(expr),
            Usage::TermOperand { pos, usage: _ } => Ok(pos.as_dom_pos(InBlockPos::Terminator)),
            Usage::TargetBlockArg { usage: target, index: _ } => Ok(target.as_dom_pos()),
        }
    }
}

impl BlockUsage {
    pub fn get_field(self, prog: &mut Program) -> &mut Block {
        match self {
            BlockUsage::FuncEntry(func) => &mut prog.get_func_mut(func).entry,
            BlockUsage::Target(target) => &mut target.get_target_mut(prog).block
        }
    }
}

impl TargetPos {
    pub fn get_target(self, prog: &Program) -> &Target {
        match self.kind {
            TargetKind::Jump =>
                unwrap_match!(&prog.get_block(self.pos.block).terminator, Terminator::Jump { target } => target),
            TargetKind::BranchTrue =>
                unwrap_match!(&prog.get_block(self.pos.block).terminator, Terminator::Branch { true_target, .. } => true_target),
            TargetKind::BranchFalse =>
                unwrap_match!(&prog.get_block(self.pos.block).terminator, Terminator::Branch { false_target, .. } => false_target),
        }
    }

    pub fn get_target_mut(self, prog: &mut Program) -> &mut Target {
        match self.kind {
            TargetKind::Jump => unwrap_match!(
                &mut prog.get_block_mut(self.pos.block).terminator,
                Terminator::Jump { target } => target
            ),
            TargetKind::BranchTrue => unwrap_match!(
                &mut prog.get_block_mut(self.pos.block).terminator,
                Terminator::Branch { true_target, .. } => true_target
            ),
            TargetKind::BranchFalse => unwrap_match!(
                &mut prog.get_block_mut(self.pos.block).terminator,
                Terminator::Branch { false_target, .. } => false_target
            ),
        }
    }

    pub fn as_dom_pos(self) -> DomPosition {
        self.pos.as_dom_pos(InBlockPos::Terminator)
    }
}

impl BlockPos {
    pub fn as_dom_pos(self, block_pos: InBlockPos) -> DomPosition {
        DomPosition::InBlock(self.func, self.block, block_pos)
    }
}

impl InstructionPos {
    pub fn as_dom_pos(self) -> DomPosition {
        DomPosition::InBlock(self.func, self.block, InBlockPos::Instruction(self.instr_index))
    }
}
