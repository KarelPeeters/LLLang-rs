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
    TargetArg {
        kind: TargetKind,
        index: usize,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BlockUsage {
    FuncEntry(Function),
    Target {
        pos: BlockPos,
        kind: TargetKind,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TargetKind {
    Jump,
    BranchTrue,
    BranchFalse,
}

impl TargetKind {
    pub fn get_target(self, term: &Terminator) -> &Target {
        match self {
            TargetKind::Jump => unwrap_match!(term, Terminator::Jump { target } => target),
            TargetKind::BranchTrue => unwrap_match!(term, Terminator::Branch { true_target, .. } => true_target),
            TargetKind::BranchFalse => unwrap_match!(term, Terminator::Branch { false_target, .. } => false_target),
        }
    }

    pub fn get_target_mut(self, term: &mut Terminator) -> &mut Target {
        match self {
            TargetKind::Jump => unwrap_match!(term, Terminator::Jump { target } => target),
            TargetKind::BranchTrue => unwrap_match!(term, Terminator::Branch { true_target, .. } => true_target),
            TargetKind::BranchFalse => unwrap_match!(term, Terminator::Branch { false_target, .. } => false_target),
        }
    }
}

// TODO is this only ever used for terminators? If so, rename and implement `as_dom_pos`.
// TODO move all of these pos structs to some common module
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

pub enum TermUsage {
    Value(Value, TermOperand),
    Block(Block, TargetKind),
}

pub fn for_each_usage_in_term(
    term: &Terminator,
    mut f: impl FnMut(TermUsage),
) {
    try_for_each_usage_in_term::<()>(
        term,
        |usage| {
            f(usage);
            Ok(())
        },
    ).unwrap();
}

pub fn try_for_each_usage_in_term<E>(
    terminator: &Terminator,
    mut f: impl FnMut(TermUsage) -> Result<(), E>,
) -> Result<(), E> {
    fn visit_target<E>(f: &mut impl FnMut(TermUsage) -> Result<(), E>, target: &Target, kind: TargetKind) -> Result<(), E> {
        let &Target { block, ref args } = target;
        f(TermUsage::Block(block, kind))?;
        for (index, &value) in args.iter().enumerate() {
            f(TermUsage::Value(value, TermOperand::TargetArg { kind, index }))?;
        }
        Ok(())
    }

    match *terminator {
        Terminator::Jump { ref target } => {
            visit_target(&mut f, target, TargetKind::Jump)?;
        }
        Terminator::Branch { cond, ref true_target, ref false_target } => {
            f(TermUsage::Value(cond, TermOperand::BranchCond))?;
            visit_target(&mut f, true_target, TargetKind::BranchTrue)?;
            visit_target(&mut f, false_target, TargetKind::BranchFalse)?;
        }
        Terminator::Return { value } => {
            f(TermUsage::Value(value, TermOperand::ReturnValue))?;
        }
        Terminator::Unreachable => {}
        Terminator::LoopForever => {}
    }
    Ok(())
}

/// Visit all values used as part of the expression tree starting from `expr`.
/// `expr` itself is not visited.
///
/// The parameters of `f` are `(value, parent, operand)`, where `value` is used as `operand` in `parent`.
pub fn try_for_each_expr_tree_operand<E, F: FnMut(Value, Expression, ExprOperand) -> Result<(), E>>(prog: &Program, expr: Expression, mut f: F) -> Result<(), E> {
    // inner function to deal with getting an "&mut F" without a recursive type
    fn inner_impl<E, F: FnMut(Value, Expression, ExprOperand) -> Result<(), E>>(prog: &Program, expr: Expression, f: &mut F) -> Result<(), E> {
        try_for_each_usage_in_expr(prog.get_expr(expr), |value, usage| {
            match value {
                Value::Immediate(_) | Value::Global(_) | Value::Scoped(_) => f(value, expr, usage),
                Value::Expr(inner) => {
                    f(value, expr, usage)?;
                    inner_impl(prog, inner, f)
                },
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
        }
    }
}

impl BlockUsage {
    pub fn get_field(self, prog: &mut Program) -> &mut Block {
        match self {
            BlockUsage::FuncEntry(func) => &mut prog.get_func_mut(func).entry,
            BlockUsage::Target { pos, kind } => {
                let term = &mut prog.get_block_mut(pos.block).terminator;
                &mut kind.get_target_mut(term).block
            }
        }
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
