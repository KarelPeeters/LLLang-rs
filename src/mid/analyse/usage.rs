use std::collections::{HashSet, VecDeque};
use std::ops::ControlFlow;

use crate::mid::analyse::dom_info::{DomPosition, InBlockPos};
use crate::mid::ir::{AffineLoopInfo, Block, Expression, ExpressionInfo, Function, Instruction, InstructionInfo, Program, Target, Terminator, Type, Value, ValueRange};
use crate::util::internal_iter::InternalIterator;

#[derive(Debug, Clone, Eq, PartialEq)]
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum InstrOperand {
    LoadAddr,
    StoreAddr,
    StoreValue,

    CallTarget,
    CallArgument(usize),

    BlackHoleValue,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ExprOperand {
    BinaryOperandLeft,
    BinaryOperandRight,

    TupleFieldPtrBase,
    PointerOffSetBase,
    PointerOffSetIndex,

    CastValue,
    ObscureValue,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TermOperand {
    BranchCond,
    ReturnValue,
    AffineRange(AffineRangeKind),
    TargetArg {
        kind: TargetKind,
        index: usize,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AffineRangeKind {
    Start,
    End,
    Step,
}

#[derive(Debug, Copy, Clone)]
pub enum TermUsage<V, B> {
    Value(V, TermOperand),
    BlockTarget(B, TargetKind),
    BlockAffineBody(B),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BlockUsage {
    FuncEntry(Function),
    Target {
        pos: BlockPos,
        kind: TargetKind,
    },
    AffineBody {
        pos: BlockPos,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TargetKind {
    Jump,
    BranchTrue,
    BranchFalse,
    AffineExit,
}

impl TargetKind {
    pub fn get_target(self, term: &Terminator) -> &Target {
        match self {
            TargetKind::Jump => unwrap_match!(term, Terminator::Jump { target } => target),
            TargetKind::BranchTrue => unwrap_match!(term, Terminator::Branch { true_target, .. } => true_target),
            TargetKind::BranchFalse => unwrap_match!(term, Terminator::Branch { false_target, .. } => false_target),
            TargetKind::AffineExit => unwrap_match!(term, Terminator::AffineLoop(AffineLoopInfo{ exit, .. }) => exit),
        }
    }

    pub fn get_target_mut(self, term: &mut Terminator) -> &mut Target {
        match self {
            TargetKind::Jump => unwrap_match!(term, Terminator::Jump { target } => target),
            TargetKind::BranchTrue => unwrap_match!(term, Terminator::Branch { true_target, .. } => true_target),
            TargetKind::BranchFalse => unwrap_match!(term, Terminator::Branch { false_target, .. } => false_target),
            TargetKind::AffineExit => unwrap_match!(term, Terminator::AffineLoop(AffineLoopInfo{ exit, .. }) => exit),
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct InstructionPos {
    pub func: Function,
    pub block: Block,
    pub instr: Instruction,
    pub instr_index: usize,
}

pub struct OperandIterator<T>(T);

pub struct TargetsIterator<T>(T);

impl InstructionInfo {
    pub fn operands(&self) -> OperandIterator<&Self> {
        OperandIterator(self)
    }
}

impl ExpressionInfo {
    pub fn operands(&self) -> OperandIterator<&Self> {
        OperandIterator(self)
    }
}

impl Terminator {
    pub fn operands(&self) -> OperandIterator<&Self> {
        OperandIterator(self)
    }

    pub fn successors(&self) -> impl InternalIterator<Item=Block> + '_ {
        self.operands().filter_map(|usage| match usage {
            TermUsage::Value(_, _) => None,
            TermUsage::BlockTarget(block, _) => Some(block),
            TermUsage::BlockAffineBody(block) => Some(block),
        })
    }

    pub fn operands_mut(&mut self) -> OperandIterator<&mut Self> {
        OperandIterator(self)
    }

    #[deprecated(note="this has become sketchy in the presence of affine loops")]
    pub fn targets(&self) -> TargetsIterator<&Self> {
        TargetsIterator(self)
    }

    #[deprecated(note="this has become sketchy in the presence of affine loops")]
    pub fn targets_mut(&mut self) -> TargetsIterator<&mut Self> {
        TargetsIterator(self)
    }
}

impl InternalIterator for OperandIterator<&InstructionInfo> {
    type Item = (Value, InstrOperand);

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        match *self.0 {
            InstructionInfo::Load { addr, ty: _ } => {
                f((addr, InstrOperand::LoadAddr))?;
            }
            InstructionInfo::Store { addr, value, ty: _ } => {
                f((addr, InstrOperand::StoreAddr))?;
                f((value, InstrOperand::StoreValue))?;
            }
            InstructionInfo::Call { target, ref args, conv: _ } => {
                f((target, InstrOperand::CallTarget))?;
                for (index, &arg) in args.iter().enumerate() {
                    f((arg, InstrOperand::CallArgument(index)))?;
                }
            }
            InstructionInfo::BlackHole { value } => {
                f((value, InstrOperand::BlackHoleValue))?;
            }
            InstructionInfo::MemBarrier => {}
        }
        ControlFlow::Continue(())
    }
}

impl InternalIterator for OperandIterator<&ExpressionInfo> {
    type Item = (Value, ExprOperand);

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        match *self.0 {
            ExpressionInfo::Arithmetic { kind: _, ty: _, left, right } |
            ExpressionInfo::Comparison { kind: _, left, right } => {
                f((left, ExprOperand::BinaryOperandLeft))?;
                f((right, ExprOperand::BinaryOperandRight))?;
            }
            ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
                f((base, ExprOperand::TupleFieldPtrBase))?;
            }
            ExpressionInfo::PointerOffSet { base, index, ty: _ } => {
                f((base, ExprOperand::PointerOffSetBase))?;
                f((index, ExprOperand::PointerOffSetIndex))?;
            }
            ExpressionInfo::Cast { ty: _, kind: _, value } => {
                f((value, ExprOperand::CastValue))?;
            }
            ExpressionInfo::Obscure { ty: _, value } => {
                f((value, ExprOperand::ObscureValue))?;
            }
        }
        ControlFlow::Continue(())
    }
}

// TODO somehow merge this with the targets iterator
impl InternalIterator for OperandIterator<&Terminator> {
    type Item = TermUsage<Value, Block>;

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        fn visit_target<R>(
            f: &mut impl FnMut(TermUsage<Value, Block>) -> ControlFlow<R>,
            target: &Target,
            kind: TargetKind,
        ) -> ControlFlow<R> {
            let &Target { block, ref args } = target;
            f(TermUsage::BlockTarget(block, kind))?;
            for (index, &value) in args.iter().enumerate() {
                f(TermUsage::Value(value, TermOperand::TargetArg { kind, index }))?;
            }
            ControlFlow::Continue(())
        }

        match *self.0 {
            Terminator::Jump { ref target } => {
                visit_target(&mut f, target, TargetKind::Jump)?;
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                f(TermUsage::Value(cond, TermOperand::BranchCond))?;
                visit_target(&mut f, true_target, TargetKind::BranchTrue)?;
                visit_target(&mut f, false_target, TargetKind::BranchFalse)?;
            }
            Terminator::AffineLoop(ref info) => {
                let AffineLoopInfo { range, body, ref exit } = *info;
                let ValueRange { start, end, step } = range;

                f(TermUsage::Value(start, TermOperand::AffineRange(AffineRangeKind::Start)))?;
                f(TermUsage::Value(end, TermOperand::AffineRange(AffineRangeKind::End)))?;
                f(TermUsage::Value(step, TermOperand::AffineRange(AffineRangeKind::Step)))?;

                f(TermUsage::BlockAffineBody(body))?;
                visit_target(&mut f, exit, TargetKind::AffineExit)?;
            }
            Terminator::Return { value } => {
                f(TermUsage::Value(value, TermOperand::ReturnValue))?;
            }
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }

        ControlFlow::Continue(())
    }
}

impl<'a> InternalIterator for OperandIterator<&'a mut Terminator> {
    type Item = TermUsage<&'a mut Value, &'a mut Block>;

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        fn visit_target<'a, R>(
            f: &mut impl FnMut(TermUsage<&'a mut Value, &'a mut Block>) -> ControlFlow<R>,
            target: &'a mut Target,
            kind: TargetKind,
        ) -> ControlFlow<R> {
            let Target { block, args } = target;
            f(TermUsage::BlockTarget(block, kind))?;
            for (index, value) in args.iter_mut().enumerate() {
                f(TermUsage::Value(value, TermOperand::TargetArg { kind, index }))?;
            }
            ControlFlow::Continue(())
        }

        match self.0 {
            Terminator::Jump { target } => {
                visit_target(&mut f, target, TargetKind::Jump)?;
            }
            Terminator::Branch { cond, true_target, false_target } => {
                f(TermUsage::Value(cond, TermOperand::BranchCond))?;
                visit_target(&mut f, true_target, TargetKind::BranchTrue)?;
                visit_target(&mut f, false_target, TargetKind::BranchFalse)?;
            }
            Terminator::AffineLoop(info) => {
                let AffineLoopInfo { range, body, exit } = info;
                let ValueRange { start, end, step } = range;

                f(TermUsage::Value(start, TermOperand::AffineRange(AffineRangeKind::Start)))?;
                f(TermUsage::Value(end, TermOperand::AffineRange(AffineRangeKind::End)))?;
                f(TermUsage::Value(step, TermOperand::AffineRange(AffineRangeKind::Step)))?;

                f(TermUsage::BlockAffineBody(body))?;
                visit_target(&mut f, exit, TargetKind::AffineExit)?;
            }
            Terminator::Return { value } => {
                f(TermUsage::Value(value, TermOperand::ReturnValue))?;
            }
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }

        ControlFlow::Continue(())
    }
}

impl<'a> InternalIterator for TargetsIterator<&'a Terminator> {
    type Item = (&'a Target, TargetKind);

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        match self.0 {
            Terminator::Jump { target } => f((target, TargetKind::Jump))?,
            Terminator::Branch { cond: _, true_target, false_target } => {
                f((true_target, TargetKind::BranchTrue))?;
                f((false_target, TargetKind::BranchFalse))?;
            }
            Terminator::AffineLoop(info) => {
                let AffineLoopInfo { range: _, body, exit } = info;
                // TODO what to do about the affine body here?
                f((exit, TargetKind::AffineExit))?;
                todo!("handle affine body")
            }
            Terminator::Return { value: _ } => {}
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }
        ControlFlow::Continue(())
    }
}

impl<'a> InternalIterator for TargetsIterator<&'a mut Terminator> {
    type Item = (&'a mut Target, TargetKind);

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        match self.0 {
            Terminator::Jump { target } => f((target, TargetKind::Jump))?,
            Terminator::Branch { cond: _, true_target, false_target } => {
                f((true_target, TargetKind::BranchTrue))?;
                f((false_target, TargetKind::BranchFalse))?;
            }
            Terminator::AffineLoop(info) => {
                let AffineLoopInfo { range: _, body, exit } = info;
                // TODO what to do about the affine body here?
                f((exit, TargetKind::AffineExit))?;
                todo!("handle affine body")
            }
            Terminator::Return { value: _ } => {}
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }
        ControlFlow::Continue(())
    }
}

pub struct ExpressionTreeIterator<'a> {
    prog: &'a Program,
    root: Expression,
}

impl Program {
    /// Visit all values used as part of the expression tree starting from `root`.
    /// `root` itself is not visited.
    ///
    /// The item values are `(value, parent, operand)`, where `value` is used as `operand` in `parent`.
    pub fn expr_tree_iter(&self, root: Expression) -> ExpressionTreeIterator {
        ExpressionTreeIterator { prog: self, root }
    }

    /// The same as [Program::expr_tree_iter] but only yields non-expression leaf values.
    pub fn expr_tree_leaf_iter(&self, root: Expression) -> impl InternalIterator<Item=(Value, Expression, ExprOperand)> + '_ {
        self.expr_tree_iter(root).filter_map(|(value, parent, operand)| {
            if value.is_expr() {
                None
            } else {
                Some((value, parent, operand))
            }
        })
    }
}

impl InternalIterator for ExpressionTreeIterator<'_> {
    type Item = (Value, Expression, ExprOperand);

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        // inner function to deal with getting an "&mut F" without a recursive type
        fn inner_impl<R, F: FnMut((Value, Expression, ExprOperand)) -> ControlFlow<R>>(prog: &Program, expr: Expression, f: &mut F) -> ControlFlow<R> {
            prog.get_expr(expr).operands().try_for_each_impl(|(value, usage)| {
                f((value, expr, usage))?;
                if let Value::Expr(inner) = value {
                    inner_impl(prog, inner, f)?;
                }
                ControlFlow::Continue(())
            })
        }
        inner_impl(self.prog, self.root, &mut f)
    }
}

pub struct ReachableBlocksIterator<'a> {
    prog: &'a Program,
    root: Block,
}

impl Program {
    /// Iterate over all blocks reachable from `root` while following terminators.
    pub fn reachable_blocks(&self, root: Block) -> ReachableBlocksIterator {
        ReachableBlocksIterator { prog: self, root }
    }
}

impl InternalIterator for ReachableBlocksIterator<'_> {
    type Item = Block;

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        let mut seen = HashSet::new();
        let mut todo = VecDeque::new();

        todo.push_back(self.root);

        while let Some(curr) = todo.pop_front() {
            if !seen.insert(curr) { continue; }
            f(curr)?;

            self.prog.get_block(curr).terminator.successors()
                .for_each(|succ| todo.push_back(succ));
        }

        ControlFlow::Continue(())
    }
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

    pub fn is_load_store_addr_get_ty(&self, prog: &Program) -> Option<Type> {
        match self {
            Usage::InstrOperand { pos, usage: InstrOperand::LoadAddr | InstrOperand::StoreAddr } => {
                let ty = unwrap_match!(prog.get_instr(pos.instr), &InstructionInfo::Load { ty, .. } | &InstructionInfo::Store { ty, .. } => ty);
                Some(ty)
            }
            _ => None,
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
