use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::zip;

use derive_more::From;

use crate::mid::analyse::dom_info::{DomInfo, DomPosition, InBlockPos};
use crate::mid::analyse::usage::{BlockPos, InstructionPos, TargetKind, TermOperand, Usage};
use crate::mid::ir::{Block, BlockInfo, CallingConvention, Expression, ExpressionInfo, Function, Instruction, InstructionInfo, Program, Scoped, Target, Terminator, Type, TypeInfo, Value};
use crate::util::internal_iter::InternalIterator;

// TODO verify that there are no expression loops
#[derive(Debug)]
pub enum VerifyError {
    ValueDeclaredTwice(Value, DomPosition, DomPosition),
    BlockDeclaredTwice(Block, Function, Function),

    NonDeclaredValueUsed(Scoped, Usage, Option<Expression>),
    NonDominatingValueUsed(Scoped, DomPosition, Usage, Option<Expression>),

    WrongDeclParamCount(Function, TypeString, usize),
    WrongBlockArgCount(DomPosition, Block),

    TypeMismatch(Position, TypeOrValue, TypeOrValue, String, String),
    ExpectedIntegerType(Position, Option<Value>, TypeString),
    ExpectedTupleType(Position, TypeString),
    ExpectedFunctionType(DomPosition, TypeString),

    WrongCallParamCount(DomPosition, TypeString, usize),
    WrongCallingConvention(Value, CallingConvention, DomPosition, CallingConvention),

    TupleIndexOutOfBounds(Expression, TypeString, u32, u32),

    EntryBlockUsedAsTarget(DomPosition, Block),
}

#[derive(Debug, Copy, Clone, From)]
pub enum Position {
    Dom(DomPosition),
    Expr(Expression),
}

type Result<T = ()> = std::result::Result<T, VerifyError>;

pub fn verify(prog: &Program) -> Result {
    let ts = |ty: Type| TypeString::new(prog, ty);

    // check that root functions exist
    for &func in prog.root_functions.values() {
        prog.get_func(func);
    }

    // check for duplicate declarations
    let mut declarer = FuncDeclareChecker::default();
    for (func, func_info) in &prog.nodes.funcs {
        declarer.declare_all(&func_info.slots, DomPosition::FuncEntry(func))?;

        // TODO this way of visiting blocks means we never verify unreachable blocks. Is that okay?
        prog.reachable_blocks(func_info.entry).try_for_each(|block| {
            let BlockInfo { params, instructions, terminator: _, debug_name: _ } = prog.get_block(block);
            let block_pos = BlockPos { func, block };

            declarer.declare_block(func, block)?;
            declarer.declare_all(params, block_pos.as_dom_pos(InBlockPos::Entry))?;

            for (instr_index, &instr) in instructions.iter().enumerate() {
                declarer.declare(instr, block_pos.as_dom_pos(InBlockPos::Instruction(instr_index)))?;
            }

            Ok(())
        })?;
    }

    // check types and value domination
    //   also collect expressions for type checking
    let mut expressions = HashSet::new();

    for (func, func_info) in &prog.nodes.funcs {
        let dom_info = &DomInfo::new(prog, func);
        let func_pos = DomPosition::FuncEntry(func);

        let mut ctx = Context {
            prog,
            declarer: &declarer,
            dom_info,
            expressions: &mut expressions,
        };

        // check function type match
        let expected_func_ty = prog.types.lookup(&TypeInfo::Func(func_info.func_ty.clone()));
        ensure_type_match(prog, func_pos, func_info.ty, expected_func_ty.unwrap())?;

        // check that entry params match the signature
        let func_entry = prog.get_block(func_info.entry);
        if func_info.func_ty.params.len() != func_entry.params.len() {
            return Err(VerifyError::WrongDeclParamCount(func, ts(func_info.ty), func_entry.params.len()));
        }
        for (&param_ty, &param) in zip(&func_info.func_ty.params, &func_entry.params) {
            ensure_type_match(prog, func_pos, param_ty, prog.type_of_value(param.into()))?;
        }

        for &block in dom_info.blocks() {
            let BlockInfo { params: _, instructions, terminator, debug_name: _ } = prog.get_block(block);
            let block_pos = BlockPos { func, block };

            // check instructions
            for (instr_index, &instr) in instructions.iter().enumerate() {
                let instr_info = prog.get_instr(instr);
                let instr_pos = InstructionPos { func, block, instr, instr_index };

                // check instruction types
                check_instr_types(prog, instr, instr_pos.as_dom_pos())?;

                // check instr arg domination
                instr_info.operands().try_for_each(|(value, usage)| {
                    let usage = Usage::InstrOperand { pos: instr_pos, usage };
                    ctx.check_value_usage(value, usage)
                })?;
            }

            // check terminator
            let term_pos = block_pos.as_dom_pos(InBlockPos::Terminator);
            match *terminator {
                Terminator::Jump { ref target } => {
                    ctx.check_target(block_pos, target, TargetKind::Jump)?
                }
                Terminator::Branch { cond, ref true_target, ref false_target } => {
                    ensure_type_match(prog, term_pos, cond, prog.ty_bool())?;
                    let cond_usage = Usage::TermOperand { pos: block_pos, usage: TermOperand::BranchCond };
                    ctx.check_value_usage(cond, cond_usage)?;
                    ctx.check_target(block_pos, true_target, TargetKind::BranchTrue)?;
                    ctx.check_target(block_pos, false_target, TargetKind::BranchFalse)?;
                }
                Terminator::Return { value } => {
                    ensure_type_match(prog, term_pos, value, func_info.func_ty.ret)?;
                    let return_usage = Usage::TermOperand { pos: block_pos, usage: TermOperand::ReturnValue };
                    ctx.check_value_usage(value, return_usage)?;
                }
                Terminator::Unreachable => {}
                Terminator::LoopForever => {}
            }
        }
    }

    // type check expressions recursively
    let mut todo_expressions: VecDeque<_> = expressions.drain().collect();
    let mut expressions_visited = expressions;
    while let Some(expr) = todo_expressions.pop_front() {
        if !expressions_visited.insert(expr) {
            continue;
        }

        let expr_info = prog.get_expr(expr);
        expr_info.operands().filter_map(|(value, _)| value.as_expr()).sink_to(&mut todo_expressions);

        check_expr_types(prog, expr)?;
    }

    Ok(())
}

struct Context<'a> {
    prog: &'a Program,
    declarer: &'a FuncDeclareChecker,
    dom_info: &'a DomInfo,

    expressions: &'a mut HashSet<Expression>,
}

impl<'a> Context<'a> {
    fn check_target(&mut self, block_pos: BlockPos, target: &Target, kind: TargetKind) -> Result {
        let prog = self.prog;
        let pos = block_pos.as_dom_pos(InBlockPos::Terminator);

        // check target block != entry
        // TODO do we really want that? it seems artificially limiting
        //   but it's pretty much necessary to get phi construction to work at all
        if target.block == self.prog.get_func(self.dom_info.func()).entry {
            return Err(VerifyError::EntryBlockUsedAsTarget(pos, target.block));
        }

        // check phi type match
        let target_block_info = prog.get_block(target.block);
        if target_block_info.params.len() != target.args.len() {
            return Err(VerifyError::WrongBlockArgCount(pos, target.block));
        }
        for (&param, &arg) in zip(&target_block_info.params, &target.args) {
            ensure_type_match(prog, pos, prog.get_param(param).ty, arg)?;
        }

        // check phi domination
        for (index, &value) in target.args.iter().enumerate() {
            let usage = Usage::TermOperand { pos: block_pos, usage: TermOperand::TargetArg { kind, index } };
            self.check_value_usage(value, usage)?;
        }
        Ok(())
    }

    fn check_value_usage(&mut self, value: Value, usage: Usage) -> Result {
        self.check_value_usage_impl(value, usage, None)
    }

    fn check_value_usage_impl(&mut self, value: Value, usage: Usage, root: Option<Expression>) -> Result {
        match value {
            Value::Global(_) | Value::Immediate(_) => Ok(()),

            Value::Scoped(value) => {
                // safe to unwrap, we know value is not an expression
                let use_pos = usage.as_dom_pos().unwrap();

                let def_pos = match self.declarer.value_declared_pos.get(&value) {
                    Some(&def_pos) => def_pos,
                    None => return Err(VerifyError::NonDeclaredValueUsed(value, usage, root)),
                };

                if self.dom_info.pos_is_strict_dominator(def_pos, use_pos) {
                    Ok(())
                } else {
                    Err(VerifyError::NonDominatingValueUsed(value, def_pos, usage, root))
                }
            }

            Value::Expr(expr) => {
                assert!(root.is_none());
                self.expressions.insert(expr);

                self.prog.expr_tree_leaf_iter(expr).try_for_each(|(inner, _, _)| {
                    assert!(!inner.is_expr());
                    self.check_value_usage_impl(inner, usage.clone(), Some(expr))
                })
            }
        }
    }
}

fn check_instr_types(prog: &Program, instr: Instruction, pos: DomPosition) -> Result {
    let instr_info = prog.get_instr(instr);
    let ts = |ty: Type| TypeString::new(prog, ty);

    match instr_info {
        &InstructionInfo::Load { addr, ty: _ } => {
            ensure_type_match(prog, pos, prog.type_of_value(addr), prog.ty_ptr())?;
        }
        &InstructionInfo::Store { addr, ty, value } => {
            ensure_type_match(prog, pos, prog.type_of_value(addr), prog.ty_ptr())?;
            ensure_type_match(prog, pos, prog.type_of_value(value), ty)?;
        }
        &InstructionInfo::Call { target, ref args, conv } => {
            let target_ty = prog.type_of_value(target);
            let target_func_ty = prog.get_type(target_ty).unwrap_func()
                .ok_or_else(|| VerifyError::ExpectedFunctionType(pos, ts(target_ty)))?;

            if target_func_ty.params.len() != args.len() {
                return Err(VerifyError::WrongCallParamCount(pos, ts(target_ty), args.len()));
            }

            for (&param, &arg) in zip(&target_func_ty.params, args) {
                ensure_type_match(prog, pos, param, prog.type_of_value(arg))?;
            }

            if conv != target_func_ty.conv {
                return Err(VerifyError::WrongCallingConvention(target, target_func_ty.conv, pos, conv));
            }
        }
        InstructionInfo::BlackBox { value: _ } => {}
    }

    Ok(())
}

fn check_expr_types(prog: &Program, expr: Expression) -> Result {
    let expr_info = prog.get_expr(expr);
    let ts = |ty: Type| TypeString::new(prog, ty);
    let pos = Position::Expr(expr);

    match *expr_info {
        ExpressionInfo::Arithmetic { kind: _, left, right } => {
            ensure_matching_int_values(prog, pos, left, right)?;
        }
        ExpressionInfo::Comparison { kind: _, left, right } => {
            ensure_matching_int_values(prog, pos, left, right)?;
        }
        ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } => {
            ensure_type_match(prog, pos, prog.type_of_value(base), prog.ty_ptr())?;

            match prog.get_type(tuple_ty).unwrap_tuple() {
                None => return Err(VerifyError::ExpectedTupleType(pos, ts(tuple_ty))),
                Some(tuple_ty_info) => {
                    if index >= tuple_ty_info.fields.len() as u32 {
                        return Err(VerifyError::TupleIndexOutOfBounds(expr, ts(tuple_ty), index, tuple_ty_info.fields.len() as u32));
                    }
                }
            }
        }
        ExpressionInfo::PointerOffSet { ty: _, base, index } => {
            ensure_type_match(prog, pos, prog.type_of_value(base), prog.ty_ptr())?;
            ensure_type_match(prog, pos, prog.type_of_value(index), prog.ty_isize())?;
        }
        ExpressionInfo::Cast { ty, kind: _, value } => {
            ensure_int_value(prog, pos, value)?;
            ensure_int_type(prog, pos, ty, None)?;
        }
    }

    Ok(())
}

#[derive(Default)]
struct FuncDeclareChecker {
    value_declared_pos: HashMap<Scoped, DomPosition>,
    block_declared_func: HashMap<Block, Function>,
}

impl FuncDeclareChecker {
    fn declare(&mut self, value: impl Into<Scoped>, pos: DomPosition) -> Result {
        let value = value.into();
        let prev = self.value_declared_pos.insert(value, pos);
        match prev {
            Some(prev) => Err(VerifyError::ValueDeclaredTwice(value.into(), prev, pos)),
            None => Ok(()),
        }
    }

    fn declare_all(&mut self, values: &[impl Into<Scoped> + Copy], pos: DomPosition) -> Result {
        for &value in values {
            self.declare(value, pos)?;
        }
        Ok(())
    }

    fn declare_block(&mut self, func: Function, block: Block) -> Result {
        let prev = self.block_declared_func.insert(block, func);
        match prev {
            Some(prev) => Err(VerifyError::BlockDeclaredTwice(block, prev, func)),
            None => Ok(()),
        }
    }
}

#[derive(Debug)]
pub struct TypeString {
    #[allow(dead_code)]
    ty: Type,
    #[allow(dead_code)]
    str: String,
}

#[derive(Debug, Copy, Clone, derive_more::From)]
pub enum TypeOrValue {
    Type(Type),
    Value(Value),
}

impl TypeString {
    fn new(prog: &Program, ty: Type) -> Self {
        TypeString {
            ty,
            str: prog.format_type(ty).to_string(),
        }
    }
}

impl TypeOrValue {
    fn ty(self, prog: &Program) -> Type {
        match self {
            TypeOrValue::Type(ty) => ty,
            TypeOrValue::Value(value) => prog.type_of_value(value),
        }
    }
}

fn ensure_type_match(prog: &Program, pos: impl Into<Position>, left: impl Into<TypeOrValue>, right: impl Into<TypeOrValue>) -> Result {
    let pos = pos.into();
    let left = left.into();
    let right = right.into();

    let left_ty = left.ty(prog);
    let right_ty = right.ty(prog);

    if left_ty == right_ty {
        Ok(())
    } else {
        Err(VerifyError::TypeMismatch(pos, left, right, prog.format_type(left_ty).to_string(), prog.format_type(right_ty).to_string()))
    }
}

fn ensure_matching_int_values(prog: &Program, pos: impl Into<Position>, left: Value, right: Value) -> Result<u32> {
    let pos = pos.into();
    let bits = ensure_int_value(prog, pos, left)?;
    ensure_type_match(prog, pos, prog.type_of_value(left), prog.type_of_value(right))?;
    Ok(bits)
}

fn ensure_int_value(prog: &Program, pos: impl Into<Position>, value: Value) -> Result<u32> {
    let pos = pos.into();
    let ty = prog.type_of_value(value);
    ensure_int_type(prog, pos, ty, Some(value))
}

fn ensure_int_type(prog: &Program, pos: impl Into<Position>, ty: Type, value: Option<Value>) -> Result<u32> {
    let pos = pos.into();
    if let Some(bits) = prog.get_type(ty).unwrap_int() {
        Ok(bits)
    } else {
        Err(VerifyError::ExpectedIntegerType(pos, value, TypeString::new(prog, ty)))
    }
}