use std::collections::HashMap;
use std::iter::zip;

use crate::mid::analyse::dom_info::{BlockPosition, DomInfo, DomPosition};
use crate::mid::analyse::use_info::try_for_each_usage_in_instr;
use crate::mid::ir::{Block, BlockInfo, Function, Instruction, InstructionInfo, Program, Target, Terminator, Type, TypeInfo, Value};

#[derive(Debug)]
pub enum VerifyError {
    ValueDeclaredTwice(Value, DomPosition, DomPosition),
    BlockDeclaredTwice(Block, Function, Function),

    NonDeclaredValueUsed(Value, DomPosition),
    NonDominatingValueUsed(Value, DomPosition, DomPosition),

    WrongDeclParamCount(Function, TypeString, usize),
    WrongPhiArgCount(DomPosition, Block),

    TypeMismatch(DomPosition, TypeOrValue, TypeOrValue, String, String),
    ExpectedIntegerType(DomPosition, Option<Value>, TypeString),
    ExpectedTupleType(DomPosition, TypeString),
    ExpectedFunctionType(DomPosition, TypeString),

    WrongCallParamCount(DomPosition, TypeString, usize),
    TupleIndexOutOfBounds(DomPosition, TypeString, u32, u32),
}

type Result<T = ()> = std::result::Result<T, VerifyError>;

// TODO check phi types and count
// TODO check instruction arg types
// TODO check instruction and phi arg dominated

// TODO first test case: ternary with runtime cond and values undef or non-dominating instr

pub fn verify(prog: &Program) -> Result {
    let mut declarer = FuncDeclareChecker::default();

    // check for duplicate declarations
    for (func, func_info) in &prog.nodes.funcs {
        declarer.declare_all(&func_info.params, DomPosition::FuncEntry(func))?;
        declarer.declare_all(&func_info.slots, DomPosition::FuncEntry(func))?;

        // TODO this way of visiting blocks means we never verify unreachable blocks. Is that okay?
        prog.try_visit_blocks(func_info.entry.block, |block| {
            let BlockInfo { phis, instructions, terminator: _ } = prog.get_block(block);

            declarer.declare_block(func, block)?;
            declarer.declare_all(phis, DomPosition::InBlock(func, block, BlockPosition::Entry))?;

            for (instr_index, &instr) in instructions.iter().enumerate() {
                declarer.declare(instr, DomPosition::InBlock(func, block, BlockPosition::Instruction(instr_index)))?;
            }

            Ok(())
        })?;
    }

    // TODO check entry function type? first improve how we handle it
    let ts = |ty: Type| TypeString::new(prog, ty);

    // check types and value domination
    for (func, func_info) in &prog.nodes.funcs {
        let dom_info = &DomInfo::new(prog, func);
        let func_pos = DomPosition::FuncEntry(func);

        let ctx = Context {
            prog,
            declarer: &declarer,
            dom_info,
        };

        // check function type match
        let expected_func_ty = prog.types.lookup(&TypeInfo::Func(func_info.func_ty.clone()));
        ensure_type_match(prog, func_pos, func_info.ty, expected_func_ty.unwrap())?;

        // check that params match the signature
        if func_info.func_ty.params.len() != func_info.params.len() {
            return Err(VerifyError::WrongDeclParamCount(func, ts(func_info.ty), func_info.params.len()));
        }
        for (&param_ty, &param) in zip(&func_info.func_ty.params, &func_info.params) {
            ensure_type_match(prog, func_pos, param_ty, prog.type_of_value(param.into()))?;
        }

        // check entry target
        ctx.check_target(DomPosition::FuncEntry(func), &func_info.entry)?;

        for &block in &dom_info.blocks {
            let BlockInfo { phis: _, instructions, terminator } = prog.get_block(block);

            for (instr_index, &instr) in instructions.iter().enumerate() {
                let instr_info = prog.get_instr(instr);
                let instr_pos = DomPosition::InBlock(func, block, BlockPosition::Instruction(instr_index));

                // check instruction types
                check_instr_types(prog, instr, instr_pos)?;

                // check instr arg domination
                try_for_each_usage_in_instr((), instr_info, |value, _| {
                    ctx.ensure_dominates(value, instr_pos)
                })?;
            }

            // check terminator
            let term_pos = DomPosition::InBlock(func, block, BlockPosition::Terminator);

            match *terminator {
                Terminator::Jump { ref target } => {
                    ctx.check_target(term_pos, target)?
                }
                Terminator::Branch { cond, ref true_target, ref false_target } => {
                    ensure_type_match(prog, term_pos, cond, prog.ty_bool())?;
                    ctx.ensure_dominates(cond, term_pos)?;
                    ctx.check_target(term_pos, true_target)?;
                    ctx.check_target(term_pos, false_target)?;
                }
                Terminator::Return { value } => {
                    ensure_type_match(prog, term_pos, value, func_info.func_ty.ret)?;
                    ctx.ensure_dominates(value, term_pos)?;
                }
                Terminator::Unreachable => {}
            }
        }
    }

    Ok(())
}

#[derive(Copy, Clone)]
struct Context<'a> {
    prog: &'a Program,
    declarer: &'a FuncDeclareChecker,
    dom_info: &'a DomInfo,
}

impl<'a> Context<'a> {
    fn check_target(&self, pos: DomPosition, target: &Target) -> Result {
        let prog = self.prog;

        // check phi type match
        let target_block_info = prog.get_block(target.block);
        if target.phi_values.len() != target_block_info.phis.len() {
            return Err(VerifyError::WrongPhiArgCount(pos, target.block));
        }
        for (&phi, &phi_value) in zip(&target_block_info.phis, &target.phi_values) {
            ensure_type_match(prog, pos, prog.get_phi(phi).ty, phi_value)?;
        }

        // check phi domination
        for &value in &target.phi_values {
            self.ensure_dominates(value, pos)?;
        }
        Ok(())
    }

    fn ensure_dominates(&self, value: Value, use_pos: DomPosition) -> Result {
        let def_pos = match value {
            Value::Global(_) | Value::Immediate(_) => DomPosition::Global,
            Value::Scoped(_) => {
                self.declarer.value_declared_pos.get(&value).copied().ok_or(VerifyError::NonDeclaredValueUsed(value, use_pos))?
            }
        };

        if self.dom_info.pos_is_strict_dominator(def_pos, use_pos) {
            Ok(())
        } else {
            Err(VerifyError::NonDominatingValueUsed(value, def_pos, use_pos))
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
        &InstructionInfo::Call { target, ref args } => {
            let target_ty = prog.type_of_value(target);
            let target_func_ty = prog.get_type(target_ty).unwrap_func()
                .ok_or_else(|| VerifyError::ExpectedFunctionType(pos, ts(target_ty)))?;

            if target_func_ty.params.len() != args.len() {
                return Err(VerifyError::WrongCallParamCount(pos, ts(target_ty), args.len()));
            }

            for (&param, &arg) in zip(&target_func_ty.params, args) {
                ensure_type_match(prog, pos, param, prog.type_of_value(arg))?;
            }
        }
        &InstructionInfo::Arithmetic { kind: _, left, right } => {
            ensure_matching_int_values(prog, pos, left, right)?;
        }
        &InstructionInfo::Comparison { kind: _, left, right } => {
            ensure_matching_int_values(prog, pos, left, right)?;
        }
        &InstructionInfo::TupleFieldPtr { base, index, tuple_ty } => {
            ensure_type_match(prog, pos, prog.type_of_value(base), prog.ty_ptr())?;

            match prog.get_type(tuple_ty).unwrap_tuple() {
                None => return Err(VerifyError::ExpectedTupleType(pos, ts(tuple_ty))),
                Some(tuple_ty_info) => {
                    if index >= tuple_ty_info.fields.len() as u32 {
                        return Err(VerifyError::TupleIndexOutOfBounds(pos, ts(tuple_ty), index, tuple_ty_info.fields.len() as u32));
                    }
                }
            }
        }
        &InstructionInfo::PointerOffSet { ty: _, base, index } => {
            ensure_type_match(prog, pos, prog.type_of_value(base), prog.ty_ptr())?;
            ensure_type_match(prog, pos, prog.type_of_value(index), prog.ty_isize())?;
        }
        &InstructionInfo::Cast { ty, kind: _, value } => {
            ensure_int_value(prog, pos, value)?;
            ensure_int_type(prog, pos, ty, None)?;
        }
        InstructionInfo::BlackBox { value: _ } => {}
    }

    Ok(())
}

#[derive(Default)]
struct FuncDeclareChecker {
    value_declared_pos: HashMap<Value, DomPosition>,
    block_declared_func: HashMap<Block, Function>,
}

impl FuncDeclareChecker {
    fn declare(&mut self, value: impl Into<Value>, pos: DomPosition) -> Result {
        let value = value.into();
        let prev = self.value_declared_pos.insert(value, pos);
        match prev {
            Some(prev) => Err(VerifyError::ValueDeclaredTwice(value, prev, pos)),
            None => Ok(()),
        }
    }

    fn declare_all(&mut self, values: &[impl Into<Value> + Copy], pos: DomPosition) -> Result {
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

fn ensure_type_match(prog: &Program, pos: DomPosition, left: impl Into<TypeOrValue>, right: impl Into<TypeOrValue>) -> Result {
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

fn ensure_matching_int_values(prog: &Program, pos: DomPosition, left: Value, right: Value) -> Result<u32> {
    let bits = ensure_int_value(prog, pos, left)?;
    ensure_type_match(prog, pos, prog.type_of_value(left), prog.type_of_value(right))?;
    Ok(bits)
}

fn ensure_int_value(prog: &Program, pos: DomPosition, value: Value) -> Result<u32> {
    let ty = prog.type_of_value(value);
    ensure_int_type(prog, pos, ty, Some(value))
}

fn ensure_int_type(prog: &Program, pos: DomPosition, ty: Type, value: Option<Value>) -> Result<u32> {
    if let Some(bits) = prog.get_type(ty).unwrap_int() {
        Ok(bits)
    } else {
        Err(VerifyError::ExpectedIntegerType(pos, value, TypeString::new(prog, ty)))
    }
}