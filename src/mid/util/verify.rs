use std::collections::HashMap;
use std::iter::zip;

use crate::mid::analyse::dom_info::{BlockPosition, DomInfo, DomPosition};
use crate::mid::analyse::use_info::try_for_each_usage_in_instr;
use crate::mid::ir::{Block, BlockInfo, Function, Instruction, InstructionInfo, Program, Type, TypeInfo, Value};

#[derive(Debug)]
pub enum VerifyError {
    ValueDeclaredTwice(Value, DomPosition, DomPosition),
    BlockDeclaredTwice(Block, Function, Function),

    TypeMismatch(Type, Type, String, String),
    ExpectedIntegerType(Option<Value>, Type, String),
    ExpectedTupleType(Type, String),
    ExpectedFunctionType(Type, String),
    WrongCallArgCount(Type, String, usize),
    TupleIndexOutOfBounds(Type, String, u32, u32),

    NonDeclaredValueUsed(Value, DomPosition),
    NonDominatingValueUsed(Value, DomPosition, DomPosition),
    WrongPhiCount(Block, Block),
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

        prog.try_visit_blocks(func_info.entry.block, |block| {
            let BlockInfo { phis, instructions, terminator: _ } = prog.get_block(block);

            declarer.declare_block(func, block)?;
            declarer.declare_all(phis, DomPosition::InBlock(func, block, BlockPosition::before_instructions()))?;

            for (instr_index, &instr) in instructions.iter().enumerate() {
                declarer.declare(instr, DomPosition::InBlock(func, block, BlockPosition::at_instruction(instr_index)))?;
            }

            Ok(())
        })?;
    }

    // check types and value domination
    for (func, func_info) in &prog.nodes.funcs {
        // check function signature match
        ensure_type_match(prog, func_info.ty, prog.types.lookup(&TypeInfo::Func(func_info.func_ty.clone())).unwrap())?;

        let dom_info = &DomInfo::new(prog, func);

        for &block in &dom_info.blocks {
            let BlockInfo { phis: _, instructions, terminator } = prog.get_block(block);

            for (instr_index, &instr) in instructions.iter().enumerate() {
                let instr_info = prog.get_instr(instr);

                // check instruction types
                check_instr_types(prog, instr)?;

                // check instr arg domination
                let use_pos = DomPosition::InBlock(func, block, BlockPosition::at_instruction(instr_index));
                try_for_each_usage_in_instr((), instr_info, |value, _| {
                    declarer.ensure_dominates(dom_info, value, use_pos)
                })?;
            }

            // check terminator arg domination
            let term_use_pos = DomPosition::InBlock(func, block, BlockPosition::after_instructions(instructions.len()));
            terminator.try_for_each_non_target_value(|value| {
                declarer.ensure_dominates(dom_info, value, term_use_pos)
            })?;

            terminator.try_for_each_target(|target| {
                // check phi type match
                let target_block_info = prog.get_block(target.block);
                if target.phi_values.len() != target_block_info.phis.len() {
                    return Err(VerifyError::WrongPhiCount(block, target.block));
                }
                for (&phi, &phi_value) in zip(&target_block_info.phis, &target.phi_values) {
                    ensure_type_match(prog, prog.get_phi(phi).ty, prog.type_of_value(phi_value))?;
                }

                // check phi domination
                for &value in &target.phi_values {
                    declarer.ensure_dominates(dom_info, value, term_use_pos)?;
                }
                Ok(())
            })?;
        }
    }

    Ok(())
}

fn check_instr_types(prog: &Program, instr: Instruction) -> Result {
    let instr_info = prog.get_instr(instr);

    match instr_info {
        &InstructionInfo::Load { addr, ty: _ } => {
            ensure_type_match(prog, prog.type_of_value(addr), prog.ty_ptr())?;
        }
        &InstructionInfo::Store { addr, ty, value } => {
            ensure_type_match(prog, prog.type_of_value(addr), prog.ty_ptr())?;
            ensure_type_match(prog, prog.type_of_value(value), ty)?;
        }
        &InstructionInfo::Call { target, ref args } => {
            let target_ty = prog.type_of_value(target);
            let target_func_ty = prog.get_type(target_ty).unwrap_func()
                .ok_or_else(|| VerifyError::ExpectedFunctionType(target_ty, prog.format_type(target_ty).to_string()))?;

            if target_func_ty.params.len() != args.len() {
                return Err(VerifyError::WrongCallArgCount(target_ty, prog.format_type(target_ty).to_string(), args.len()));
            }

            for (&param, &arg) in zip(&target_func_ty.params, args) {
                ensure_type_match(prog, param, prog.type_of_value(arg))?;
            }
        }
        &InstructionInfo::Arithmetic { kind: _, left, right } => {
            ensure_matching_int_values(prog, left, right)?;
        }
        &InstructionInfo::Comparison { kind: _, left, right } => {
            ensure_matching_int_values(prog, left, right)?;
        }
        &InstructionInfo::TupleFieldPtr { base, index, tuple_ty } => {
            ensure_type_match(prog, prog.type_of_value(base), prog.ty_ptr())?;

            match prog.get_type(tuple_ty).unwrap_tuple() {
                None => return Err(VerifyError::ExpectedTupleType(tuple_ty, prog.format_type(tuple_ty).to_string())),
                Some(tuple_ty_info) => {
                    if index >= tuple_ty_info.fields.len() as u32 {
                        return Err(VerifyError::TupleIndexOutOfBounds(tuple_ty, prog.format_type(tuple_ty).to_string(), index, tuple_ty_info.fields.len() as u32));
                    }
                }
            }
        }
        &InstructionInfo::PointerOffSet { ty: _, base, index } => {
            ensure_type_match(prog, prog.type_of_value(base), prog.ty_ptr())?;
            ensure_type_match(prog, prog.type_of_value(index), prog.ty_isize())?;
        }
        &InstructionInfo::Cast { ty, kind: _, value } => {
            ensure_int_value(prog, value)?;
            ensure_int_type(prog, ty, None)?;
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

    fn ensure_dominates(&self, dom_info: &DomInfo, value: Value, use_pos: DomPosition) -> Result {
        let def_pos = match value {
            Value::Void | Value::Undef(_) | Value::Const(_) | Value::Func(_) | Value::Extern(_) | Value::Data(_) => {
                DomPosition::Global
            }
            Value::Param(_) | Value::Slot(_) | Value::Phi(_) | Value::Instr(_) => {
                self.value_declared_pos.get(&value).copied().ok_or_else(|| VerifyError::NonDeclaredValueUsed(value, use_pos))?
            }
        };

        if dom_info.pos_is_strict_dominator(def_pos, use_pos) {
            Ok(())
        } else {
            Err(VerifyError::NonDominatingValueUsed(value, def_pos, use_pos))
        }
    }
}

fn ensure_type_match(prog: &Program, left: Type, right: Type) -> Result {
    if left == right {
        Ok(())
    } else {
        Err(VerifyError::TypeMismatch(left, right, prog.format_type(left).to_string(), prog.format_type(right).to_string()))
    }
}

fn ensure_matching_int_values(prog: &Program, left: Value, right: Value) -> Result<u32> {
    let bits = ensure_int_value(prog, left)?;
    ensure_type_match(prog, prog.type_of_value(left), prog.type_of_value(right))?;
    Ok(bits)
}

fn ensure_int_value(prog: &Program, value: Value) -> Result<u32> {
    let ty = prog.type_of_value(value);
    ensure_int_type(prog, ty, Some(value))
}

fn ensure_int_type(prog: &Program, ty: Type, value: Option<Value>) -> Result<u32> {
    if let Some(bits) = prog.get_type(ty).unwrap_int() {
        Ok(bits)
    } else {
        Err(VerifyError::ExpectedIntegerType(value, ty, prog.format_type(ty).to_string()))
    }
}