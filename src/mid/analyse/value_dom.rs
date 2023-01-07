use crate::mid::analyse::dom_info::{DomInfo, DomPosition, InBlockPos};
use crate::mid::analyse::usage::{try_for_each_expr_leaf_value, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Expression, Function, Program, Scoped, Value};
use crate::util::VecExt;

// TODO this entire file is kind of brute-forcy and sad, can we compute this in advance in either dominfo or useinfo?

#[derive(Debug)]
pub enum DefError {
    NoDefFound,
    NeedFunction,
    Expression(Expression),
}

impl DomPosition {
    // TODO find a faster way to do this
    //   maybe the only solution is to keep track of this for each value? that's pretty ugly and brittle...
    pub fn find_def_slow(prog: &Program, func: Option<Function>, value: Value) -> Result<Self, DefError> {
        let get_func = || {
            let func = func.ok_or(DefError::NeedFunction)?;
            Ok((func, prog.get_func(func)))
        };

        match value {
            Value::Global(_) | Value::Immediate(_) => {
                Ok(DomPosition::Global)
            }
            Value::Scoped(value) => {
                match value {
                    Scoped::Param(param) => {
                        let (func, func_info) = get_func()?;
                        prog.try_visit_blocks(func_info.entry, |block| {
                            let block_info = prog.get_block(block);
                            if block_info.params.contains(&param) {
                                Err(DomPosition::InBlock(func, block, InBlockPos::Entry))
                            } else {
                                Ok(())
                            }
                        }).err().ok_or(DefError::NoDefFound)
                    }
                    Scoped::Slot(slot) => {
                        let (func, func_info) = get_func()?;
                        func_info.slots.contains(&slot).then_some(DomPosition::FuncEntry(func)).ok_or(DefError::NoDefFound)
                    }
                    Scoped::Instr(instr) => {
                        let (func, func_info) = get_func()?;
                        prog.try_visit_blocks(func_info.entry, |block| {
                            let block_info = prog.get_block(block);
                            if let Some(index) = block_info.instructions.index_of(&instr) {
                                Err(DomPosition::InBlock(func, block, InBlockPos::Instruction(index)))
                            } else {
                                Ok(())
                            }
                        }).err().ok_or(DefError::NoDefFound)
                    }
                }
            }
            // TODO implement some infrastructure for expression domination, both in the use and def direction
            Value::Expr(expr) => Err(DefError::Expression(expr)),
        }
    }
}

#[derive(Debug)]
pub struct NoDefFound;

// TODO this can be slot for large expression trees, O(leaf * down)
pub fn value_strictly_dominates_usage_slow(
    prog: &Program,
    dom_info: &DomInfo,
    use_info: &UseInfo,
    value: Value,
    usage: &Usage
) -> Result<bool, NoDefFound> {
    let use_pos = usage.as_dom_pos();

    match use_pos {
        Ok(use_pos) => {
            let func = use_pos.function();
            let def_pos = DomPosition::find_def_slow(prog, func, value);

            match def_pos {
                Ok(def_pos) => Ok(dom_info.pos_is_strict_dominator(def_pos, use_pos)),
                Err(DefError::NeedFunction) => {
                    // the usage is not in a function but the define is
                    Ok(false)
                }
                Err(DefError::NoDefFound) => Err(NoDefFound),
                Err(DefError::Expression(expr)) => {
                    let result = try_for_each_expr_leaf_value(prog, expr, |leaf, _| {
                        assert!(leaf.as_expr().is_none());
                        let result = value_strictly_dominates_usage_slow(prog, dom_info, use_info, leaf, usage);
                        match result {
                            Ok(true) => Ok(()),
                            Ok(false) => Err(AllError::FoundFalse),
                            Err(e) => Err(AllError::Error(e)),
                        }
                    });

                    match result {
                        Ok(()) => Ok(true),
                        Err(AllError::FoundFalse) => Ok(false),
                        Err(AllError::Error(e)) => Err(e),
                    }
                }
            }
        }
        Err(use_expr) => {
            // check if the def dominates all downstream users of this expression
            for down_usage in &use_info[use_expr] {
                let down_dom = value_strictly_dominates_usage_slow(prog, dom_info, use_info, value, down_usage)?;
                if !down_dom {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}

enum AllError<E> {
    FoundFalse,
    Error(E),
}