use std::collections::{HashMap, HashSet};
use std::convert::identity;

use derive_more::Constructor;
use itertools::Itertools;

use crate::mid::analyse::use_info::{BlockUsage, for_each_usage_in_instr, Usage, UseInfo};
use crate::mid::ir::{Block, BlockInfo, Function, FunctionInfo, Instruction, InstructionInfo, Program, Terminator, TypeInfo, Value};
use crate::mid::util::visit::{Visitor, VisitState};
use crate::util::VecExt;

/// Dead code elimination.
///
/// Removes unused:
/// * function parameters and the corresponding call arguments
/// * function slots
/// * phi parameters and the corresponding terminator arguments
/// * instructions
///
/// Here unused is not just a simple "no usages", but a recursive "no usages with potential side-effects".
pub fn dce(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let alive_values = find_alive_values(prog, &use_info);
    let removed = remove_dead_values(prog, &use_info, &alive_values);

    println!("dce removed {:?}", removed);
    removed.total() > 0
}

fn find_alive_values(prog: &Program, use_info: &UseInfo) -> HashSet<Value> {
    let mut state = VisitState::new(prog);
    let visitor = DceVisitor::new(use_info);

    state.add_value(prog.main);
    let result = state.run(visitor);

    result.visited_values
}

#[derive(Constructor)]
struct DceVisitor<'a> {
    use_info: &'a UseInfo,
}

impl Visitor for DceVisitor<'_> {
    fn visit_value(&mut self, state: &mut VisitState, value: Value) {
        let prog = state.prog;

        match value {
            Value::Void | Value::Undef(_) | Value::Const(_) | Value::Extern(_) | Value::Data(_) | Value::Slot(_) => {
                // no additional handling (beyond maybe marking them as used, which already happens in add_value)
                //   this also works for slots!
                // TODO maybe only consider slots alive if they are actually loaded from?
            }
            Value::Func(func) => {
                let FunctionInfo {
                    entry, params, slots,
                    ty: _, func_ty: _, global_name: _, debug_name: _
                } = state.prog.get_func(func);

                // slots, params and phi arguments are tracked separately
                let _ = slots;
                let _ = params;
                let _ = entry.phi_values;

                state.add_block(entry.block);
            }
            Value::Param(param) => {
                // find func and index of this param
                // TODO this is slow and ugly
                let (func, index) = prog.nodes.funcs.iter().find_map(|(func, func_info)| {
                    func_info.params.index_of(&param).map(|index| (func, index))
                }).unwrap();

                // mark corresponding call arguments as used
                for &usage in &self.use_info[func] {
                    if let Usage::CallTarget { pos } = usage {
                        let args = unwrap_match!(
                            prog.get_instr(pos.instr),
                            InstructionInfo::Call { target: _, args } => args
                        );
                        state.add_value(args[index]);
                    }
                }
            }
            Value::Phi(phi) => {
                // find block and index of this phi
                // TODO this is slow and ugly
                let (block, index) = prog.nodes.blocks.iter().find_map(|(block, block_info)| {
                    block_info.phis.index_of(&phi).map(|index| (block, index))
                }).unwrap();

                // mark corresponding phi args as used
                for &usage in &self.use_info[block] {
                    let BlockUsage { target_kind } = usage;
                    state.add_value(target_kind.get_target(prog).phi_values[index]);
                }
            }
            Value::Instr(instr) => {
                // mark operands as used
                for_each_usage_in_instr((), prog.get_instr(instr), |operand, _usage| {
                    state.add_value(operand);
                });
            }
        }
    }

    fn visit_block(&mut self, state: &mut VisitState, block: Block) {
        let prog = state.prog;

        let BlockInfo { phis, instructions, terminator } = state.prog.get_block(block);

        // phy parameters are tracked separately
        let _ = phis;

        // mark side effect instructions as used
        for &instr in instructions {
            if instr_has_side_effect(prog, instr) {
                state.add_value(instr);
            }
        }

        // mark successor block as used
        // phy arguments are tracked separately
        match *terminator {
            Terminator::Jump { ref target } => {
                state.add_block(target.block);
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                state.add_value(cond);
                state.add_block(true_target.block);
                state.add_block(false_target.block);
            }
            Terminator::Return { value } => {
                state.add_value(value);
            }
            Terminator::Unreachable => {}
        }

        terminator.for_each_target(|target| {
            state.add_block(target.block);
        });
    }
}

fn instr_has_side_effect(prog: &Program, instr: Instruction) -> bool {
    match prog.get_instr(instr) {
        InstructionInfo::Load { addr: _, ty: _ } => false,
        InstructionInfo::Store { addr: _, ty, value: _ } => {
            *ty != prog.ty_void()
        }

        InstructionInfo::Call { target: _, args: _ } => {
            // TODO somehow track side effects for a function?
            true
        }

        InstructionInfo::Arithmetic { kind: _, left: _, right: _ } => false,
        InstructionInfo::Comparison { kind: _, left: _, right: _ } => false,
        InstructionInfo::TupleFieldPtr { base: _, index: _, tuple_ty: _ } => false,
        InstructionInfo::PointerOffSet { ty: _, base: _, index: _ } => false,
        InstructionInfo::Cast { ty: _, kind: _, value: _ } => false,
        InstructionInfo::BlackBox { .. } => true,
    }
}

#[derive(Debug, Default)]
struct Removed {
    params: usize,
    args: usize,
    slots: usize,
    phi_params: usize,
    phi_args: usize,
    instrs: usize,
}

fn remove_dead_values(prog: &mut Program, use_info: &UseInfo, alive_values: &HashSet<Value>) -> Removed {
    let mut removed = Removed::default();

    let param_masks: HashMap<Function, Vec<bool>> = calc_param_masks(prog, use_info, alive_values);

    for block in use_info.blocks() {
        // figure out which phis are alive
        let phi_mask = prog.get_block(block).phis.iter()
            .map(|&phi| {
                alive_values.contains(&phi.into())
            })
            .collect_vec();

        // remove all dead phi args from targets pointing to this block
        for usage in &use_info[block] {
            let BlockUsage { target_kind } = usage;
            let target = target_kind.get_target_mut(prog);
            removed.phi_args += retain_mask(&mut target.phi_values, &phi_mask);
        }

        // remove the phi params of this block itself
        removed.phi_params += retain_mask(&mut prog.get_block_mut(block).phis, &phi_mask);

        // remove dead instructions (and dead call args)
        let block_info = &mut prog.nodes.blocks[block];
        let prog_instrs = &mut prog.nodes.instrs;
        block_info.instructions.retain(|&instr| {
            let keep = alive_values.contains(&instr.into());
            if keep {
                // potentially remove dead call args
                if let InstructionInfo::Call { target: Value::Func(target), args } = &mut prog_instrs[instr] {
                    if let Some(arg_mask) = param_masks.get(target) {
                        removed.args += retain_mask(args, arg_mask);
                    }
                }
            }
            removed.instrs += !keep as usize;
            keep
        });
    }

    for (func, func_info) in prog.nodes.funcs.iter_mut() {
        let FunctionInfo {
            ty, func_ty,
            global_name: _, debug_name: _, entry: _,
            params, slots
        } = func_info;

        // remove dead function params
        if let Some(param_mask) = param_masks.get(&func) {
            removed.params += retain_mask(params, param_mask);

            // also change function type
            let mut new_func_ty = func_ty.clone();
            retain_mask(&mut new_func_ty.params, param_mask);
            let new_ty = prog.types.push(TypeInfo::Func(new_func_ty.clone()));

            *ty = new_ty;
            *func_ty = new_func_ty;
        }

        // remove dead slots
        slots.retain(|&slot| {
            let keep = alive_values.contains(&slot.into());
            removed.slots += !keep as usize;
            keep
        })
    }

    removed
}

/// Calculate which parameters to keep for the given function.
/// If a function is not present all its parameters should be kept.
fn calc_param_masks(prog: &mut Program, use_info: &UseInfo, alive_values: &HashSet<Value>) -> HashMap<Function, Vec<bool>> {
    prog.nodes.funcs.iter().filter_map(|(func, func_info)| {
        if use_info.function_only_used_as_call_target(func) {
            let mask = func_info.params.iter()
                .map(|&param| alive_values.contains(&param.into()))
                .collect_vec();

            if mask.iter().copied().all(identity) {
                None
            } else {
                Some((func, mask))
            }
        } else {
            None
        }
    }).collect()
}

fn retain_mask<T>(values: &mut Vec<T>, mask: &[bool]) -> usize {
    assert_eq!(values.len(), mask.len());

    let mut count = 0;

    let mut phi_index = 0;
    values.retain(|_| {
        let keep = mask[phi_index];
        count += !keep as usize;
        phi_index += 1;
        keep
    });

    count
}

impl Removed {
    fn total(&self) -> usize {
        let &Removed {
            params, args, slots, phi_params, phi_args, instrs
        } = self;

        params + args + slots + phi_params + phi_args + instrs
    }
}