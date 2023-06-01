use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use fixedbitset::FixedBitSet;

use crate::mid::analyse::usage::{BlockUsage, InstrOperand, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, BlockInfo, Function, FunctionInfo, Global, Immediate, Instruction, InstructionInfo, Parameter, Program, Scoped, Target, Terminator, TypeInfo, Value};
use crate::mid::util::visit::{Visitor, VisitState};
use crate::util::VecExt;
use crate::util::internal_iter::InternalIterator;

/// Dead code elimination.
///
/// Removes unused:
/// * function parameters and the corresponding call arguments
/// * function slots
/// * block parameters and the corresponding target arguments
/// * instructions
/// * TODO func return values
///
/// Here unused is not just a simple "no usages", but a recursive "no usages with potential side-effects".
///
/// For functions used as non-call targets we have to keep the params,
/// but in  calls to functions with dead params we still replace the corresponding args with undef.
pub fn dce(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let alive = collect_alive(prog, &use_info);

    let removed = remove_dead_values(prog, &use_info, &alive);

    println!("dce removed {:?}", removed);
    removed.total() > 0
}

struct Alive {
    values: HashSet<Value>,
    funcs_used_as_non_call_target: HashSet<Function>,
    block_masks: HashMap<Block, FixedBitSet>,
}

enum FuncParamMask<'a> {
    RemoveKeep(&'a FixedBitSet),
    ReplaceKeep(&'a FixedBitSet),
    Full,
}

impl Alive {
    fn is_alive(&self, value: impl Into<Value>) -> bool {
        self.values.contains(&value.into())
    }

    fn block_param_mask(&self, block: Block) -> Option<&FixedBitSet> {
        self.block_masks.get(&block)
    }

    fn func_param_mask(&self, func: Function, entry: Block) -> FuncParamMask {
        match self.block_param_mask(entry) {
            None => FuncParamMask::Full,
            Some(mask) => {
                let can_remove = !self.funcs_used_as_non_call_target.contains(&func);
                if can_remove {
                    FuncParamMask::RemoveKeep(mask)
                } else {
                    FuncParamMask::ReplaceKeep(mask)
                }
            }
        }
    }
}

fn collect_alive(prog: &Program, use_info: &UseInfo) -> Alive {
    let mut state = VisitState::new(prog);
    let mut visitor = DceVisitor::new(use_info);

    visitor.add_values_target(&mut state, prog.root_functions.values().copied());
    let result = state.run(&mut visitor);

    let block_masks: HashMap<Block, FixedBitSet> = result.visited_blocks.iter()
        .filter_map(|&block| {
            calc_block_param_mask(prog, block, &result.visited_values)
                .map(|used| (block, used))
        })
        .collect();

    Alive {
        values: result.visited_values,
        funcs_used_as_non_call_target: visitor.funcs_used_as_non_call_target,
        block_masks,
    }
}

struct DceVisitor<'a> {
    use_info: &'a UseInfo,

    // separately track which functions are used as non-call-targets
    //   we don't rely on use_info for this since we can discover more of them
    funcs_used_as_non_call_target: HashSet<Function>,
}

impl Visitor for DceVisitor<'_> {
    fn visit_value(&mut self, state: &mut VisitState, value: Value) {
        let prog = state.prog;

        match value {
            Value::Immediate(_) | Value::Global(Global::Extern(_) | Global::Data(_)) | Value::Scoped(Scoped::Slot(_)) => {
                // no additional handling (beyond marking them as used, which already happens in add_value)
            }
            Value::Global(Global::Func(func)) => {
                // slots and func params (really block params) are tracked separately
                let &FunctionInfo {
                    entry, slots: _,
                    ty: _, func_ty: _, debug_name: _
                } = state.prog.get_func(func);

                state.add_block(entry);
            }
            Value::Scoped(Scoped::Param(param)) => {
                let (func, block, index) = find_param_pos(prog, &param);

                if prog.get_func(func).entry == block {
                    // this is a function param, visit the corresponding call args
                    for usage in &self.use_info[func] {
                        if let Usage::InstrOperand { pos, usage: InstrOperand::CallTarget } = usage {
                            let args = unwrap_match!(
                                prog.get_instr(pos.instr),
                                InstructionInfo::Call { target: _, args, conv: _ } => args
                            );

                            self.add_value(state, args[index]);
                        }
                    }
                } else {
                    // this is a block param, visit the corresponding target args
                    for &usage in &self.use_info[block] {
                        let (pred, kind) = unwrap_match!(usage, BlockUsage::Target { pos, kind } => (pos, kind));
                        let target = kind.get_target(&prog.get_block(pred.block).terminator);
                        self.add_value(state, target.args[index]);
                    }
                }
            }
            Value::Scoped(Scoped::Instr(instr)) => {
                let instr_info = prog.get_instr(instr);

                match instr_info {
                    &InstructionInfo::Call { target: Value::Global(Global::Func(func)), ref args, conv: _ } => {
                        // value used as call target, so we don't need to mark all of the args as used
                        self.add_value_target(state, func);

                        // mark args that correspond to used params as used
                        for (i, &arg) in args.iter().enumerate() {
                            let param = prog.get_block(prog.get_func(func).entry).params[i];
                            if state.has_visited_value(param) {
                                self.add_value(state, arg);
                            }
                        }
                    }
                    _ => {
                        // fallback, mark all operands as used
                        prog.get_instr(instr).operands().for_each(|(operand, usage)| {
                            if matches!(usage, InstrOperand::CallTarget) {
                                self.add_value_target(state, operand);
                            } else {
                                self.add_value(state, operand);
                            }
                        });
                    }
                }
            }
            Value::Expr(expr) => {
                // mark all operands as used
                prog.get_expr(expr).operands().for_each(|(operand, _)| {
                    self.add_value(state, operand);
                });
            }
        }
    }

    fn visit_block(&mut self, state: &mut VisitState, block: Block) {
        let prog = state.prog;

        // block params are tracked separately
        let BlockInfo { params: _, instructions, terminator, debug_name: _ } = state.prog.get_block(block);

        // mark side effect instructions as used
        for &instr in instructions {
            if instr_has_side_effect(prog, instr) {
                self.add_value(state, instr);
            }
        }

        // mark successor block as used
        // block args are tracked separately
        match *terminator {
            Terminator::Jump { ref target } => {
                state.add_block(target.block);
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                self.add_value(state, cond);
                state.add_block(true_target.block);
                state.add_block(false_target.block);
            }
            Terminator::Return { value } => {
                self.add_value(state, value);
            }
            Terminator::Unreachable => {}
            Terminator::LoopForever => {}
        }

        terminator.targets().for_each(|(target, _)| {
            state.add_block(target.block);
        });
    }
}

// TODO it's kind of awkward that we have to remember to use these functions instead of the state ones
//    (aka default unsafe), is there a better way to do this? maybe make visitor usage-aware?
impl<'a> DceVisitor<'a> {
    pub fn new(use_info: &'a UseInfo) -> Self {
        Self {
            use_info,
            funcs_used_as_non_call_target: Default::default(),
        }
    }

    fn add_value_target(&mut self, state: &mut VisitState, value: impl Into<Value>) {
        state.add_value(value);
    }

    pub fn add_values_target<I: Into<Value>>(&mut self, state: &mut VisitState, values: impl IntoIterator<Item=I>) {
        state.add_values(values);
    }

    fn add_value(&mut self, state: &mut VisitState, value: impl Into<Value>) {
        let value = value.into();

        // add the value as normal
        state.add_value(value);

        // potentially mark the function as used as non-call-target
        if let Some(func) = value.as_func() {
            self.funcs_used_as_non_call_target.insert(func);
        }
    }

    #[allow(dead_code)]
    pub fn add_values<I: Into<Value>>(&mut self, state: &mut VisitState, values: impl IntoIterator<Item=I>) {
        for value in values {
            self.add_value(state, value.into());
        }
    }
}

// TODO this is slow and ugly
fn find_param_pos(prog: &Program, param: &Parameter) -> (Function, Block, usize) {
    prog.nodes.funcs.iter().find_map(|(func, func_info)| {
        prog.reachable_blocks(func_info.entry).find_map(|block| {
            prog.get_block(block)
                .params.index_of(param)
                .map(|index| (func, block, index))
        })
    }).unwrap()
}

fn instr_has_side_effect(prog: &Program, instr: Instruction) -> bool {
    match prog.get_instr(instr) {
        InstructionInfo::Load { addr: _, ty: _ } => false,
        InstructionInfo::Store { addr: _, ty, value: _ } => *ty != prog.ty_void(),
        InstructionInfo::Call { target: _, args: _, conv: _ } => true,
        InstructionInfo::BlackBox { value: _ } => true,
    }
}

#[derive(Debug, Default)]
struct Removed {
    slots: usize,
    instrs: usize,

    func_params: usize,
    call_args: usize,
    call_args_undef: usize,

    block_params: usize,
    target_args: usize,
}

fn remove_dead_values(prog: &mut Program, use_info: &UseInfo, alive: &Alive) -> Removed {
    let mut removed = Removed::default();

    for func in use_info.funcs() {
        // don't bother fixing dead functions
        // TODO maybe we should, otherwise verify can fail?
        if !alive.is_alive(func) {
            continue;
        }

        let FunctionInfo { ty, func_ty, slots, entry, debug_name: _ } =
            &mut prog.nodes.funcs[func];
        let entry = *entry;

        // remove dead slots
        slots.retain(|&slot| {
            let keep = alive.is_alive(slot);
            removed.slots += !keep as usize;
            keep
        });

        // update the function type
        if let FuncParamMask::RemoveKeep(param_mask) = alive.func_param_mask(func, entry) {
            let mut new_func_ty = func_ty.clone();
            let _ = retain_mask(&mut new_func_ty.params, param_mask);
            let new_ty = prog.types.push(TypeInfo::Func(new_func_ty.clone()));

            *ty = new_ty;
            *func_ty = new_func_ty;
        }

        let func_used_as_non_call_target = alive.funcs_used_as_non_call_target.contains(&func);

        let blocks = prog.reachable_blocks(entry).collect_vec();
        for &block in &blocks {
            let keep_params = block == entry && func_used_as_non_call_target;
            remove_dead_values_from_block(prog, &mut removed, alive, block, keep_params);
        }
    }

    removed
}

fn remove_dead_values_from_block(prog: &mut Program, removed: &mut Removed, alive: &Alive, block: Block, keep_params: bool) {
    let prog_instrs = &mut prog.nodes.instrs;
    let prog_blocks = &mut prog.nodes.blocks;
    let prog_funcs = &mut prog.nodes.funcs;

    let BlockInfo { params, instructions, terminator, debug_name: _ } = &mut prog_blocks[block];

    // remove block params if we're allowed to
    if !keep_params {
        if let Some(block_mask) = alive.block_param_mask(block) {
            removed.block_params += retain_mask(params, block_mask);
        }
    }

    // remove dead instructions and dead call args
    instructions.retain(|&instr| {
        let keep = alive.is_alive(instr);

        if keep {
            // only consider instructions that we're going to keep
            let instr_info = &mut prog_instrs[instr];

            // is this is a call to a function
            if let &mut InstructionInfo::Call { target: Value::Global(Global::Func(target)), ref mut args, conv: _ } = instr_info {
                let target_info = &prog_funcs[target];

                // remove or replace dead params if any
                match alive.func_param_mask(target, target_info.entry) {
                    FuncParamMask::RemoveKeep(mask) => {
                        // we can just remove the args
                        removed.call_args += retain_mask(args, mask);
                    }
                    FuncParamMask::ReplaceKeep(mask) => {
                        // we can't actually remove the args, but we can replace them with undef
                        for (i, arg) in args.iter_mut().enumerate() {
                            if !mask[i] && !arg.is_undef() {
                                let ty = target_info.func_ty.params[i];
                                *arg = Immediate::Undef(ty).into();
                                removed.call_args_undef += 1;
                            }
                        }
                    }
                    FuncParamMask::Full => {
                        // we can't do anything
                    }
                }
            }
        }

        removed.instrs += !keep as usize;
        keep
    });

    // remove dead target args
    terminator.targets_mut().for_each(|(target, _)| {
        let &mut Target { block: target_block, ref mut args } = target;
        if let Some(target_mask) = alive.block_param_mask(target_block) {
            removed.target_args += retain_mask(args, target_mask);
        }
    })
}

fn calc_block_param_mask(prog: &Program, block: Block, alive: &HashSet<Value>) -> Option<FixedBitSet> {
    let params = &prog.get_block(block).params;

    let mut used = FixedBitSet::with_capacity(params.len());
    for (i, &param) in params.iter().enumerate() {
        used.set(i, alive.contains(&param.into()));
    }

    if used.count_ones(..) == used.len() {
        None
    } else {
        Some(used)
    }
}

#[must_use]
fn retain_mask<T: Debug>(values: &mut Vec<T>, mask: &FixedBitSet) -> usize {
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
        let &Removed { slots, instrs, func_params, call_args, call_args_undef, block_params, target_args } = self;
        slots + instrs + func_params + call_args + call_args_undef + block_params + target_args
    }
}