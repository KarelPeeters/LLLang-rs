use std::collections::{HashSet, VecDeque};

use indexmap::map::IndexMap;

use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Program, Target, Terminator, Value};

//TODO figure out a way to fake type safety here, eg guarantee that the linked instruction is indeed
// a call or a load or whatever
//TODO maybe write a specialized version that only cares about specific usages for certain passes?
// eg. slot_to_phi only cares about slots
//TODO try to unify some of this code with gc
#[derive(Debug, Copy, Clone)]
pub enum Usage {
    //program main
    Main,
    //address in load or store
    Addr {
        func: Function,
        block: Block,
        instr: Instruction,
    },
    //store value
    StoreValue {
        func: Function,
        block: Block,
        instr: Instruction,
    },
    //call target
    CallTarget {
        func: Function,
        block: Block,
        instr: Instruction,
    },
    //call argument
    CallArgument {
        func: Function,
        block: Block,
        instr: Instruction,
        index: usize,
    },
    //operand in binary operation
    BinaryOperand {
        func: Function,
        block: Block,
        instr: Instruction,
    },
    //target of subptr
    SubPtrTarget {
        func: Function,
        block: Block,
        instr: Instruction,
    },
    //values passed to target as phi value
    TargetPhiValue {
        func: Function,
        from_block: Block,
        target_index: TargetIndex,
        phi_index: usize,
    },
    //branch terminator uses value as cond
    BranchCond {
        func: Function,
        from_block: Block,
    },
    //return terminator uses value as return value
    ReturnValue {
        func: Function,
        from_block: Block,
    },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TargetIndex {
    Jump,
    BranchTrue,
    BranchFalse,
}

#[derive(Debug)]
pub struct UseInfo {
    usages: IndexMap<Value, Vec<Usage>>,
}

pub fn for_each_usage_in_instr<F: FnMut(Value, Usage)>(
    func: Function,
    block: Block,
    instr: Instruction,
    instr_info: &InstructionInfo,
    mut f: F,
) {
    match instr_info {
        &InstructionInfo::Load { addr } => {
            f(addr, Usage::Addr { func, block, instr })
        }
        &InstructionInfo::Store { addr, value } => {
            f(addr, Usage::Addr { func, block, instr });
            f(value, Usage::StoreValue { func, block, instr });
        }
        &InstructionInfo::Call { target, ref args } => {
            f(target, Usage::CallTarget { func, block, instr });
            for (index, &arg) in args.iter().enumerate() {
                f(arg, Usage::CallArgument { func, block, instr, index });
            }
        }
        &InstructionInfo::Arithmetic { kind: _, left, right } |
        &InstructionInfo::Comparison { kind: _, left, right } => {
            f(left, Usage::BinaryOperand { func, block, instr });
            f(right, Usage::BinaryOperand { func, block, instr });
        }
        &InstructionInfo::TupleFieldPtr { base, index: _, result_ty: _ } => {
            f(base, Usage::SubPtrTarget { func, instr, block });
        }
    }
}

impl UseInfo {
    pub fn new(prog: &Program) -> Self {
        let mut info = UseInfo { usages: Default::default() };

        info.add_usage(Value::Func(prog.main), Usage::Main);

        let mut todo_funcs = VecDeque::new();
        let mut todo_blocks = VecDeque::new();
        let mut visited_funcs = HashSet::new();
        let mut visited_blocks = HashSet::new();

        todo_funcs.push_back(prog.main);

        while !todo_funcs.is_empty() | !todo_blocks.is_empty() {
            if let Some(func) = todo_funcs.pop_front() {
                if visited_funcs.insert(func) {
                    let func_info = prog.get_func(func);
                    todo_blocks.push_back((func, func_info.entry))
                }
            }

            if let Some((func, block)) = todo_blocks.pop_front() {
                if visited_blocks.insert(block) {
                    let block_info = prog.get_block(block);

                    //instructions
                    for &instr in &block_info.instructions {
                        let instr_info = prog.get_instr(instr);

                        for_each_usage_in_instr(func, block, instr, instr_info, |value, usage| {
                            info.add_usage(value, usage);

                            //if the usage is a function visit it too
                            if let Value::Func(func) = value {
                                todo_funcs.push_back(func);
                            }
                        });
                    }

                    //terminator
                    match &block_info.terminator {
                        Terminator::Jump { target } => {
                            info.add_target_usages(func, block, target, TargetIndex::Jump);
                            todo_blocks.push_back((func, target.block));
                        }
                        Terminator::Branch { cond, true_target, false_target } => {
                            info.add_usage(*cond, Usage::BranchCond { func, from_block: block });
                            info.add_target_usages(func, block, true_target, TargetIndex::BranchTrue);
                            todo_blocks.push_back((func, true_target.block));
                            info.add_target_usages(func, block, false_target, TargetIndex::BranchFalse);
                            todo_blocks.push_back((func, false_target.block));
                        }
                        Terminator::Return { value } => {
                            info.add_usage(*value, Usage::ReturnValue { func, from_block: block });
                        }
                        Terminator::Unreachable => {}
                    }
                }
            }
        }

        info
    }

    fn add_usage(&mut self, value: Value, usage: Usage) {
        //we don't care about const
        if let Value::Const(_) = value { return; }

        self.usages.entry(value).or_default().push(usage);
    }

    fn add_target_usages(&mut self, func: Function, block: Block, target: &Target, target_idx: TargetIndex) {
        for (phi_idx, &value) in target.phi_values.iter().enumerate() {
            self.add_usage(value, Usage::TargetPhiValue {
                func,
                from_block: block,
                target_index: target_idx,
                phi_index: phi_idx,
            })
        }
    }

    //TODO figure out a way to make all of this a lot more typesafe
    pub fn replace_usages(&self, prog: &mut Program, old: Value, new: Value) -> usize {
        debug_assert_ne!(old, new);

        fn repl(count: &mut usize, field: &mut Value, old: Value, new: Value) {
            debug_assert!(maybe_repl(count, field, old, new))
        }

        fn maybe_repl(count: &mut usize, field: &mut Value, old: Value, new: Value) -> bool {
            if *field == old {
                *field = new;
                *count += 1;
                true
            } else {
                false
            }
        }

        let count = &mut 0;

        for &usage in &self[old] {
            match usage {
                Usage::Main => {
                    if let Value::Func(new) = new {
                        prog.main = new;
                        *count += 1;
                    } else {
                        //TODO remove this once prog.main is a value
                        panic!("Replacing main func not yet supported")
                    }
                }
                Usage::Addr { instr, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Load { addr } => repl(count, addr, old, new),
                        InstructionInfo::Store { addr, .. } => repl(count, addr, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::StoreValue { instr, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Store { value, .. } => repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::CallTarget { instr, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Call { target, .. } => repl(count, target, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::CallArgument { instr, index, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Call { args, .. } =>
                            repl(count, &mut args[index], old, new),
                        _ => unreachable!()
                    }
                }
                Usage::BinaryOperand { instr, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Arithmetic { left, right, .. } |
                        InstructionInfo::Comparison { left, right, .. } => {
                            let mut replaced_any = false;
                            replaced_any |= maybe_repl(count, left, old, new);
                            replaced_any |= maybe_repl(count, right, old, new);
                            debug_assert!(replaced_any);
                        }
                        _ => unreachable!()
                    }
                }
                Usage::SubPtrTarget { instr, .. } => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::TupleFieldPtr { base, .. } =>
                            repl(count, base, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::TargetPhiValue { from_block, target_index: target_idx, phi_index: phi_idx, .. } => {
                    let block_info = prog.get_block_mut(from_block);

                    let target = terminator_target_by_index_mut(&mut block_info.terminator, target_idx);
                    repl(count, &mut target.phi_values[phi_idx], old, new);
                }
                Usage::BranchCond { from_block, .. } => {
                    match &mut prog.get_block_mut(from_block).terminator {
                        Terminator::Branch { cond, .. } => repl(count, cond, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::ReturnValue { from_block, .. } => {
                    match &mut prog.get_block_mut(from_block).terminator {
                        Terminator::Return { value, .. } => repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
            }
        }

        *count
    }
}

pub fn terminator_target_by_index(term: &Terminator, index: TargetIndex) -> &Target {
    match term {
        Terminator::Jump { target } => {
            assert_eq!(index, TargetIndex::Jump, "Jump only has Jump target");
            target
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            match index {
                TargetIndex::Jump => panic!("Branch doesn't have Jump target"),
                TargetIndex::BranchTrue => true_target,
                TargetIndex::BranchFalse => false_target,
            }
        }
        Terminator::Return { .. } => panic!("Return doesn't have any targets"),
        Terminator::Unreachable => panic!("Unreachable doesn't have any targets"),
    }
}

pub fn terminator_target_by_index_mut(term: &mut Terminator, index: TargetIndex) -> &mut Target {
    match term {
        Terminator::Jump { target } => {
            assert_eq!(index, TargetIndex::Jump, "Jump only has Jump target");
            target
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            match index {
                TargetIndex::Jump => panic!("Branch doesn't have Jump target"),
                TargetIndex::BranchTrue => true_target,
                TargetIndex::BranchFalse => false_target,
            }
        }
        Terminator::Return { .. } => panic!("Return doesn't have any targets"),
        Terminator::Unreachable => panic!("Unreachable doesn't have any targets"),
    }
}

static EMPTY_USAGE_VEC: Vec<Usage> = Vec::new();

impl std::ops::Index<Value> for UseInfo {
    type Output = Vec<Usage>;

    fn index(&self, index: Value) -> &Self::Output {
        self.usages.get(&index).unwrap_or(&EMPTY_USAGE_VEC)
    }
}