use indexmap::map::IndexMap;

use crate::mid::ir::{Block, Instruction, InstructionInfo, Program, Target, Terminator, Value};

//TODO figure out a way to fake type safety here, eg guarantee that the linked instruction is indeed
// a call or a load or whatever
//TODO maybe write a specialized version that only cares about specific usages for certain passes?
// eg. slot_to_phi only cares about slots
//TODO try to unify some of this code with gc
#[derive(Debug, Copy, Clone)]
pub enum Usage {
    //program main
    Main,
    //address in load or store instruction
    Addr(Instruction, Block),
    //used as call target
    CallTarget(Instruction, Block),
    //used as a general operand in an instruction
    Operand(Instruction, Block),
    //values passed to target as phi value
    TargetPhiValue(Block),
    //branch terminator uses value as cond
    BranchCond(Block),
    //return terminator uses value as return value
    ReturnValue(Block),
}

#[derive(Debug)]
pub struct UseInfo {
    usages: IndexMap<Value, Vec<Usage>>,
}

impl UseInfo {
    pub fn new(prog: &Program) -> Self {
        let mut info = UseInfo { usages: Default::default() };

        info.add_usage(Value::Func(prog.main), Usage::Main);

        for (block, block_info) in &prog.nodes.blocks {
            for &instr in &block_info.instructions {
                match prog.get_instr(instr) {
                    &InstructionInfo::Freeze { value } => {
                        info.add_usage(value, Usage::Operand(instr, block))
                    }
                    &InstructionInfo::Load { addr } => {
                        info.add_usage(addr, Usage::Addr(instr, block));
                    }
                    &InstructionInfo::Store { addr, value } => {
                        info.add_usage(addr, Usage::Addr(instr, block));
                        info.add_usage(value, Usage::Operand(instr, block));
                    }
                    InstructionInfo::Call { target, args } => {
                        info.add_usage(*target, Usage::CallTarget(instr, block));
                        for &arg in args {
                            info.add_usage(arg, Usage::Operand(instr, block));
                        }
                    }
                    &InstructionInfo::Arithmetic { kind: _, left, right } |
                    &InstructionInfo::Logical { kind: _, left, right } => {
                        info.add_usage(left, Usage::Operand(instr, block));
                        info.add_usage(right, Usage::Operand(instr, block));
                    }
                    &InstructionInfo::StructSubPtr { target, index: _, result_ty: _ } => {
                        info.add_usage(target, Usage::Operand(instr, block));
                    }
                }
            }

            match &block_info.terminator {
                Terminator::Jump { target } => {
                    info.add_target_usages(block, target);
                }
                Terminator::Branch { cond, true_target, false_target } => {
                    info.add_usage(*cond, Usage::BranchCond(block));
                    info.add_target_usages(block, true_target);
                    info.add_target_usages(block, false_target);
                }
                Terminator::Return { value } => {
                    info.add_usage(*value, Usage::ReturnValue(block));
                }
                Terminator::Unreachable => {}
            }
        }
        info
    }

    fn add_usage(&mut self, value: Value, usage: Usage) {
        //we don't care about const
        if let Value::Const(_) = value { return; }

        self.usages.entry(value).or_default().push(usage);
    }

    fn add_target_usages(&mut self, block: Block, target: &Target) {
        for &value in &target.phi_values {
            self.add_usage(value, Usage::TargetPhiValue(block))
        }
    }

    //TODO figure out a way to make all of this a lot more typesafe
    pub fn replace_usages(&self, prog: &mut Program, old: Value, new: Value) {
        debug_assert_ne!(old, new);

        fn repl(field: &mut Value, old: Value, new: Value) {
            debug_assert!(maybe_repl(field, old, new))
        }

        fn maybe_repl(field: &mut Value, old: Value, new: Value) -> bool {
            if *field == old {
                *field = new;
                true
            } else {
                false
            }
        }

        for &usage in &self[old] {
            match usage {
                Usage::Main => {
                    if let Value::Func(new) = new {
                        prog.main = new;
                    } else {
                        //TODO remove this once prog.main is a value
                        panic!("Replacing main func not yet supported")
                    }
                }
                Usage::Addr(instr, _) => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Load { addr } => repl(addr, old, new),
                        InstructionInfo::Store { addr, .. } => repl(addr, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::CallTarget(instr, _) => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Call { target, .. } => repl(target, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::Operand(instr, _) => {
                    match prog.get_instr_mut(instr) {
                        InstructionInfo::Store { value, .. } => repl(value, old, new),
                        InstructionInfo::Call { args, .. } => {
                            let mut replaced_any = false;
                            for arg in args {
                                replaced_any |= maybe_repl(arg, old, new);
                            }
                            debug_assert!(replaced_any);
                        }
                        InstructionInfo::Arithmetic { left, right, .. } |
                        InstructionInfo::Logical { left, right, .. } => {
                            let mut replaced_any = false;
                            replaced_any |= maybe_repl(left, old, new);
                            replaced_any |= maybe_repl(right, old, new);
                            debug_assert!(replaced_any);
                        }
                        _ => unreachable!()
                    }
                }
                Usage::TargetPhiValue(block) => {
                    let block_info = prog.get_block_mut(block);
                    let mut replaced_any = false;
                    block_info.terminator.for_each_target_mut(|target| {
                        for phi_value in &mut target.phi_values {
                            replaced_any |= maybe_repl(phi_value, old, new)
                        }
                    });
                    debug_assert!(replaced_any)
                }
                Usage::BranchCond(block) => {
                    match &mut prog.get_block_mut(block).terminator {
                        Terminator::Branch { cond, .. } => repl(cond, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::ReturnValue(block) => {
                    match &mut prog.get_block_mut(block).terminator {
                        Terminator::Return { value, .. } => repl(value, old, new),
                        _ => unreachable!()
                    }
                }
            }
        }
    }
}

static EMPTY_USAGE_VEC: Vec<Usage> = Vec::new();

impl std::ops::Index<Value> for UseInfo {
    type Output = Vec<Usage>;

    fn index(&self, index: Value) -> &Self::Output {
        self.usages.get(&index).unwrap_or(&EMPTY_USAGE_VEC)
    }
}