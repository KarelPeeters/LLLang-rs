use std::collections::{HashSet, VecDeque};

use indexmap::map::IndexMap;

use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Program, Target, Terminator, Value};

#[derive(Debug, Copy, Clone)]
pub struct InstructionPos {
    pub func: Function,
    pub block: Block,
    pub instr: Instruction,
}

//TODO figure out a way to fake type safety here, eg guarantee that the linked instruction is indeed
// a call or a load or whatever
//TODO maybe write a specialized version that only cares about specific usages for certain passes?
// eg. slot_to_phi only cares about slots
//TODO try to unify some of this code with gc
//TODO maybe extract a subtype for all instruction operand usages
#[derive(Debug, Copy, Clone)]
pub enum Usage<P = InstructionPos> {
    //program main
    Main,

    //address in Load
    LoadAddr { pos: P },
    //address in Store
    StoreAddr { pos: P },
    //Store value
    StoreValue { pos: P },

    //Call target
    CallTarget { pos: P },
    //Call argument
    CallArgument {
        pos: P,
        index: usize,
    },

    //operand in Arithmetic or Comparison
    BinaryOperand { pos: P },

    //target of TupleFieldPtr
    TupleFieldPtrBase { pos: P },
    //target of ArrayIndexPtr
    ArrayIndexPtrBase { pos: P },
    //index of ArrayIndexPtr

    ArrayIndexPtrIndex { pos: P },
    //values passed to target as phi value

    TargetPhiValue {
        func: Function,
        target_kind: TargetKind,
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
pub enum TargetKind {
    Entry,
    Jump(Block),
    BranchTrue(Block),
    BranchFalse(Block),
}

#[derive(Debug)]
pub struct UseInfo {
    usages: IndexMap<Value, Vec<Usage>>,
}

pub fn for_each_usage_in_instr<P: Copy, F: FnMut(Value, Usage<P>)>(
    pos: P,
    instr_info: &InstructionInfo,
    mut f: F,
) {
    // match patterns in this function don't use .. since newly added fields could mean newly added usages!
    match instr_info {
        &InstructionInfo::Load { addr, ty: _ } => {
            f(addr, Usage::LoadAddr { pos })
        }
        &InstructionInfo::Store { addr, value, ty: _ } => {
            f(addr, Usage::StoreAddr { pos });
            f(value, Usage::StoreValue { pos });
        }
        &InstructionInfo::Call { target, ref args } => {
            f(target, Usage::CallTarget { pos });
            for (index, &arg) in args.iter().enumerate() {
                f(arg, Usage::CallArgument { pos, index });
            }
        }
        &InstructionInfo::Arithmetic { kind: _, left, right } |
        &InstructionInfo::Comparison { kind: _, left, right } => {
            f(left, Usage::BinaryOperand { pos });
            f(right, Usage::BinaryOperand { pos });
        }
        &InstructionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
            f(base, Usage::TupleFieldPtrBase { pos });
        }
        &InstructionInfo::PointerOffSet { base, index, ty: _ } => {
            f(base, Usage::ArrayIndexPtrBase { pos });
            f(index, Usage::ArrayIndexPtrIndex { pos });
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

                    todo_blocks.push_back((func, func_info.entry.block));
                    info.add_target_usages(func, &func_info.entry, TargetKind::Entry)
                }
            }

            if let Some((func, block)) = todo_blocks.pop_front() {
                if visited_blocks.insert(block) {
                    let block_info = prog.get_block(block);

                    //instructions
                    for &instr in &block_info.instructions {
                        let instr_info = prog.get_instr(instr);
                        let pos = InstructionPos { func, block, instr };

                        for_each_usage_in_instr(pos, instr_info, |value, usage| {
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
                            info.add_target_usages(func, target, TargetKind::Jump(block));
                            todo_blocks.push_back((func, target.block));
                        }
                        Terminator::Branch { cond, true_target, false_target } => {
                            info.add_usage(*cond, Usage::BranchCond { func, from_block: block });
                            info.add_target_usages(func, true_target, TargetKind::BranchTrue(block));
                            todo_blocks.push_back((func, true_target.block));
                            info.add_target_usages(func, false_target, TargetKind::BranchFalse(block));
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

    fn add_target_usages(&mut self, func: Function, target: &Target, target_kind: TargetKind) {
        for (phi_idx, &value) in target.phi_values.iter().enumerate() {
            self.add_usage(value, Usage::TargetPhiValue {
                func,
                target_kind,
                phi_index: phi_idx,
            })
        }
    }

    //TODO figure out a way to make all of this a lot more typesafe
    pub fn replace_usages(&self, prog: &mut Program, old: Value, new: Value) -> usize {
        assert_ne!(old, new);

        fn repl(count: &mut usize, field: &mut Value, old: Value, new: Value) {
            assert!(maybe_repl(count, field, old, new));
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
                Usage::LoadAddr { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Load { addr, .. } => repl(count, addr, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::StoreAddr { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Store { addr, .. } => repl(count, addr, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::StoreValue { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Store { value, .. } => repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::CallTarget { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Call { target, .. } => repl(count, target, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::CallArgument { pos, index, .. } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Call { args, .. } =>
                            repl(count, &mut args[index], old, new),
                        _ => unreachable!()
                    }
                }
                Usage::BinaryOperand { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Arithmetic { left, right, .. } |
                        InstructionInfo::Comparison { left, right, .. } => {
                            let mut replaced_any = false;
                            replaced_any |= maybe_repl(count, left, old, new);
                            replaced_any |= maybe_repl(count, right, old, new);
                            assert!(replaced_any);
                        }
                        _ => unreachable!()
                    }
                }
                Usage::TupleFieldPtrBase { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::TupleFieldPtr { base, .. } =>
                            repl(count, base, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::ArrayIndexPtrBase { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::PointerOffSet { base, .. } =>
                            repl(count, base, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::ArrayIndexPtrIndex { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::PointerOffSet { index, .. } =>
                            repl(count, index, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::TargetPhiValue { func, target_kind, phi_index: phi_idx } => {
                    let target = target_kind.get_target_mut(prog, func);
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

impl TargetKind {
    pub fn get_target(self, prog: &Program, func: Function) -> &Target {
        match self {
            TargetKind::Entry => &prog.get_func(func).entry,
            TargetKind::Jump(block) => {
                match &prog.get_block(block).terminator {
                    Terminator::Jump { target } => target,
                    _ => panic!("Expected to find Terminator::Jump for TargetKind::Jump")
                }
            }
            TargetKind::BranchTrue(block) => {
                match &prog.get_block(block).terminator {
                    Terminator::Branch { true_target, .. } => true_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchTrue")
                }
            }
            TargetKind::BranchFalse(block) => {
                match &prog.get_block(block).terminator {
                    Terminator::Branch { false_target, .. } => false_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchFalse")
                }
            }
        }
    }

    pub fn get_target_mut(self, prog: &mut Program, func: Function) -> &mut Target {
        match self {
            TargetKind::Entry => &mut prog.get_func_mut(func).entry,
            TargetKind::Jump(block) => {
                match &mut prog.get_block_mut(block).terminator {
                    Terminator::Jump { target } => target,
                    _ => panic!("Expected to find Terminator::Jump for TargetKind::Jump")
                }
            }
            TargetKind::BranchTrue(block) => {
                match &mut prog.get_block_mut(block).terminator {
                    Terminator::Branch { true_target, .. } => true_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchTrue")
                }
            }
            TargetKind::BranchFalse(block) => {
                match &mut prog.get_block_mut(block).terminator {
                    Terminator::Branch { false_target, .. } => false_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchFalse")
                }
            }
        }
    }
}

static EMPTY_USAGE_VEC: Vec<Usage> = Vec::new();

impl<T: Into<Value>> std::ops::Index<T> for UseInfo {
    type Output = Vec<Usage>;

    fn index(&self, index: T) -> &Self::Output {
        let index = index.into();
        self.usages.get(&index).unwrap_or(&EMPTY_USAGE_VEC)
    }
}