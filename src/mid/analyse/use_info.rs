use std::collections::VecDeque;

use indexmap::IndexSet;
use indexmap::map::{Entry, IndexMap};

use crate::mid::analyse::dom_info::{BlockPosition, DomPosition};
use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Program, Target, Terminator, Value};

#[derive(Debug, Copy, Clone)]
pub struct InstructionPos {
    pub func: Function,
    pub block: Block,
    pub instr: Instruction,
    pub instr_index: usize,
}

// TODO is this only ever used for terminators? If so, rename and implement `as_dom_pos`.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BlockPos {
    pub func: Function,
    pub block: Block,
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
    BinaryOperandLeft { pos: P },
    BinaryOperandRight { pos: P },

    //target of TupleFieldPtr
    TupleFieldPtrBase { pos: P },
    //target of ArrayIndexPtr
    ArrayIndexPtrBase { pos: P },
    //index of ArrayIndexPtr
    ArrayIndexPtrIndex { pos: P },

    CastValue { pos: P },
    BlackBoxValue { pos: P },

    //values passed to target as phi value
    TargetPhiValue {
        target_kind: TargetKind,
        phi_index: usize,
    },

    //branch terminator uses value as cond
    BranchCond {
        pos: BlockPos,
    },

    //return terminator uses value as return value
    ReturnValue {
        pos: BlockPos,
    },

    // TODO add "global" usage for functions with global_name set
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BlockUsage {
    pub target_kind: TargetKind,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TargetKind {
    EntryFrom(Function),
    JumpFrom(BlockPos),
    BranchTrueFrom(BlockPos),
    BranchFalseFrom(BlockPos),
}

#[derive(Debug, Copy, Clone)]
pub enum TargetSource {
    Entry(Function),
    Block(BlockPos),
}

#[derive(Debug)]
pub struct UseInfo {
    func_blocks: IndexMap<Function, IndexSet<Block>>,
    value_usages: IndexMap<Value, Vec<Usage>>,
    block_usages: IndexMap<Block, Vec<BlockUsage>>,
}

pub fn for_each_usage_in_instr<P: Copy>(pos: P, instr_info: &InstructionInfo, mut f: impl FnMut(Value, Usage<P>)) {
    try_for_each_usage_in_instr::<P, ()>(pos, instr_info, |value, usage| {
        f(value, usage);
        Ok(())
    }).unwrap();
}

// TODO maybe create additional "InstrUsage" enum for only these Usages?
pub fn try_for_each_usage_in_instr<P: Copy, E>(
    pos: P,
    instr_info: &InstructionInfo,
    mut f: impl FnMut(Value, Usage<P>) -> Result<(), E>,
) -> Result<(), E> {
    match instr_info {
        &InstructionInfo::Load { addr, ty: _ } => {
            f(addr, Usage::LoadAddr { pos })?;
        }
        &InstructionInfo::Store { addr, value, ty: _ } => {
            f(addr, Usage::StoreAddr { pos })?;
            f(value, Usage::StoreValue { pos })?;
        }
        &InstructionInfo::Call { target, ref args } => {
            f(target, Usage::CallTarget { pos })?;
            for (index, &arg) in args.iter().enumerate() {
                f(arg, Usage::CallArgument { pos, index })?;
            }
        }
        &InstructionInfo::Arithmetic { kind: _, left, right } |
        &InstructionInfo::Comparison { kind: _, left, right } => {
            f(left, Usage::BinaryOperandLeft { pos })?;
            f(right, Usage::BinaryOperandRight { pos })?;
        }
        &InstructionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
            f(base, Usage::TupleFieldPtrBase { pos })?;
        }
        &InstructionInfo::PointerOffSet { base, index, ty: _ } => {
            f(base, Usage::ArrayIndexPtrBase { pos })?;
            f(index, Usage::ArrayIndexPtrIndex { pos })?;
        }
        &InstructionInfo::Cast { ty: _, kind: _, value } => {
            f(value, Usage::CastValue { pos })?;
        }
        &InstructionInfo::BlackBox { value } => {
            f(value, Usage::BlackBoxValue { pos })?;
        }
    }
    Ok(())
}

impl InstructionPos {
    pub fn as_dom_pos(self) -> DomPosition {
        DomPosition::InBlock(self.func, self.block, BlockPosition::Instruction(self.instr_index))
    }
}

impl Usage {
    // returns None for
    pub fn as_dom_pos(self) -> DomPosition {
        match self {
            Usage::Main => {
                DomPosition::Global
            }
            Usage::LoadAddr { pos } |
            Usage::StoreAddr { pos } |
            Usage::StoreValue { pos } |
            Usage::CallTarget { pos } |
            Usage::CallArgument { pos, index: _, } |
            Usage::BinaryOperandLeft { pos } |
            Usage::BinaryOperandRight { pos } |
            Usage::TupleFieldPtrBase { pos } |
            Usage::ArrayIndexPtrBase { pos } |
            Usage::ArrayIndexPtrIndex { pos } |
            Usage::CastValue { pos } |
            Usage::BlackBoxValue { pos } => {
                pos.as_dom_pos()
            }
            Usage::TargetPhiValue { target_kind, phi_index: _ } => {
                target_kind.as_dom_pos()
            }
            Usage::BranchCond { pos } | Usage::ReturnValue { pos } => {
                DomPosition::InBlock(pos.func, pos.block, BlockPosition::Terminator)
            }
        }
    }
}

// TODO use visitor here as well
impl UseInfo {
    pub fn new(prog: &Program) -> Self {
        let mut info = UseInfo {
            func_blocks: Default::default(),
            value_usages: Default::default(),
            block_usages: Default::default(),
        };

        info.add_value_usage(Value::Func(prog.main), Usage::Main);

        let mut todo_funcs = VecDeque::new();
        let mut todo_blocks = VecDeque::new();
        let mut visited_funcs = IndexMap::new();

        todo_funcs.push_back(prog.main);

        while !todo_funcs.is_empty() | !todo_blocks.is_empty() {
            if let Some(func) = todo_funcs.pop_front() {
                match visited_funcs.entry(func) {
                    Entry::Occupied(_) => {
                        // we've already visited this function
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(IndexSet::default());

                        let func_info = prog.get_func(func);
                        let block_pos = BlockPos { func, block: func_info.entry.block };

                        todo_blocks.push_back(block_pos);
                        info.add_target_usages(&func_info.entry, TargetKind::EntryFrom(func))
                    }
                }
            }

            if let Some(block_pos) = todo_blocks.pop_front() {
                let BlockPos { func, block } = block_pos;
                if visited_funcs.get_mut(&func).unwrap().insert(block) {
                    let block_info = prog.get_block(block);

                    //instructions
                    for (instr_index, &instr) in block_info.instructions.iter().enumerate() {
                        let instr_info = prog.get_instr(instr);
                        let instr_pos = InstructionPos { func, block, instr, instr_index };

                        for_each_usage_in_instr(instr_pos, instr_info, |value, usage| {
                            info.add_value_usage(value, usage);

                            //if the usage is a function visit it too
                            if let Value::Func(func) = value {
                                todo_funcs.push_back(func);
                            }
                        });
                    }

                    //terminator
                    match &block_info.terminator {
                        Terminator::Jump { target } => {
                            info.add_target_usages(target, TargetKind::JumpFrom(block_pos));
                            todo_blocks.push_back(BlockPos { func, block: target.block });
                        }
                        Terminator::Branch { cond, true_target, false_target } => {
                            info.add_value_usage(*cond, Usage::BranchCond { pos: block_pos });
                            info.add_target_usages(true_target, TargetKind::BranchTrueFrom(block_pos));
                            todo_blocks.push_back(BlockPos { func, block: true_target.block });
                            info.add_target_usages(false_target, TargetKind::BranchFalseFrom(block_pos));
                            todo_blocks.push_back(BlockPos { func, block: false_target.block });
                        }
                        Terminator::Return { value } => {
                            info.add_value_usage(*value, Usage::ReturnValue { pos: block_pos });
                        }
                        Terminator::Unreachable => {}
                    }
                }
            }
        }

        assert!(info.func_blocks.is_empty());
        info.func_blocks = visited_funcs;
        info
    }

    fn add_value_usage(&mut self, value: Value, usage: Usage) {
        //we don't care about const
        if let Value::Const(_) = value { return; }

        self.value_usages.entry(value).or_default().push(usage);
    }

    fn add_block_usage(&mut self, block: Block, usage: BlockUsage) {
        self.block_usages.entry(block).or_default().push(usage);
    }

    fn add_target_usages(&mut self, target: &Target, target_kind: TargetKind) {
        for (phi_idx, &value) in target.phi_values.iter().enumerate() {
            self.add_value_usage(value, Usage::TargetPhiValue {
                target_kind,
                phi_index: phi_idx,
            })
        }

        self.add_block_usage(target.block, BlockUsage { target_kind });
    }

    pub fn replace_value_usages(&self, prog: &mut Program, old: Value, new: Value) -> usize {
        self.replace_value_usages_if(prog, old, new, |_| true)
    }

    //TODO figure out a way to make all of this a lot more typesafe
    pub fn replace_value_usages_if(&self, prog: &mut Program, old: Value, new: Value, mut filter: impl FnMut(Usage) -> bool) -> usize {
        assert_ne!(old, new);
        let count = &mut 0;

        for &usage in &self[old] {
            if !filter(usage) {
                continue;
            }

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
                Usage::BinaryOperandLeft { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Arithmetic { left, .. } |
                        InstructionInfo::Comparison { left, .. } => {
                            repl(count, left, old, new)
                        }
                        _ => unreachable!()
                    }
                }
                Usage::BinaryOperandRight { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Arithmetic { right, .. } |
                        InstructionInfo::Comparison { right, .. } => {
                            repl(count, right, old, new)
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
                Usage::CastValue { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::Cast { value, .. } =>
                            repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::BlackBoxValue { pos } => {
                    match prog.get_instr_mut(pos.instr) {
                        InstructionInfo::BlackBox { value } =>
                            repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::TargetPhiValue { target_kind, phi_index: phi_idx } => {
                    let target = target_kind.get_target_mut(prog);
                    repl(count, &mut target.phi_values[phi_idx], old, new);
                }
                Usage::BranchCond { pos } => {
                    match &mut prog.get_block_mut(pos.block).terminator {
                        Terminator::Branch { cond, .. } => repl(count, cond, old, new),
                        _ => unreachable!()
                    }
                }
                Usage::ReturnValue { pos } => {
                    match &mut prog.get_block_mut(pos.block).terminator {
                        Terminator::Return { value, .. } => repl(count, value, old, new),
                        _ => unreachable!()
                    }
                }
            }
        }

        *count
    }

    pub fn replace_block_usages(&self, prog: &mut Program, old: Block, new: Block) -> usize {
        assert_ne!(old, new);
        let count = &mut 0;

        for &usage in &self[old] {
            let BlockUsage { target_kind } = usage;
            let block = &mut target_kind.get_target_mut(prog).block;
            repl(count, block, old, new);
        }

        *count
    }

    pub fn function_only_used_as_call_target(&self, func: Function) -> bool {
        self[func].iter().all(|usage| {
            matches!(usage, Usage::CallTarget { .. })
        })
    }

    pub fn funcs(&self) -> impl Iterator<Item=Function> + '_ {
        self.func_blocks.keys().copied()
    }

    pub fn func_blocks(&self, func: Function) -> &IndexSet<Block> {
        self.func_blocks.get(&func).unwrap()
    }

    pub fn values(&self) -> impl Iterator<Item=Value> + '_ {
        self.value_usages.keys().copied()
    }

    pub fn instructions(&self) -> impl Iterator<Item=Instruction> + '_ {
        self.values().filter_map(|value| {
            match value {
                Value::Instr(instr) => Some(instr),
                _ => None,
            }
        })
    }

    pub fn blocks(&self) -> impl Iterator<Item=Block> + '_ {
        self.block_usages.keys().copied()
    }
}

impl TargetKind {
    pub fn func(self) -> Function {
        match self {
            TargetKind::EntryFrom(func) => func,
            TargetKind::JumpFrom(pos) => pos.func,
            TargetKind::BranchTrueFrom(pos) => pos.func,
            TargetKind::BranchFalseFrom(pos) => pos.func,
        }
    }

    pub fn source(self) -> TargetSource {
        match self {
            TargetKind::EntryFrom(func) => TargetSource::Entry(func),
            TargetKind::JumpFrom(pos) | TargetKind::BranchTrueFrom(pos) | TargetKind::BranchFalseFrom(pos) => {
                TargetSource::Block(pos)
            }
        }
    }

    pub fn get_target(self, prog: &Program) -> &Target {
        match self {
            TargetKind::EntryFrom(func) => &prog.get_func(func).entry,
            TargetKind::JumpFrom(pos) => {
                match &prog.get_block(pos.block).terminator {
                    Terminator::Jump { target } => target,
                    _ => panic!("Expected to find Terminator::Jump for TargetKind::Jump")
                }
            }
            TargetKind::BranchTrueFrom(pos) => {
                match &prog.get_block(pos.block).terminator {
                    Terminator::Branch { true_target, .. } => true_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchTrue")
                }
            }
            TargetKind::BranchFalseFrom(pos) => {
                match &prog.get_block(pos.block).terminator {
                    Terminator::Branch { false_target, .. } => false_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchFalse")
                }
            }
        }
    }

    pub fn get_target_mut(self, prog: &mut Program) -> &mut Target {
        match self {
            TargetKind::EntryFrom(func) => &mut prog.get_func_mut(func).entry,
            TargetKind::JumpFrom(pos) => {
                match &mut prog.get_block_mut(pos.block).terminator {
                    Terminator::Jump { target } => target,
                    _ => panic!("Expected to find Terminator::Jump for TargetKind::Jump")
                }
            }
            TargetKind::BranchTrueFrom(pos) => {
                match &mut prog.get_block_mut(pos.block).terminator {
                    Terminator::Branch { true_target, .. } => true_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchTrue")
                }
            }
            TargetKind::BranchFalseFrom(pos) => {
                match &mut prog.get_block_mut(pos.block).terminator {
                    Terminator::Branch { false_target, .. } => false_target,
                    _ => panic!("Expected to find Terminator::Branch for TargetKind::BranchFalse")
                }
            }
        }
    }

    pub fn as_dom_pos(self) -> DomPosition {
        match self {
            TargetKind::EntryFrom(func) => DomPosition::FuncEntry(func),
            TargetKind::JumpFrom(pos) | TargetKind::BranchTrueFrom(pos) | TargetKind::BranchFalseFrom(pos) => {
                DomPosition::InBlock(pos.func, pos.block, BlockPosition::Terminator)
            }
        }
    }
}

impl<T: Into<Value>> std::ops::Index<T> for UseInfo {
    type Output = [Usage];

    fn index(&self, index: T) -> &Self::Output {
        let index = index.into();
        self.value_usages.get(&index).map_or(&[], |v| v)
    }
}

impl std::ops::Index<Block> for UseInfo {
    type Output = [BlockUsage];

    fn index(&self, index: Block) -> &Self::Output {
        self.block_usages.get(&index).map_or(&[], |v| v)
    }
}

fn repl<T: Eq>(count: &mut usize, field: &mut T, old: T, new: T) {
    assert!(maybe_repl(count, field, old, new));
}

fn maybe_repl<T: Eq>(count: &mut usize, field: &mut T, old: T, new: T) -> bool {
    if *field == old {
        *field = new;
        *count += 1;
        true
    } else {
        false
    }
}