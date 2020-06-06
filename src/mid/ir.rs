use std::fmt::Debug;

use crate::util::arena::{Arena, Idx};

pub type Function = Idx<FunctionInfo>;
pub type Block = Idx<BlockInfo>;
pub type Instruction = Idx<InstructionInfo>;
pub type Terminator = Idx<TerminatorInfo>;
pub type Variable = Idx<VariableInfo>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Type {
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Program {
    functions: Arena<FunctionInfo>,
    blocks: Arena<BlockInfo>,
    instructions: Arena<InstructionInfo>,
    terminators: Arena<TerminatorInfo>,
    variables: Arena<VariableInfo>,

    pub entry: Function,
}

impl Program {
    // Return the program representing `fn main() -> int { return 0; }`
    pub fn new() -> Self {
        let mut functions: Arena<FunctionInfo> = Default::default();
        let mut blocks: Arena<BlockInfo> = Default::default();
        let mut terminators: Arena<TerminatorInfo> = Default::default();

        let entry_func = functions.push(FunctionInfo {
            ret_type: Type::Int,
            entry: blocks.push(BlockInfo {
                instructions: vec![],
                terminator: terminators.push(TerminatorInfo::Return {
                    value: Value::Const(Const { ty: Type::Int, value: 0 }),
                }),
            }),
        });

        Self {
            functions,
            blocks,
            instructions: Default::default(),
            terminators,
            variables: Default::default(),

            entry: entry_func,
        }
    }

    pub fn define_func(&mut self, info: FunctionInfo) -> Function {
        self.functions.push(info)
    }

    pub fn define_block(&mut self, info: BlockInfo) -> Block {
        self.blocks.push(info)
    }

    pub fn define_terminator(&mut self, info: TerminatorInfo) -> Terminator {
        self.terminators.push(info)
    }

    pub fn func(&self, func: Function) -> &FunctionInfo {
        &self.functions[func]
    }

    pub fn block(&self, block: Block) -> &BlockInfo {
        &self.blocks[block]
    }

    pub fn term(&self, term: Terminator) -> &TerminatorInfo {
        &self.terminators[term]
    }

    pub fn func_mut(&mut self, func: Function) -> &mut FunctionInfo {
        &mut self.functions[func]
    }

    pub fn block_mut(&mut self, block: Block) -> &mut BlockInfo {
        &mut self.blocks[block]
    }

    pub fn term_mut(&mut self, term: Terminator) -> &mut TerminatorInfo {
        &mut self.terminators[term]
    }
}

#[derive(Debug)]
pub struct FunctionInfo {
    pub ret_type: Type,
    pub entry: Block,
}

#[derive(Debug)]
pub struct VariableInfo {
    ty: Type,
}

#[derive(Debug)]
pub struct VariableId {
    index: usize,
}

#[derive(Debug)]
pub struct BlockInfo {
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub enum InstructionInfo {}

#[derive(Debug)]
pub enum TerminatorInfo {
    Return { value: Value },
    Unreachable,
}

#[derive(Debug)]
pub enum Value {
    Const(Const)
}

#[derive(Debug, Clone, Copy)]
pub struct Const {
    pub ty: Type,
    pub value: i32,
}
