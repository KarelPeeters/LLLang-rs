use std::fmt::Debug;
use std::marker::PhantomData;

use crate::util::arena::{Arena, Idx};

macro_rules! gen_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident],)*) => {
        impl Program {
        $(
            pub fn $def(&mut self, info: $info) -> $node {
                Node {
                    i: self.nodes.push(NodeInfo::$node(info)),
                    ph: PhantomData,
                }
            }

            pub fn $get(&self, node: $node) -> &$info {
                let node = &self.nodes[node.i];
                if let NodeInfo::$node(info) = node { info }
                else { panic!("Expected {:?}, got {:?}", std::any::type_name::<$info>(), node ) }
            }

            pub fn $get_mut(&mut self, node: $node) -> &mut $info {
                let node = &mut self.nodes[node.i];
                if let NodeInfo::$node(info) = node { info }
                else { panic!("Expected {:?}, got {:?}", std::any::type_name::<$info>(), node ) }
            }
        )*
        }
    }
}

pub type Function = Node<FunctionInfo>;
pub type Block = Node<BlockInfo>;
pub type Instruction = Node<InstructionInfo>;
pub type Terminator = Node<TerminatorInfo>;
pub type Variable = Node<VariableInfo>;

#[derive(Debug)]
enum NodeInfo {
    Function(FunctionInfo),
    Block(BlockInfo),
    Instruction(InstructionInfo),
    Terminator(TerminatorInfo),
    Variable(VariableInfo),
}

gen_program_accessors![
    [Function, FunctionInfo, define_func, get_func, get_func_mut],
    [Block, BlockInfo, define_block, get_block, get_block_mut],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut],
    [Terminator, TerminatorInfo, define_term, get_term, get_term_mut],
    [Variable, VariableInfo, define_var, get_var, get_var_mut],
];

#[derive(Debug)]
pub struct Node<T> {
    i: Idx<NodeInfo>,
    ph: PhantomData<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self { i: self.i, ph: PhantomData }
    }
}

impl <T> Copy for Node<T> {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Type {
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Program {
    nodes: Arena<NodeInfo>,

    pub entry: Function,
}

impl Program {
    // Return the program representing `fn main() -> int { return 0; }`
    pub fn new() -> Self {
        let mut prog = Self {
            nodes: Default::default(),
            entry: Node { i: Arena::sentinel(), ph: PhantomData },
        };

        let term = prog.define_term(TerminatorInfo::Return {
            value: Value::Const(Const { ty: Type::Int, value: 0 })
        });
        let block = prog.define_block(BlockInfo {
            instructions: vec![],
            terminator: term,
        });
        prog.entry = prog.define_func(FunctionInfo {
            ret_type: Type::Int,
            entry: block,
        });

        prog
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
