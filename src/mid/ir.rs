use std::fmt::Debug;
use std::marker::PhantomData;

use crate::util::arena::{Arena, ArenaSet, Idx};

macro_rules! gen_node_and_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident],)*) => {
        $(
        pub type $node = Node<$info>;
        )*

        #[derive(Debug)]
        enum NodeInfo {
            $(
            $node($info),
            )*
        }

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

gen_node_and_program_accessors![
    [Function, FunctionInfo, define_func, get_func, get_func_mut],
    [Block, BlockInfo, define_block, get_block, get_block_mut],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut],
    [Terminator, TerminatorInfo, define_term, get_term, get_term_mut],
    [StackSlot, StackSlotInfo, define_slot, get_slot, get_slot_mut],
];

//TODO think about debug printing Node, right now it's kind of crappy with PhantomData
//  also improve NodeType printing

//TODO implement Eq for Node

#[derive(Debug, Hash)]
pub struct Node<T> {
    i: Idx<NodeInfo>,
    ph: PhantomData<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self { i: self.i, ph: PhantomData }
    }
}

impl<T> Copy for Node<T> {}

impl<T> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.i == other.i
    }
}

impl<T> Eq for Node<T> {}

pub type Type = Idx<TypeInfo>;

#[derive(Debug)]
pub struct Program {
    nodes: Arena<NodeInfo>,
    types: ArenaSet<TypeInfo>,

    pub entry: Function,
}

impl Program {
    // Return the program representing `fn main() -> int { return 0; }`
    pub fn new() -> Self {
        let mut prog = Self {
            nodes: Default::default(),
            types: Default::default(),
            entry: Node { i: Idx::sentinel(), ph: PhantomData },
        };

        let int_ty = prog.define_type(TypeInfo::Integer { bits: 32 });
        let term = prog.define_term(TerminatorInfo::Return {
            value: Value::Const(Const { ty: int_ty, value: 0 })
        });
        let block = prog.define_block(BlockInfo {
            instructions: vec![],
            terminator: term,
        });
        prog.entry = prog.define_func(FunctionInfo {
            ret_type: int_ty,
            entry: block,
            slots: Default::default(),
        });

        prog
    }

    pub fn get_type_int(&mut self, bits: u32) -> Type {
        self.define_type(TypeInfo::Integer { bits })
    }

    pub fn define_type(&mut self, info: TypeInfo) -> Type {
        self.types.push(info)
    }

    pub fn get_type(&mut self, ty: Type) -> &TypeInfo {
        &self.types[ty]
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum TypeInfo {
    Integer { bits: u32 },
    Pointer { inner: Type },
}

#[derive(Debug)]
pub struct FunctionInfo {
    pub ret_type: Type,
    pub entry: Block,
    pub slots: Vec<StackSlot>,
}

#[derive(Debug)]
pub struct StackSlotInfo {
    pub inner_ty: Type,
}

#[derive(Debug)]
pub struct BlockInfo {
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub enum InstructionInfo {
    Load { addr: Value },
    Store { addr: Value, value: Value },
}

#[derive(Debug)]
pub enum TerminatorInfo {
    Return { value: Value },
    Unreachable,
}

#[derive(Debug, Copy, Clone)]
pub enum Value {
    Const(Const),
    StackSlot(StackSlot),
}

#[derive(Debug, Clone, Copy)]
pub struct Const {
    pub ty: Type,
    pub value: i32,
}
