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
    // Return the program representing `fn main() -> int { unreachable(); }`
    pub fn new() -> Self {
        let mut prog = Self {
            nodes: Default::default(),
            types: Default::default(),
            entry: Node { i: Idx::sentinel(), ph: PhantomData },
        };

        let ty_int = prog.define_type_int(32);
        let term = prog.define_term(TerminatorInfo::Unreachable);
        let block = prog.define_block(BlockInfo {
            instructions: vec![],
            terminator: term,
        });
        let func = prog.define_func(FunctionInfo {
            ret_type: ty_int,
            entry: block,
            slots: Default::default(),
        });
        prog.entry = func;

        prog
    }

    pub fn define_type(&mut self, info: TypeInfo) -> Type {
        self.types.push(info)
    }

    pub fn define_type_int(&mut self, bits: u32) -> Type {
        self.define_type(TypeInfo::Integer { bits })
    }

    pub fn define_type_ptr(&mut self, inner: Type) -> Type {
        self.types.push(TypeInfo::Pointer { inner })
    }

    pub fn get_type(&self, ty: Type) -> &TypeInfo {
        &self.types[ty]
    }

    pub fn type_of_value(&self, value: Value) -> Type {
        match value {
            Value::Const(cst) => cst.ty,
            Value::Slot(slot) => self.get_slot(slot).ty,
            Value::Instr(instr) => self.get_instr(instr).ty(self),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum TypeInfo {
    Integer { bits: u32 },
    Pointer { inner: Type },
    Void,
}

impl TypeInfo {
    fn unwrap_ptr(self) -> Type {
        if let TypeInfo::Pointer {  inner} = self {
            inner
        } else {
            panic!("Expected a pointer type, got {:?}", self)
        }
    }
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
    pub ty: Type,
}

impl StackSlotInfo {
    pub fn new(inner_ty: Type, prog: &mut Program) -> Self {
        Self { inner_ty, ty: prog.define_type_ptr(inner_ty) }
    }
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

impl InstructionInfo {
    fn ty(&self, prog: &Program) -> Type {
        let addr = match self {
            InstructionInfo::Load { addr } => addr,
            InstructionInfo::Store { addr, .. } => addr,
        };
        prog.get_type(prog.type_of_value(*addr)).unwrap_ptr()
    }
}

#[derive(Debug)]
pub enum TerminatorInfo {
    Return { value: Value },
    Unreachable,
}

#[derive(Debug, Copy, Clone)]
pub enum Value {
    Const(Const),
    Slot(StackSlot),
    Instr(Instruction),
}

#[derive(Debug, Clone, Copy)]
pub struct Const {
    pub ty: Type,
    pub value: i32,
}
