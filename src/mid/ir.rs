use std::fmt::{Debug, Formatter, Display};
use std::marker::PhantomData;

use crate::util::arena::{Arena, ArenaSet, Idx};
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};

macro_rules! gen_node_and_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident],)*) => {
        $(
        pub type $node = Node<$info>;

        impl Debug for Node<$info> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?} {}", self.i, stringify!($node))
            }
        }
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
    [StackSlot, StackSlotInfo, define_slot, get_slot, get_slot_mut],
    [Block, BlockInfo, define_block, get_block, get_block_mut],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut],
];

//TODO think about debug printing Node, right now it's kind of crappy with PhantomData
//  also improve NodeType printing

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

impl<T> Hash for Node<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.i.hash(state)
    }
}

pub type Type = Idx<TypeInfo>;

#[derive(Debug)]
pub struct Program {
    //all values that may be used multiple times are stored as nodes
    nodes: Arena<NodeInfo>,
    //the types are stored separately in a set for interning
    types: ArenaSet<TypeInfo>,

    pub main: Function,
}

impl Program {
    // Return the program representing `fn main() -> int { unreachable(); }`
    pub fn new() -> Self {
        let mut prog = Self {
            nodes: Default::default(),
            types: Default::default(),
            main: Node { i: Idx::sentinel(), ph: PhantomData },
        };

        let ty_int = prog.define_type_int(32);
        let block = prog.define_block(BlockInfo {
            instructions: vec![],
            terminator: Terminator::Unreachable,
        });
        let func = prog.define_func(FunctionInfo {
            ret_type: ty_int,
            entry: block,
            slots: Default::default(),
        });
        prog.main = func;

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
    pub fn as_ptr(self) -> Option<Type> {
        if let TypeInfo::Pointer {  inner} = self {
            Some(inner)
        } else {
            None
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
        match self {
            InstructionInfo::Load { addr } => {
                prog.get_type(prog.type_of_value(*addr)).as_ptr()
                    .expect("load addr should have a pointer type")
            },
            InstructionInfo::Store { .. } => {
                panic!("Store doesn't have a return type")
            },
        }
    }
}

#[derive(Debug)]
pub enum Terminator {
    Return { value: Value },
    Unreachable,
}

impl Terminator {
    pub fn successors(&self) -> &[Block] {
        match self {
            Terminator::Return { .. } => &[],
            Terminator::Unreachable => &[],
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Value {
    Const(Const),
    Slot(StackSlot),
    Instr(Instruction),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Const {
    pub ty: Type,
    pub value: i32,
}

//Formatting related stuff
impl Program {
    /// Wrap a type as a Display value that recursively prints the type
    fn format_type(&self, ty: Type) -> impl Display + '_ {
        struct Wrapped<'a> {
            ty: Type,
            prog: &'a Program,
        }

        impl Display for Wrapped<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self.prog.get_type(self.ty) {
                    TypeInfo::Integer { bits } =>
                        write!(f, "i{}", bits),
                    TypeInfo::Pointer { inner } =>
                        write!(f, "*{}", self.prog.format_type(*inner)),
                    TypeInfo::Void =>
                        write!(f, "void"),
                }
            }
        }

        Wrapped { ty, prog: self }
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Program {{")?;
        writeln!(f, "  main: {:?}", self.main)?;

        writeln!(f, "  types:")?;
        for (ty, _) in &self.types {
            writeln!(f, "    {:?}: {}", ty, self.format_type(ty))?
        }

        for &func in &[self.main] {
            let func_info = self.get_func(func);
            writeln!(f, "  {:?}: () -> {} {{", func, self.format_type(func_info.ret_type))?;
            writeln!(f, "    slots:")?;
            for &slot in &func_info.slots {
                let slot_info = self.get_slot(slot);
                writeln!(f, "      {:?}: {}", slot, self.format_type(slot_info.ty))?;
            }
            writeln!(f, "    entry: {:?}", func_info.entry)?;

            let mut blocks_left = VecDeque::new();
            blocks_left.push_front(func_info.entry);

            while let Some(block) = blocks_left.pop_front() {
                let block_info = self.get_block(block);
                writeln!(f, "    {:?} {{", block)?;

                blocks_left.extend(block_info.terminator.successors());

                for &instr in &block_info.instructions {
                    let instr_info = self.get_instr(instr);
                    writeln!(f, "      {:?}: {:?}", instr, instr_info)?;
                }

                writeln!(f, "      term: {:?}", block_info.terminator)?;
                writeln!(f, "    }}")?;
            }
            writeln!(f, "  }}")?;
        }

        writeln!(f, "}}")?;
        Ok(())
    }
}