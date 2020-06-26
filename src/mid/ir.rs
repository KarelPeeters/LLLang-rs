use std::collections::{HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use crate::util::arena::{Arena, ArenaSet, Idx};

macro_rules! gen_node_and_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident, $mul:ident],)*) => {
        $(
        pub type $node = Idx<$info>;

        impl Debug for $node {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                write!(f, "<{}> {}", self.i, stringify!($node))
            }
        }
        )*

        #[derive(Debug, Default)]
        pub struct Arenas {
            $(
            pub $mul: Arena<$info>,
            )*
        }

        impl Arenas {
            fn total_node_count(&self) -> usize {
                0 $(+ self.$mul.len())*
            }
        }

        impl Program {
        $(
            pub fn $def(&mut self, info: $info) -> $node {
                self.nodes.$mul.push(info)
            }

            #[allow(dead_code)]
            pub fn $get(&self, node: $node) -> &$info {
                &self.nodes.$mul[node]
            }

            #[allow(dead_code)]
            pub fn $get_mut(&mut self, node: $node) -> &mut $info {
                &mut self.nodes.$mul[node]
            }
        )*
        }
    }
}

gen_node_and_program_accessors![
    [Function, FunctionInfo, define_func, get_func, get_func_mut, funcs],
    [Parameter, ParameterInfo, define_param, get_param, get_param_mut, params],
    [StackSlot, StackSlotInfo, define_slot, get_slot, get_slot_mut, slots],
    [Block, BlockInfo, define_block, get_block, get_block_mut, blocks],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut, instrs],
    [Extern, ExternInfo, define_ext, get_ext, get_ext_mut, exts],
    [Data, DataInfo, define_data, get_data, get_data_mut, datas],
];

pub type Type = Idx<TypeInfo>;

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}> Type", self.i)
    }
}

#[derive(Debug)]
pub struct Program {
    //all values that may be used multiple times are stored as nodes
    pub nodes: Arenas,
    //the types are stored separately in a set for interning
    types: ArenaSet<TypeInfo>,

    //predefined types
    ty_bool: Type,
    ty_void: Type,

    pub main: Function,
}

impl Program {
    // Return the program representing `fn main() -> int { unreachable(); }`
    pub fn new() -> Self {
        let mut types = ArenaSet::default();
        let ty_bool = types.push(TypeInfo::Integer { bits: 1 });
        let ty_void = types.push(TypeInfo::Void);

        let mut prog = Self {
            nodes: Default::default(),
            types,
            ty_bool,
            ty_void,
            main: Idx::sentinel(),
        };

        let ty_int = prog.define_type_int(32);
        let func_ty = FunctionType { params: Vec::new(), ret: ty_int };
        let func = FunctionInfo::new(func_ty, &mut prog);
        let func = prog.define_func(func);
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

    pub fn define_type_func(&mut self, func_ty: FunctionType) -> Type {
        self.types.push(TypeInfo::Func(func_ty))
    }

    pub fn type_bool(&self) -> Type {
        self.ty_bool
    }

    pub fn type_void(&self) -> Type {
        self.ty_void
    }

    pub fn get_type(&self, ty: Type) -> &TypeInfo {
        &self.types[ty]
    }

    pub fn type_of_value(&self, value: Value) -> Type {
        match value {
            Value::Undef(ty) => ty,
            Value::Const(cst) => cst.ty,
            Value::Func(func) => self.get_func(func).ty,
            Value::Param(param) => self.get_param(param).ty,
            Value::Slot(slot) => self.get_slot(slot).ty,
            Value::Instr(instr) => self.get_instr(instr).ty(self),
            Value::Extern(ext) => self.get_ext(ext).ty,
            Value::Data(data) => self.get_data(data).ty,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeInfo {
    Void,
    Integer { bits: u32 },
    Pointer { inner: Type },
    Func(FunctionType),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionType {
    pub params: Vec<Type>,
    pub ret: Type,
}

impl TypeInfo {
    pub fn unwrap_int(&self) -> Option<u32> {
        if let TypeInfo::Integer { bits } = self {
            Some(*bits)
        } else {
            None
        }
    }

    pub fn unwrap_ptr(&self) -> Option<Type> {
        if let TypeInfo::Pointer { inner } = self {
            Some(*inner)
        } else {
            None
        }
    }

    pub fn as_func(&self) -> Option<&FunctionType> {
        if let TypeInfo::Func(func_ty) = self {
            Some(func_ty)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct FunctionInfo {
    pub ty: Type,
    pub func_ty: FunctionType,
    pub global_name: Option<String>,
    pub entry: Block,
    pub params: Vec<Parameter>,
    pub slots: Vec<StackSlot>,
}

impl FunctionInfo {
    /// Create a new function with the given type. The entry blocks starts out empty and unreachable.
    pub fn new(func_ty: FunctionType, prog: &mut Program) -> Self {
        let ty = prog.define_type_func(func_ty.clone());
        let entry = prog.define_block(BlockInfo {
            instructions: vec![],
            terminator: Terminator::Unreachable,
        });

        Self {
            ty,
            func_ty,
            global_name: None,
            entry,
            params: Vec::new(),
            slots: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct ParameterInfo {
    pub ty: Type,
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
    Call { target: Value, args: Vec<Value> },
    Binary { kind: BinaryOp, left: Value, right: Value },
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
}

impl InstructionInfo {
    fn ty(&self, prog: &Program) -> Type {
        match self {
            InstructionInfo::Load { addr } => {
                prog.get_type(prog.type_of_value(*addr)).unwrap_ptr()
                    .expect("load addr should have a pointer type")
            },
            InstructionInfo::Store { .. } => {
                prog.type_void()
            },
            InstructionInfo::Call { target, .. } => {
                prog.get_type(prog.type_of_value(*target)).as_func()
                    .expect("call target should have a function type")
                    .ret
            }
            InstructionInfo::Binary { kind, left, .. } => {
                match kind {
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div |
                    BinaryOp::Mod =>
                        prog.type_of_value(*left),
                    BinaryOp::Eq | BinaryOp::Neq =>
                        prog.ty_bool,
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Terminator {
    Jump { target: Block },
    //TODO figure out a way to get named fields here
    Branch { cond: Value, targets: [Block; 2] },
    Return { value: Value },
    Unreachable,
}

impl Terminator {
    pub fn successors(&self) -> &[Block] {
        match self {
            Terminator::Jump { target } => std::slice::from_ref(target),
            Terminator::Branch { targets, .. } => targets,
            Terminator::Return { .. } => &[],
            Terminator::Unreachable => &[],
        }
    }
}

//TODO undef, func, param, slot, extern and data can all be "marked" const I think
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Value {
    Undef(Type),
    Const(Const),
    Func(Function),
    Param(Parameter),
    Slot(StackSlot),
    Instr(Instruction),
    Extern(Extern),
    Data(Data),
}

#[derive(Debug)]
pub struct DataInfo {
    pub ty: Type,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Const {
    pub ty: Type,
    pub value: i32,
}

impl Const {
    pub const fn new(ty: Type, value: i32) -> Self {
        Const { ty, value }
    }
}

#[derive(Debug, Clone)]
pub struct ExternInfo {
    pub name: String,
    pub ty: Type,
}

//Visitors
//TODO think about how to structure this, right now it's kind of crappy and non consistent
impl Program {
    /// Visit all the blocks reachable from the entry of `func`
    pub fn try_visit_blocks<E, F: FnMut(Block) -> Result<(), E>>(&self, func: Function, mut f: F) -> Result<(), E> {
        let func = self.get_func(func);

        let mut blocks_left = VecDeque::new();
        let mut blocks_seen = HashSet::new();
        blocks_left.push_front(func.entry);

        while let Some(block) = blocks_left.pop_front() {
            if !blocks_seen.insert(block) { continue }

            f(block)?;

            let block_info = self.get_block(block);
            blocks_left.extend(block_info.terminator.successors());
        }

        Ok(())
    }

    /// Visit all the blocks reachable from the entry of `func`
    pub fn visit_blocks<F: FnMut(Block)>(&self, func: Function, mut f: F) {
        //change this to use ! once that's stable
        self.try_visit_blocks::<(), _>(func, |block| {
            f(block);
            Ok(())
        }).unwrap();
    }
}

//Formatting related stuff
impl Program {
    /// Wrap a type as a Display value that recursively prints the type
    pub fn format_type(&self, ty: Type) -> impl Display + '_ {
        struct Wrapped<'a> {
            ty: Type,
            prog: &'a Program,
        }

        impl Display for Wrapped<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match self.prog.get_type(self.ty) {
                    TypeInfo::Void =>
                        write!(f, "void"),
                    TypeInfo::Integer { bits } =>
                        write!(f, "i{}", bits),
                    TypeInfo::Pointer { inner } =>
                        write!(f, "&{}", self.prog.format_type(*inner)),
                    TypeInfo::Func(func_ty) => {
                        write!(f, "(")?;
                        for (i, &param_ty) in func_ty.params.iter().enumerate() {
                            if i > 0 { write!(f, ", ")?; }
                            write!(f, "{}", self.prog.format_type(param_ty))?;
                        }
                        write!(f, ") -> {}", self.prog.format_type(func_ty.ret))?;
                        Ok(())
                    }
                }
            }
        }

        Wrapped { ty, prog: self }
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Program (nodes: {}) {{", self.nodes.total_node_count())?;
        writeln!(f, "  main: {:?}", self.main)?;

        writeln!(f, "  types:")?;
        for (ty, _) in &self.types {
            writeln!(f, "    {:?}: {}", ty, self.format_type(ty))?
        }

        for (func, func_info) in &self.nodes.funcs {
            writeln!(f, "  {:?}: {} {{", func, self.format_type(func_info.ty))?;
            writeln!(f, "    params:")?;
            for &param in &func_info.params {
                let param_info = self.get_param(param);
                writeln!(f, "      {:?}: {}", param, self.format_type(param_info.ty))?;
            }
            writeln!(f, "    slots:")?;
            for &slot in &func_info.slots {
                let slot_info = self.get_slot(slot);
                writeln!(f, "      {:?}: {}", slot, self.format_type(slot_info.ty))?;
            }
            writeln!(f, "    entry: {:?}", func_info.entry)?;

            self.try_visit_blocks(func, |block| {
                let block_info = self.get_block(block);
                writeln!(f, "    {:?} {{", block)?;

                for &instr in &block_info.instructions {
                    let instr_info = self.get_instr(instr);
                    writeln!(f, "      {:?}: {:?}", instr, instr_info)?;
                }

                writeln!(f, "      term: {:?}", block_info.terminator)?;
                writeln!(f, "    }}")?;

                Ok(())
            })?;
            writeln!(f, "  }}")?;
        };

        writeln!(f, "}}")?;
        Ok(())
    }
}