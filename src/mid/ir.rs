use std::collections::{HashSet, VecDeque};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use crate::util::arena::{Arena, ArenaSet};

macro_rules! gen_node_and_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident, $mul:ident],)*) => {
        $(
        new_index_type!(pub $node);
        )*

        #[derive(Debug, Default)]
        pub struct Arenas {
            $(
            pub $mul: Arena<$node, $info>,
            )*
        }

        impl Arenas {
            pub fn total_node_count(&self) -> usize {
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
    [Phi, PhiInfo, define_phi, get_phi, get_phi_mut, phis],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut, instrs],
    [Extern, ExternInfo, define_ext, get_ext, get_ext_mut, exts],
    [Data, DataInfo, define_data, get_data, get_data_mut, datas],
];

new_index_type!(pub Type);

#[derive(Debug)]
pub struct Program {
    //TODO we've lost distinct indices! is there an easy way to get that back?
    //all values that may be used multiple times are stored as nodes
    pub nodes: Arenas,
    //TODO maybe look into adding a cell here so we can modify this when we have a &Program for usability
    //the types are stored separately in a set for interning
    types: ArenaSet<Type, TypeInfo>,

    //predefined types
    ty_void: Type,
    ty_ptr: Type,
    ty_bool: Type,
    ty_int: Type,

    //TODO change program to have multiple possible entries with arbitrary signatures instead
    //  partly for elegance but also because this is too limiting, all extern functions should be considered entry points
    pub main: Function,
}

impl Default for Program {
    /// Return the program representing `fn main() -> int { unreachable(); }`
    fn default() -> Self {
        let mut types = ArenaSet::default();
        let mut nodes = Arenas::default();

        let ty_void = types.push(TypeInfo::Void);
        let ty_ptr = types.push(TypeInfo::Pointer);
        let ty_bool = types.push(TypeInfo::Integer { bits: 1 });
        let ty_int = types.push(TypeInfo::Integer { bits: 32 });

        let main_func_ty = FunctionType { params: Vec::new(), ret: ty_int };
        let main_ty = types.push(TypeInfo::Func(main_func_ty.clone()));

        let block = nodes.blocks.push(BlockInfo::new());
        let entry = Target { block, phi_values: vec![] };
        let main_info = FunctionInfo::new_given_parts(main_func_ty, main_ty, entry);
        let main = nodes.funcs.push(main_info);

        Program { nodes, types, ty_void, ty_ptr, ty_bool, ty_int, main }
    }
}

impl Program {
    pub fn define_type(&mut self, info: TypeInfo) -> Type {
        self.types.push(info)
    }

    pub fn define_type_int(&mut self, bits: u32) -> Type {
        self.define_type(TypeInfo::Integer { bits })
    }

    pub fn define_type_func(&mut self, func_ty: FunctionType) -> Type {
        self.types.push(TypeInfo::Func(func_ty))
    }

    pub fn define_type_tuple(&mut self, tuple_ty: TupleType) -> Type {
        self.types.push(TypeInfo::Tuple(tuple_ty))
    }

    pub fn define_type_array(&mut self, array_ty: ArrayType) -> Type {
        self.types.push(TypeInfo::Array(array_ty))
    }

    pub fn ty_void(&self) -> Type {
        self.ty_void
    }

    pub fn ty_ptr(&self) -> Type {
        self.ty_ptr
    }

    pub fn ty_bool(&self) -> Type {
        self.ty_bool
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
            Value::Slot(_) => self.ty_ptr,
            Value::Phi(phi) => self.get_phi(phi).ty,
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
    Pointer,
    Func(FunctionType),
    Tuple(TupleType),
    Array(ArrayType),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionType {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TupleType {
    pub fields: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ArrayType {
    pub inner: Type,
    pub length: u32,
}

impl TypeInfo {
    pub fn unwrap_int(&self) -> Option<u32> {
        match self {
            &TypeInfo::Integer { bits } => Some(bits),
            _ => None,
        }
    }

    pub fn is_ptr(&self) -> bool {
        matches!(self, TypeInfo::Pointer)
    }

    pub fn unwrap_func(&self) -> Option<&FunctionType> {
        match self {
            TypeInfo::Func(func_ty) => Some(func_ty),
            _ => None,
        }
    }

    pub fn unwrap_tuple(&self) -> Option<&TupleType> {
        match self {
            TypeInfo::Tuple(tuple_ty) => Some(tuple_ty),
            _ => None,
        }
    }

    pub fn unwrap_array(&self) -> Option<&ArrayType> {
        match self {
            TypeInfo::Array(ty) => Some(ty),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct FunctionInfo {
    pub ty: Type,
    pub func_ty: FunctionType,
    pub global_name: Option<String>,
    pub debug_name: Option<String>,
    pub entry: Target,
    pub params: Vec<Parameter>,
    pub slots: Vec<StackSlot>,
}

impl FunctionInfo {
    /// Create a new function with the given type. The entry blocks starts out empty and unreachable.
    pub fn new(func_ty: FunctionType, prog: &mut Program) -> Self {
        let ty = prog.define_type_func(func_ty.clone());
        let block = prog.define_block(BlockInfo::new());
        let entry = Target { block, phi_values: vec![] };

        Self::new_given_parts(func_ty, ty, entry)
    }

    fn new_given_parts(func_ty: FunctionType, ty: Type, entry: Target) -> Self {
        Self {
            ty,
            func_ty,
            global_name: None,
            debug_name: None,
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
}

#[derive(Debug)]
pub struct BlockInfo {
    pub phis: Vec<Phi>,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}

impl BlockInfo {
    /// Create a new empty block with unreachable terminator.
    pub fn new() -> BlockInfo {
        BlockInfo {
            phis: Vec::new(),
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }
}

#[derive(Debug)]
pub struct PhiInfo {
    pub ty: Type,
}

#[derive(Debug)]
pub enum InstructionInfo {
    /// Load a value of type `ty` from `addr`.
    ///
    /// signature: `Load { addr: &, ty=T } -> T`
    Load { addr: Value, ty: Type },

    /// Store `value` into `addr`.
    ///
    /// `Store { addr: &, ty=T, value: T } -> void`
    Store { addr: Value, ty: Type, value: Value },

    /// Call `target` with arguments `args`.
    ///
    /// `Call { target: (A, B, C) -> R, args: [A, B, C] } -> R`
    Call { target: Value, args: Vec<Value> },

    ///Perform binary arithmetic operation `kind(left, right)`;
    ///
    /// `Arithmetic { kind, left: iN, right: iN } -> iN`
    Arithmetic { kind: ArithmeticOp, left: Value, right: Value },

    /// Perform binary comparison operation `kind(left, right)`;
    ///
    /// `Comparison { kind, left: iN, right: iN } -> i1`
    Comparison { kind: LogicalOp, left: Value, right: Value },

    /// Compute the pointer to a tuple field at `index` in `tuple_ty` from a pointer to containing tuple `base`.
    ///
    /// `TupleFieldPtr { base: &, index=1, tuple_ty=(A, B, C) } -> &`
    TupleFieldPtr { base: Value, index: u32, tuple_ty: Type },

    /// Compute the pointer to element `index` of a hypothetical array containing elements of type `T` starting at `base`.
    /// Intuitively this is `&base[index]` or equivalently `base + index * sizeof(T)`.
    /// `value` can be negative..
    ///
    /// `PointerOffSet { ty=T, base: &, index: i32 } -> &`
    PointerOffSet { ty: Type, base: Value, index: Value },
}

//TODO what about signed and unsigned? type or operation?
#[derive(Debug, Copy, Clone)]
pub enum ArithmeticOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

//TODO what about signed and unsigned? type or operation?
#[derive(Debug, Copy, Clone)]
pub enum LogicalOp {
    Eq,
    Neq,
    Gt,
    Gte,
    Lt,
    Lte,
}

impl InstructionInfo {
    pub fn ty(&self, prog: &Program) -> Type {
        //TODO this implementation is prone to infinite recursion!
        // eg a = add (a, a) or similar constructs
        // maybe change InstructionInfo to always include the result type?
        match self {
            InstructionInfo::Load { ty, .. } => *ty,
            InstructionInfo::Store { .. } => prog.ty_ptr(),
            InstructionInfo::Call { target, .. } => {
                prog.get_type(prog.type_of_value(*target)).unwrap_func()
                    .expect("call target should have a function type")
                    .ret
            }
            InstructionInfo::Arithmetic { left, .. } => prog.type_of_value(*left),
            InstructionInfo::Comparison { .. } => prog.ty_bool,
            InstructionInfo::TupleFieldPtr { tuple_ty, index, .. } => {
                *prog.get_type(*tuple_ty).unwrap_tuple()
                    .expect("tuple_ty should be a tuple type")
                    .fields.get(*index as usize)
                    .unwrap_or_else(|| panic!("tuple index {} out of range for {:?} {}", index, tuple_ty, prog.format_type(*tuple_ty)))
            },
            InstructionInfo::PointerOffSet { .. } => prog.ty_ptr,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jump { target: Target },
    Branch { cond: Value, true_target: Target, false_target: Target },
    Return { value: Value },
    Unreachable,
}

#[derive(Debug, Clone)]
pub struct Target {
    pub block: Block,
    pub phi_values: Vec<Value>,
}

impl Terminator {
    pub fn for_each_target_mut<F: FnMut(&mut Target)>(&mut self, mut f: F) {
        match self {
            Terminator::Jump { target } => f(target),
            Terminator::Branch { true_target, false_target, .. } => {
                f(true_target);
                f(false_target);
            }
            Terminator::Return { .. } => {}
            Terminator::Unreachable => {}
        }
    }

    pub fn for_each_target<F: FnMut(&Target)>(&self, mut f: F) {
        match self {
            Terminator::Jump { target } => f(target),
            Terminator::Branch { true_target, false_target, .. } => {
                f(true_target);
                f(false_target);
            }
            Terminator::Return { .. } => {}
            Terminator::Unreachable => {}
        }
    }

    pub fn for_each_successor<F: FnMut(Block)>(&self, mut f: F) {
        self.for_each_target(|target| f(target.block))
    }
}

//TODO maybe this enum could implement From to make all the wrapping easier?
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Value {
    Undef(Type),
    Const(Const),
    Func(Function),
    Param(Parameter),
    Slot(StackSlot),
    Phi(Phi),
    Instr(Instruction),
    Extern(Extern),
    Data(Data),
}

//TODO should this be represented in the type system instead?
impl Value {
    pub fn is_const_like(self) -> bool {
        match self {
            Value::Undef(_) => false,
            Value::Const(_) => true,
            Value::Func(_) => true,
            Value::Param(_) => false,
            Value::Slot(_) => false,
            Value::Phi(_) => false,
            Value::Instr(_) => false,
            Value::Extern(_) => true,
            Value::Data(_) => true,
        }
    }
}

#[derive(Debug)]
pub struct DataInfo {
    pub ty: Type,
    pub inner_ty: Type,
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
    /// Visit all the blocks reachable from the entry of `func` in breadth-first order.
    pub fn try_visit_blocks<E, F: FnMut(Block) -> Result<(), E>>(&self, func: Function, mut f: F) -> Result<(), E> {
        let func = self.get_func(func);

        let mut blocks_left = VecDeque::new();
        let mut blocks_seen = HashSet::new();
        blocks_left.push_front(func.entry.block);

        while let Some(block) = blocks_left.pop_front() {
            if !blocks_seen.insert(block) { continue; }

            f(block)?;

            let block_info = self.get_block(block);
            block_info.terminator.for_each_successor(
                |succ| blocks_left.push_back(succ));
        }

        Ok(())
    }

    pub fn try_visit_blocks_mut<E, F: FnMut(&mut Program, Block) -> Result<(), E>>(&mut self, func: Function, mut f: F) -> Result<(), E> {
        let func = self.get_func(func);

        let mut blocks_left = VecDeque::new();
        let mut blocks_seen = HashSet::new();
        blocks_left.push_front(func.entry.block);

        while let Some(block) = blocks_left.pop_front() {
            if !blocks_seen.insert(block) { continue; }

            f(self, block)?;

            let block_info = self.get_block(block);
            block_info.terminator.for_each_successor(
                |succ| blocks_left.push_back(succ));
        }

        Ok(())
    }

    /// Visit all the blocks reachable from the entry of `func` in breadth-first order.
    pub fn visit_blocks<F: FnMut(Block)>(&self, func: Function, mut f: F) {
        //change this to use ! once that's stable
        self.try_visit_blocks::<(), _>(func, |block| {
            f(block);
            Ok(())
        }).unwrap();
    }

    /// Visit all the blocks reachable from the entry of `func` in breadth-first order.
    pub fn visit_blocks_mut<F: FnMut(&mut Program, Block)>(&mut self, func: Function, mut f: F) {
        //change this to use ! once that's stable
        self.try_visit_blocks_mut::<(), _>(func, |prog, block| {
            f(prog, block);
            Ok(())
        }).unwrap();
    }
}

//Formatting related stuff
impl Program {
    /// Wrap a `Type` as a `Display` value that recursively prints a human-readable version of the type.
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
                    TypeInfo::Pointer =>
                        write!(f, "&"),
                    TypeInfo::Tuple(TupleType { fields }) =>
                        self.prog.write_tuple(f, fields),
                    TypeInfo::Func(FunctionType { params, ret }) => {
                        self.prog.write_tuple(f, params)?;
                        write!(f, " -> {}", self.prog.format_type(*ret))
                    }
                    TypeInfo::Array(ArrayType { inner, length }) =>
                        write!(f, "[{}; {}]", self.prog.format_type(*inner), length),
                }
            }
        }

        Wrapped { ty, prog: self }
    }

    /// Helper function for formatting types, writes `(fields[0], fields[1], ...)`
    fn write_tuple(&self, f: &mut Formatter<'_>, fields: &[Type]) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, &field) in fields.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{}", self.format_type(field))?;
        }
        write!(f, ")")?;
        Ok(())
    }

    /// Wrap a `Value` as a `Display` value that prints a mostly human-readable representation of the value,
    /// including the type.
    pub fn format_value(&self, value: Value) -> impl Display + '_ {
        struct Wrapped<'a> {
            value: Value,
            prog: &'a Program,
        }

        impl Display for Wrapped<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let ty = self.prog.format_type(self.prog.type_of_value(self.value));

                match self.value {
                    Value::Undef(_) =>
                        write!(f, "Undef(: {})", ty),
                    Value::Const(cst) =>
                        write!(f, "Const({}: {})", cst.value, ty),
                    Value::Func(func) =>
                        write!(f, "Func({:?}: {})", func.0, ty),
                    Value::Param(param) =>
                        write!(f, "Param({:?}: {})", param.0, ty),
                    Value::Slot(slot) =>
                        write!(f, "Slot({:?}: {})", slot.0, ty),
                    Value::Phi(phi) =>
                        write!(f, "Phi({:?}: {})", phi.0, ty),
                    Value::Instr(instr) =>
                        write!(f, "Instr({:?}: {})", instr.0, ty),
                    Value::Extern(ext) =>
                        write!(f, "Extern({:?} -> {}: {})", ext.0, self.prog.get_ext(ext).name, ty),
                    Value::Data(data) =>
                        write!(f, "Data({:?}: {})", data.0, ty),
                }
            }
        }

        Wrapped { value, prog: self }
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

            if let Some(global_name) = &func_info.global_name {
                writeln!(f, "    global_name: {}", global_name)?;
            }
            if let Some(debug_name) = &func_info.debug_name {
                writeln!(f, "    debug_name: {}", debug_name)?;
            }

            if !func_info.params.is_empty() {
                writeln!(f, "    params:")?;
                for &param in &func_info.params {
                    let param_info = self.get_param(param);
                    writeln!(f, "      {:?}: {}", param, self.format_type(param_info.ty))?;
                }
            }
            if !func_info.slots.is_empty() {
                writeln!(f, "    slots:")?;
                for &slot in &func_info.slots {
                    let slot_info = self.get_slot(slot);
                    writeln!(f, "      {:?}: &{}", slot, self.format_type(slot_info.inner_ty))?;
                }
            }
            writeln!(f, "    entry: {:?}", func_info.entry)?;

            self.try_visit_blocks(func, |block| {
                let block_info = self.get_block(block);
                writeln!(f, "    {:?} {{", block)?;

                if !block_info.phis.is_empty() {
                    writeln!(f, "      phis:")?;
                    for &phi in &block_info.phis {
                        let phi_info = self.get_phi(phi);
                        writeln!(f, "        {:?}: {}", phi, self.format_type(phi_info.ty))?;
                    }
                }

                for &instr in &block_info.instructions {
                    let instr_info = self.get_instr(instr);
                    writeln!(f, "      {:?}: {:?}", instr, instr_info)?;
                }

                match &block_info.terminator {
                    Terminator::Jump { target } => {
                        writeln!(f, "      Jump {{")?;
                        writeln!(f, "        {:?}", target)?;
                        writeln!(f, "      }}")?;
                    }
                    Terminator::Branch { cond, true_target, false_target } => {
                        writeln!(f, "      Branch {{")?;
                        writeln!(f, "        cond: {:?}", cond)?;
                        writeln!(f, "        true:  {:?}", true_target)?;
                        writeln!(f, "        false: {:?}", false_target)?;
                        writeln!(f, "      }}")?;
                    }
                    term => writeln!(f, "      {:?}", term)?,
                }

                writeln!(f, "    }}")?;

                Ok(())
            })?;
            writeln!(f, "  }}")?;
        };

        writeln!(f, "}}")?;
        Ok(())
    }
}