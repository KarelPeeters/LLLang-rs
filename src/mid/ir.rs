use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use derive_more::{Constructor, From};
use itertools::Itertools;

use crate::mid::util::bit_int::BitInt;
use crate::util::arena::{Arena, ArenaSet};
use crate::util::internal_iter::InternalIterator;

macro_rules! gen_node_and_program_accessors {
    ($([$node:ident, $info:ident, $def:ident, $get:ident, $get_mut:ident, $single:ident, $mul:ident],)*) => {
        $(
        new_index_type!(pub $node);
        )*

        #[derive(Debug, Default, Clone)]
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
            pub fn $get(&self, $single: $node) -> &$info {
                &self.nodes.$mul[$single]
            }

            #[allow(dead_code)]
            pub fn $get_mut(&mut self, $single: $node) -> &mut $info {
                &mut self.nodes.$mul[$single]
            }
        )*
        }
    }
}

// TODO should expressions be stored as a deduplicating set as well?
// TODO find a better name for expression, eg. "PureInstruction"
gen_node_and_program_accessors![
    [Function, FunctionInfo, define_func, get_func, get_func_mut, func, funcs],
    [StackSlot, StackSlotInfo, define_slot, get_slot, get_slot_mut, slot, slots],
    [Block, BlockInfo, define_block, get_block, get_block_mut, block, blocks],
    [Parameter, ParameterInfo, define_param, get_param, get_param_mut, param, params],
    [Instruction, InstructionInfo, define_instr, get_instr, get_instr_mut, instr, instrs],
    [Expression, ExpressionInfo, define_expr, get_expr, get_expr_mut, expr, exprs],
    [Extern, ExternInfo, define_ext, get_ext, get_ext_mut, ext, exts],
    [Data, DataInfo, define_data, get_data, get_data_mut, data, datas],
];

new_index_type!(pub Type);
pub type ProgramTypes = ArenaSet<Type, TypeInfo>;

#[derive(Debug, Clone)]
pub struct Program {
    ptr_size_bits: u32,

    //TODO we've lost distinct indices! is there an easy way to get that back?
    //all values that may be used multiple times are stored as nodes
    pub nodes: Arenas,
    //TODO maybe look into adding a cell here so we can modify this when we have a &Program for usability
    //the types are stored separately in a set for interning
    pub types: ProgramTypes,

    //predefined types
    ty_void: Type,
    ty_ptr: Type,
    ty_bool: Type,
    ty_isize: Type,

    pub root_functions: HashMap<String, Function>,
}

impl Program {
    // TODO fix this documentation
    /// Return the program representing `fn main() -> void { unreachable(); }`
    pub fn new(ptr_size_bits: u32) -> Self {
        let mut types = ArenaSet::default();

        let ty_void = types.push(TypeInfo::Void);
        let ty_ptr = types.push(TypeInfo::Pointer);
        let ty_bool = types.push(TypeInfo::Integer { bits: 1 });
        let ty_isize = types.push(TypeInfo::Integer { bits: ptr_size_bits });

        Program {
            ptr_size_bits,
            nodes: Arenas::default(),
            types,
            ty_void,
            ty_ptr,
            ty_bool,
            ty_isize,
            root_functions: Default::default()
        }
    }

    pub fn ptr_size_bits(&self) -> u32 {
        self.ptr_size_bits
    }

    // TODO maybe make self.types use internal mutability?
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

    pub fn ty_isize(&self) -> Type {
        self.ty_isize
    }

    pub fn get_type(&self, ty: Type) -> &TypeInfo {
        &self.types[ty]
    }

    pub fn const_null_ptr(&self) -> Const {
        Const::new(self.ty_ptr, BitInt::zero(self.ptr_size_bits))
    }

    pub fn const_bool(&self, value: bool) -> Const {
        Const::new(self.ty_bool, BitInt::from_bool(value))
    }

    pub fn type_of_value(&self, value: Value) -> Type {
        match value {
            Value::Immediate(value) => {
                match value {
                    Immediate::Void => self.ty_void(),
                    Immediate::Undef(ty) => ty,
                    Immediate::Const(cst) => cst.ty,
                }
            }
            Value::Global(value) => {
                match value {
                    Global::Func(func) => self.get_func(func).ty,
                    Global::Extern(ext) => self.get_ext(ext).ty,
                    Global::Data(data) => self.get_data(data).ty,
                }
            }
            Value::Scoped(value) => {
                match value {
                    Scoped::Param(param) => self.get_param(param).ty,
                    Scoped::Slot(_) => self.ty_ptr,
                    Scoped::Instr(instr) => self.get_instr(instr).ty(self),
                }
            }
            Value::Expr(expr) => self.get_expr(expr).ty(self),
        }
    }

    pub fn is_zero_sized_type(&self, ty: Type) -> bool {
        // maybe in the future we need to change this to be tristate (ie. "don't know" option) but for now it's fine
        match *self.get_type(ty) {
            TypeInfo::Void => true,
            TypeInfo::Integer { bits } => bits == 0,
            TypeInfo::Pointer => false,
            TypeInfo::Func(_) => false,
            TypeInfo::Tuple(TupleType { ref fields }) => fields.iter().all(|&f| self.is_zero_sized_type(f)),
            TypeInfo::Array(ArrayType { inner, length }) => length == 0 || self.is_zero_sized_type(inner),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeInfo {
    // TODO replace void with zero-sized int?
    Void,
    Integer { bits: u32 },
    Pointer,
    Func(FunctionType),
    Tuple(TupleType),
    Array(ArrayType),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum CallingConvention {
    /// Windows 64-bit calling convention.
    /// This is the same as `__stdcall` when compiling for x64.
    Win64,
    /// The backend can freely choose the calling convention.
    /// The only requirement is that it's the same for functions with the same signature.
    Custom,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionType {
    pub params: Vec<Type>,
    // TODO allow multiple returns
    pub ret: Type,
    pub conv: CallingConvention,
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

// TODO return results instead of options here
//  (and also do this for other option-returning things)
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

#[derive(Debug, Clone)]
pub struct FunctionInfo {
    pub ty: Type,
    pub func_ty: FunctionType,

    pub slots: Vec<StackSlot>,
    pub entry: Block,

    pub debug_name: Option<String>,
}

impl FunctionInfo {
    /// Create a new function with the given type.
    /// * The params are automatically created.
    /// * The entry block starts out empty and with an unreachable terminator.
    pub fn new(func_ty: FunctionType, prog: &mut Program) -> Self {
        let ty = prog.define_type_func(func_ty.clone());
        let params = func_ty.params.iter()
            .map(|&param_ty| prog.define_param(ParameterInfo { ty: param_ty }))
            .collect_vec();

        let entry = prog.define_block(BlockInfo {
            params,
            instructions: vec![],
            terminator: Terminator::Unreachable,
            debug_name: None,
        });

        Self::new_given_parts(func_ty, ty, entry)
    }

    fn new_given_parts(func_ty: FunctionType, ty: Type, entry: Block) -> Self {
        Self {
            ty,
            func_ty,
            debug_name: None,
            entry,
            slots: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParameterInfo {
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct StackSlotInfo {
    pub inner_ty: Type,
    pub debug_name: Option<String>,
}

#[derive(Debug, Clone)]
pub struct BlockInfo {
    pub params: Vec<Parameter>,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
    // TODO check whether this (and other) debug names are propagated and rendered whenever possible
    pub debug_name: Option<String>,
}

impl BlockInfo {
    /// Create a new empty block without params and with an unreachable terminator.
    pub fn new() -> BlockInfo {
        BlockInfo {
            params: Vec::new(),
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
            debug_name: None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum InstructionInfo {
    /// Load a value of type `ty` from `addr`.
    ///
    /// signature: `Load { addr: &, ty=T } -> T`
    Load { addr: Value, ty: Type },

    /// Store `value` into `addr`.
    ///
    /// `Store { addr: &, ty=T, value: T } -> void`
    // TODO remove the ty field here?
    Store { addr: Value, ty: Type, value: Value },

    /// Call `target` with arguments `args`.
    ///
    /// `Call { target: (A, B, C) -> R, args: [A, B, C] } -> R`
    // TODO add an expression variant of call that can't have have any side effects 
    Call { target: Value, args: Vec<Value>, conv: CallingConvention },

    /// Return `value` as-is.
    /// Optimizations should assume that:
    /// * the operand value is actually used some some side-effect purpose
    /// * the returned value is not known at compile time.
    BlackBox { value: Value },
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ExpressionInfo {
    ///Perform binary arithmetic operation `kind(left, right)`;
    ///
    /// `Arithmetic { kind, left: iN, right: iN } -> iN`
    Arithmetic { kind: ArithmeticOp, left: Value, right: Value },

    /// Perform binary comparison operation `kind(left, right)`;
    ///
    /// `Comparison { kind, left: iN, right: iN } -> i1`
    Comparison { kind: ComparisonOp, left: Value, right: Value },

    // TODO should this really be an instruction?
    //   kind of, otherwise we may as well switch to sea of nodes and make arithmetic no longer an instruction
    // TODO how does this fit into the untyped ptr story?
    //   we can't really remove this since the layout is only decided in the backend...
    /// Compute the pointer to a tuple field at `index` in `tuple_ty` from a pointer to containing tuple `base`.
    ///
    /// `TupleFieldPtr { base: &, index=1, tuple_ty=(A, B, C) } -> &`
    TupleFieldPtr { base: Value, index: u32, tuple_ty: Type },

    /// Compute the pointer to element `index` of a hypothetical array containing elements of type `T` starting at `base`.
    /// Intuitively this is `&base[index]` or equivalently `base + index * sizeof(T)`.
    /// `value` can be negative..
    ///
    /// `PointerOffSet { ty=T, base: &, index: i32 } -> &`
    // TODO clarify whether index is signed or unsigned
    // TODO rename to ArrayOffset?
    PointerOffSet { ty: Type, base: Value, index: Value },

    /// Convert `value` to `ty`. `kind` specifies additional semantics this cast will have.
    ///
    /// `Cast { after_ty: B, before_value: A } -> B`
    Cast { ty: Type, kind: CastKind, value: Value },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Signed {
    Signed,
    Unsigned,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ArithmeticOp {
    Add,
    Sub,
    Mul,
    Div(Signed),
    Mod(Signed),
    // TODO split these into separate bitwise op?
    And,
    Or,
    Xor,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ComparisonOp {
    Eq,
    Neq,
    Gt(Signed),
    Gte(Signed),
    Lt(Signed),
    Lte(Signed),
}

#[derive(Debug, Constructor)]
pub struct ArithmeticProperties {
    pub commuted: Option<ArithmeticOp>,
    pub associative: bool,
}

#[derive(Debug, Constructor)]
pub struct ComparisonProperties {
    pub commuted: ComparisonOp,
    pub negated: ComparisonOp,
    pub result_self: bool,
}

impl ArithmeticOp {
    pub fn signed(self) -> Option<Signed> {
        match self {
            ArithmeticOp::Add | ArithmeticOp::Sub | ArithmeticOp::Mul | ArithmeticOp::And | ArithmeticOp::Or | ArithmeticOp::Xor => None,
            ArithmeticOp::Div(s) | ArithmeticOp::Mod(s) => Some(s),
        }
    }

    pub fn properties(self) -> ArithmeticProperties {
        use ArithmeticOp as Op;
        use ArithmeticProperties as Props;
        match self {
            Op::Add => Props::new(Some(Op::Add), true),
            Op::Sub => Props::new(None, false),
            Op::Mul => Props::new(Some(Op::Mul), true),
            Op::Div(_) => Props::new(None, false),
            Op::Mod(_) => Props::new(None, false),
            Op::And => Props::new(Some(Op::And), true),
            Op::Or => Props::new(Some(Op::Or), true),
            Op::Xor => Props::new(Some(Op::Xor), true),
        }
    }
}

impl ComparisonOp {
    pub fn signed(self) -> Option<Signed> {
        match self {
            ComparisonOp::Eq | ComparisonOp::Neq => None,
            ComparisonOp::Gt(s) | ComparisonOp::Gte(s) | ComparisonOp::Lt(s) | ComparisonOp::Lte(s) => Some(s),
        }
    }

    pub fn properties(self) -> ComparisonProperties {
        use ComparisonProperties as Props;
        use ComparisonOp as Op;
        match self {
            Op::Eq => Props::new(Op::Eq, Op::Neq, true),
            Op::Neq => Props::new(Op::Neq, Op::Eq, false),
            Op::Gt(signed) => Props::new(Op::Lt(signed), Op::Lte(signed), false),
            Op::Gte(signed) => Props::new(Op::Lte(signed), Op::Lt(signed), true),
            Op::Lt(signed) => Props::new(Op::Gt(signed), Op::Gte(signed), false),
            Op::Lte(signed) => Props::new(Op::Gte(signed), Op::Gt(signed), true),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum CastKind {
    /// Cast from an int to a possibly shorter int.
    IntTruncate,
    /// Cast from an int to a possibly longer int, sign- or zero-extending depending on the signedness.
    IntExtend(Signed),

    // TODO add casts between int and ptr
    //   maybe call it bitwise? or is that something else?
}

impl ExpressionInfo {
    //TODO this implementation is prone to infinite recursion!
    pub fn ty(&self, prog: &Program) -> Type {
        match *self {
            ExpressionInfo::Arithmetic { left, .. } => prog.type_of_value(left),
            ExpressionInfo::Comparison { .. } => prog.ty_bool,
            ExpressionInfo::TupleFieldPtr { .. } => prog.ty_ptr,
            ExpressionInfo::PointerOffSet { .. } => prog.ty_ptr,
            ExpressionInfo::Cast { ty: after_ty, .. } => after_ty,
        }
    }

    pub fn replace_values(&mut self, mut f: impl FnMut(Value) -> Value) {
        match self {
            ExpressionInfo::Arithmetic { kind: _, left, right } => {
                *left = f(*left);
                *right = f(*right);
            }
            ExpressionInfo::Comparison { kind: _, left, right } => {
                *left = f(*left);
                *right = f(*right);
            }
            ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _ } => {
                *base = f(*base);
            }
            ExpressionInfo::PointerOffSet { ty: _, base, index } => {
                *base = f(*base);
                *index = f(*index);
            }
            ExpressionInfo::Cast { ty: _, kind: _, value } => {
                *value = f(*value);
            }
        }
    }
}

impl InstructionInfo {
    pub fn ty(&self, prog: &Program) -> Type {
        //TODO this implementation is prone to infinite recursion!
        match *self {
            InstructionInfo::Load { ty, .. } => ty,
            InstructionInfo::Store { .. } => prog.ty_void(),
            InstructionInfo::Call { target, .. } => {
                prog.get_type(prog.type_of_value(target)).unwrap_func()
                    .expect("call target should have a function type")
                    .ret
            }
            InstructionInfo::BlackBox { value } => prog.type_of_value(value),
        }
    }

    pub fn replace_values(&mut self, mut f: impl FnMut(Value) -> Value) {
        // avoid using ".." here to avoid accidentally forgetting to update this function
        match self {
            InstructionInfo::Load { addr, ty: _ } => *addr = f(*addr),
            InstructionInfo::Store { addr, ty: _, value } => {
                *addr = f(*addr);
                *value = f(*value);
            }
            InstructionInfo::Call { target, args, conv: _ } => {
                *target = f(*target);
                for arg in args {
                    *arg = f(*arg);
                }
            }
            InstructionInfo::BlackBox { value } => {
                *value = f(*value);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jump { target: Target },
    Branch { cond: Value, true_target: Target, false_target: Target },
    Return { value: Value },
    Unreachable,
    LoopForever,
}

#[derive(Debug, Clone)]
pub struct Target {
    pub block: Block,
    pub args: Vec<Value>,
}

impl Target {
    pub fn replace_blocks(&mut self, f: impl FnOnce(Block) -> Block) {
        self.block = f(self.block);
    }

    pub fn replace_values(&mut self, mut f: impl FnMut(Value) -> Value) {
        for value in &mut self.args {
            *value = f(*value);
        }
    }
}

macro_rules! impl_nested_from {
    ($outer:ident::$variant:ident($inner:ty)) => {
        impl From<$inner> for $outer {
            fn from(value: $inner) -> Self {
                <$outer>::$variant(value.into())
            }
        }
    }
}

// TODO considering using .value() instead of the current .into() which is more vague
#[derive(Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum Value {
    // TODO move immediate into expression? they're both identity-less, do we ever handle them differently?
    Immediate(Immediate),
    Global(Global),
    Scoped(Scoped),
    Expr(Expression),
}

// TODO find a better name for these identity-less, immediate, instant, on-demand values
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum Immediate {
    Void,
    Undef(Type),
    Const(Const),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum Global {
    Func(Function),
    Extern(Extern),
    Data(Data),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, From)]
pub enum Scoped {
    Slot(StackSlot),
    Param(Parameter),
    Instr(Instruction),
}

impl_nested_from!(Value::Immediate(Const));
impl_nested_from!(Value::Global(Function));
impl_nested_from!(Value::Global(Extern));
impl_nested_from!(Value::Global(Data));
impl_nested_from!(Value::Scoped(Parameter));
impl_nested_from!(Value::Scoped(StackSlot));
impl_nested_from!(Value::Scoped(Instruction));

impl Debug for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // don't print the additional wrapper types
        match self {
            Value::Immediate(value) => value.fmt(f),
            Value::Global(value) => value.fmt(f),
            Value::Scoped(value) => value.fmt(f),
            Value::Expr(value) => write!(f, "Expr({:?})", value),
        }
    }
}

impl Value {
    pub fn void() -> Self {
        Value::Immediate(Immediate::Void)
    }

    pub fn undef(ty: Type) -> Self {
        Value::Immediate(Immediate::Undef(ty))
    }

    pub fn as_global(self) -> Option<Global> {
        option_match!(self, Value::Global(global) => global)
    }

    pub fn as_const(self) -> Option<Const> {
        option_match!(self, Value::Immediate(Immediate::Const(cst)) => cst)
    }

    pub fn as_func(self) -> Option<Function> {
        option_match!(self, Value::Global(Global::Func(func)) => func)
    }

    pub fn as_instr(self) -> Option<Instruction> {
        option_match!(self, Value::Scoped(Scoped::Instr(instr)) => instr)
    }

    pub fn as_expr(self) -> Option<Expression> {
        option_match!(self, Value::Expr(expr) => expr)
    }

    pub fn as_slot(self) -> Option<StackSlot> {
        option_match!(self, Value::Scoped(Scoped::Slot(slot)) => slot)
    }

    pub fn is_undef(self) -> bool {
        matches!(self, Value::Immediate(Immediate::Undef(_)))
    }

    pub fn is_const(self) -> bool {
        self.as_const().is_some()
    }

    pub fn is_const_zero(self) -> bool {
        self.as_const().map_or(false, |cst| cst.is_zero())
    }

    pub fn is_expr(self) -> bool {
        self.as_expr().is_some()
    }

    pub fn is_slot(self) -> bool {
        self.as_slot().is_some()
    }
}

#[derive(Debug, Clone)]
pub struct DataInfo {
    // TODO should data always have type &u8? Currently it has &T, but we could just cast it when used.
    pub ty: Type,
    pub inner_ty: Type,
    pub bytes: Vec<u8>,
}

// TODO assert there are no conflicting extern names
// TODO rename name to symbol?
#[derive(Debug, Clone)]
pub struct ExternInfo {
    pub name: String,
    pub ty: Type,
}

// TODO think about how ptr-typed consts are supposed to work
//   if we decide to keep those separate, remove this struct and rename Value:::Const to ::IntConst
#[derive(Clone, Copy, Eq, PartialEq, Hash, Constructor)]
pub struct Const {
    pub ty: Type,
    pub value: BitInt,
}

impl Debug for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.display_value())
    }
}

impl Const {
    pub fn is_zero(self) -> bool {
        self.value.is_zero()
    }

    pub fn as_bool(self) -> Option<bool> {
        self.value.as_bool()
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
                    TypeInfo::Func(FunctionType { params, ret, conv }) => {
                        write!(f, "{:?} ", conv)?;
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
                    Value::Immediate(value) => match value {
                        Immediate::Void =>
                            write!(f, "Void"),
                        Immediate::Undef(_ty) =>
                            write!(f, "Undef(: {})", ty),
                        Immediate::Const(cst) =>
                            write!(f, "Const({:?}: {})", cst.value, ty),
                    }
                    Value::Global(value) => match value {
                        Global::Func(func) =>
                            write!(f, "Func({:?}: {})", func.0, ty),
                        Global::Extern(ext) =>
                            write!(f, "Extern({:?} -> {}: {})", ext.0, self.prog.get_ext(ext).name, ty),
                        Global::Data(data) =>
                            write!(f, "Data({:?}: {})", data.0, ty),
                    }
                    Value::Scoped(value) => match value {
                        Scoped::Param(param) =>
                            write!(f, "Param({:?}: {})", param.0, ty),
                        Scoped::Slot(slot) =>
                            write!(f, "Slot({:?}: {})", slot.0, ty),
                        Scoped::Instr(instr) =>
                            write!(f, "Instr({:?}: {})", instr.0, ty),
                    }
                    Value::Expr(expr) =>
                        write!(f, "Expr({:?} : {})", expr.0, ty)
                }
            }
        }

        Wrapped { value, prog: self }
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Program (nodes: {}) {{", self.nodes.total_node_count())?;

        match self.root_functions.iter().collect_vec().as_slice() {
            &[] => writeln!(f, "  roots: []")?,
            &[(name, func)] => writeln!(f, "  roots: {{{:?}: {:?}}}", name, func)?,
            roots => {
                writeln!(f, "  roots: {{")?;
                for (name, func) in roots {
                    writeln!(f, "    {:?}: {:?}", name, func)?;
                }
                writeln!(f, "  }}")?;
            }
        }

        // TODO try to print in topological order
        for (func, func_info) in &self.nodes.funcs {
            writeln!(f, "\n  {:?}: {} {{", func, self.format_type(func_info.ty))?;

            if let Some(debug_name) = &func_info.debug_name {
                writeln!(f, "    debug_name: {:?}", debug_name)?;
            }

            if !func_info.slots.is_empty() {
                writeln!(f, "    slots:")?;
                for &slot in &func_info.slots {
                    let slot_info = self.get_slot(slot);

                    if let Some(debug_name) = &slot_info.debug_name {
                        writeln!(f, "      {:?}: &{}, debug_name: {:?}", slot, self.format_type(slot_info.inner_ty), debug_name)?;
                    } else {
                        writeln!(f, "      {:?}: &{}", slot, self.format_type(slot_info.inner_ty))?;
                    }
                }
            }
            writeln!(f, "    entry: {:?}", func_info.entry)?;

            self.reachable_blocks(self.get_func(func).entry).try_for_each(|block| {
                let block_info = self.get_block(block);
                writeln!(f, "    {:?} {{", block)?;

                if !block_info.params.is_empty() {
                    writeln!(f, "      params:")?;
                    for &param in &block_info.params {
                        let param_info = self.get_param(param);
                        writeln!(f, "        {:?}: {}", param, self.format_type(param_info.ty))?;
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

        // TODO can we do some simple scheduling to print these closer to their usage sites?
        writeln!(f, "  expressions:")?;
        for (expr, expr_info) in &self.nodes.exprs {
            writeln!(f, "    {:?}: {:?}", expr, expr_info)?;
        }

        writeln!(f, "  types:")?;
        for (ty, _) in &self.types {
            writeln!(f, "    {:?}: {}", ty, self.format_type(ty))?
        }

        if self.nodes.exts.len() > 0 {
            writeln!(f, "  extern:")?;
            for (ext, ext_info) in &self.nodes.exts {
                writeln!(f, "    {:?}: {:?}", ext, ext_info)?
            }
        }

        if self.nodes.datas.len() > 0 {
            writeln!(f, "  data:")?;
            for (data, data_info) in &self.nodes.datas {
                writeln!(f, "    {:?}: {:?}", data, data_info)?
            }
        }

        writeln!(f, "}}")?;
        Ok(())
    }
}
