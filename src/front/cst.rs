use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Index;

use derive_more::Constructor;
use itertools::Itertools;

use crate::front::{ast, error};
use crate::front::error::{Error, Result};
use crate::front::lower::LRValue;
use crate::front::scope::Scope;
use crate::front::type_solver::TypeVar;
use crate::mid::ir::{PTR_SIZE_BITS, Signed};
use crate::util::arena::{Arena, ArenaSet};

new_index_type!(pub Module);
new_index_type!(pub Type);
new_index_type!(pub Function);
new_index_type!(pub Const);

#[derive(Debug)]
pub struct ResolvedProgram<'a> {
    pub types: TypeStore<'a>,
    pub items: ItemStore<'a>,
    pub main_func: Function,
}

type BasicTypeInfo<'ast> = TypeInfo<'ast, Type>;

pub struct TypeStore<'a> {
    types: ArenaSet<Type, BasicTypeInfo<'a>>,

    ty_wildcard: Type,
    ty_void: Type,
    ty_bool: Type,

    ty_u8: Type,
    ty_isize: Type,
    ty_usize: Type,
}

impl<'a> Debug for TypeStore<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "TypeStore {{")?;
        for (ty, _) in &self.types {
            writeln!(f, "    {:?}: {}", ty, self.format_type(ty))?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl<'a> Default for TypeStore<'a> {
    fn default() -> Self {
        let mut types = ArenaSet::default();
        let ty_wildcard = types.push(TypeInfo::Wildcard);
        let ty_void = types.push(TypeInfo::Void);
        let ty_bool = types.push(TypeInfo::Bool);

        let ty_u8 = types.push(TypeInfo::Int(IntTypeInfo::U8));
        let ty_isize = types.push(TypeInfo::Int(IntTypeInfo::ISIZE));
        let ty_usize = types.push(TypeInfo::Int(IntTypeInfo::USIZE));

        Self { types, ty_wildcard, ty_void, ty_bool, ty_u8, ty_isize, ty_usize }
    }
}

impl<'a> TypeStore<'a> {
    pub fn type_void(&self) -> Type {
        self.ty_void
    }

    pub fn type_bool(&self) -> Type {
        self.ty_bool
    }

    pub fn type_u8(&self) -> Type {
        self.ty_u8
    }

    pub fn type_isize(&self) -> Type {
        self.ty_isize
    }

    pub fn type_usize(&self) -> Type {
        self.ty_usize
    }

    pub fn new_placeholder(&mut self) -> Type {
        self.types.push(TypeInfo::Placeholder(self.types.len()))
    }

    pub fn replace_placeholder(&mut self, ph: Type, info: BasicTypeInfo<'a>) {
        let old_info = self.types.replace(ph, info);
        assert!(matches!(old_info, TypeInfo::Placeholder(_)), "tried to replace non-placeholder type {:?}", old_info)
    }

    pub fn define_type(&mut self, info: BasicTypeInfo<'a>) -> Type {
        self.types.push(info)
    }

    pub fn define_type_ptr(&mut self, inner: Type) -> Type {
        self.define_type(TypeInfo::Pointer(inner))
    }

    pub fn format_type(&self, ty: Type) -> impl Display + '_ {
        struct Wrapped<'s> {
            store: &'s TypeStore<'s>,
            ty: Type,
        }

        fn write_tuple(store: &TypeStore, f: &mut Formatter<'_>, fields: &[Type]) -> std::fmt::Result {
            write!(f, "(")?;
            for (i, &param_ty) in fields.iter().enumerate() {
                if i > 0 { write!(f, ", ")?; }
                write!(f, "{}", store.format_type(param_ty))?;
            }
            write!(f, ")")
        }

        impl Display for Wrapped<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match &self.store[self.ty] {
                    TypeInfo::Placeholder(i) => write!(f, "placeholder({})", i),
                    TypeInfo::Wildcard => write!(f, "_"),
                    TypeInfo::Void => write!(f, "void"),
                    TypeInfo::Bool => write!(f, "bool"),
                    &TypeInfo::Int(IntTypeInfo { signed, bits }) => {
                        let letter = match signed {
                            Signed::Signed => "i",
                            Signed::Unsigned => "u",
                        };
                        write!(f, "{}{}", letter, bits)
                    }
                    TypeInfo::Pointer(inner) => write!(f, "&{}", self.store.format_type(*inner)),
                    TypeInfo::Tuple(info) => write_tuple(&self.store, f, &info.fields),
                    TypeInfo::Function(info) => {
                        write_tuple(&self.store, f, &info.params)?;
                        write!(f, " -> {}", self.store.format_type(info.ret))
                    }
                    TypeInfo::Array(info) => write!(f, "[{}; {}]", self.store.format_type(info.inner), info.length),
                    TypeInfo::Struct(info) => write!(f, "{}", info.decl.id.string),
                }
            }
        }

        Wrapped { store: self, ty }
    }
}

impl<'a> Index<Type> for TypeStore<'a> {
    type Output = BasicTypeInfo<'a>;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index]
    }
}

#[derive(Debug, Default)]
pub struct ItemStore<'a> {
    /// The root scope of the program, contains all top level modules. This scope is separate from the normal module
    /// scopes so items declared in those modules can shadow the root modules.
    pub root_scope: Scope<'static, ScopedItem>,

    pub modules: Arena<Module, CollectedModule>,
    pub funcs: Arena<Function, FunctionDecl<'a>>,
    pub consts: Arena<Const, ConstDecl<'a>>,
}

#[derive(Debug, Default)]
pub struct CollectedModule {
    /// The scope that only contains items actually defined in this module.
    /// Should only be used as intermediate result while constructing the cst.
    pub local_scope: Scope<'static, ScopedItem>,

    /// The real module scope, including top level modules, imports and locally defined items
    pub scope: Scope<'static, ScopedItem>,

    /// The set of functions defined in this module that need to have code generated
    pub codegen_funcs: Vec<Function>,
}

#[derive(Debug, Copy, Clone)]
pub enum ScopeKind {
    Local,
    Real,
}

impl<'a> ItemStore<'a> {
    // Resolve a given path to a ScopedItem. This includes mapping primitive types.
    pub fn resolve_path<'p>(
        &self,
        scope_kind: ScopeKind,
        scope: &Scope<ScopedItem>,
        path: &'p ast::Path,
    ) -> Result<'p, ScopedItem> {
        //real paths
        let scope = path.parents.iter().try_fold(scope, |scope, id| {
            let &item = scope.find(Some(&self.root_scope), id)?;

            if let ScopedItem::Module(module) = item {
                let module = &self.modules[module];
                let next_scope = match scope_kind {
                    ScopeKind::Local => &module.local_scope,
                    ScopeKind::Real => &module.scope,
                };
                Ok(next_scope)
            } else {
                Err(item.err_unexpected_kind(error::ItemType::Module, path))
            }
        })?;

        scope.find(Some(&self.root_scope), &path.id).map(|&v| v)
    }

    pub fn resolve_path_type(&self, scope_kind: ScopeKind, scope: &Scope<ScopedItem>, path: &'a ast::Path) -> Result<'a, Type> {
        let item = self.resolve_path(scope_kind, scope, path)?;
        if let ScopedItem::Type(ty) = item {
            Ok(ty)
        } else {
            Err(item.err_unexpected_kind(error::ItemType::Type, path))
        }
    }

    pub fn resolve_type(
        &self,
        scope_kind: ScopeKind,
        scope: &Scope<ScopedItem>,
        types: &mut TypeStore,
        ty: &'a ast::Type,
    ) -> Result<'a, Type> {
        match &ty.kind {
            ast::TypeKind::Wildcard => Ok(types.ty_wildcard),

            ast::TypeKind::Void => Ok(types.ty_void),
            ast::TypeKind::Bool => Ok(types.ty_bool),
            &ast::TypeKind::Int(info) => Ok(types.define_type(TypeInfo::Int(info))),

            ast::TypeKind::Path(path) => self.resolve_path_type(scope_kind, scope, path),
            ast::TypeKind::Ref(inner) => {
                let inner = self.resolve_type(scope_kind, scope, types, &*inner)?;
                Ok(types.define_type(TypeInfo::Pointer(inner)))
            }
            ast::TypeKind::Tuple { fields } => {
                let fields = fields.iter()
                    .map(|field| self.resolve_type(scope_kind, scope, types, field))
                    .try_collect()?;

                Ok(types.define_type(TypeInfo::Tuple(TupleTypeInfo { fields })))
            }
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|param| self.resolve_type(scope_kind, scope, types, param))
                    .try_collect()?;
                let ret = self.resolve_type(scope_kind, scope, types, ret)?;

                Ok(types.define_type(TypeInfo::Function(FunctionTypeInfo { params, ret })))
            }
            ast::TypeKind::Array { inner, length } => {
                let inner = self.resolve_type(scope_kind, scope, types, inner)?;
                Ok(types.define_type(TypeInfo::Array(ArrayTypeInfo { inner, length: *length })))
            }
        }
    }
}

/// Any item that can be found in a scope.
#[derive(Debug, Copy, Clone)]
pub enum ScopedItem {
    Module(Module),
    Type(Type),
    Value(ScopedValue),
}

/// A value that can be found in a scope. All possible values should be convertible to an `LRValue`,
/// but there is an extra step of indirection because scopes are build before an `ir::Program` is created so the
/// corresponding values for functions and consts cannot be created yet.
#[derive(Debug, Copy, Clone)]
pub enum ScopedValue {
    Function(Function),
    Const(Const),
    Immediate(LRValue),
    TypeVar(TypeVar),
}

impl ScopedItem {
    /// Return an error because this item is not of the expected kind.
    pub fn err_unexpected_kind(self, expected: error::ItemType, path: &ast::Path) -> Error<'_> {
        let actual = match self {
            ScopedItem::Module(_) => error::ItemType::Module,
            ScopedItem::Type(_) => error::ItemType::Type,
            ScopedItem::Value(_) => error::ItemType::Value,
        };

        assert_ne!(actual, expected);

        Error::UnexpectedItemType { expected, actual, path }
    }
}

/// Information about a type in the high-level language. The type parameter T is the key used to represent nested types.
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum TypeInfo<'ast, T> {
    /// A temporary placeholder used during cst construction.
    Placeholder(usize),

    /// The wildcard type, used to declare types without known inner types, eg. `&_` or `(_, _)`.
    Wildcard,

    Void,
    Bool,
    Int(IntTypeInfo),

    Pointer(T),

    Tuple(TupleTypeInfo<T>),
    Function(FunctionTypeInfo<T>),
    Array(ArrayTypeInfo<T>),

    Struct(StructTypeInfo<'ast>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Constructor)]
pub struct IntTypeInfo {
    pub signed: Signed,
    pub bits: u32,
}

impl IntTypeInfo {
    pub const I8: IntTypeInfo = IntTypeInfo { signed: Signed::Signed, bits: 8 };
    pub const I16: IntTypeInfo = IntTypeInfo { signed: Signed::Signed, bits: 16 };
    pub const I32: IntTypeInfo = IntTypeInfo { signed: Signed::Signed, bits: 32 };
    pub const U8: IntTypeInfo = IntTypeInfo { signed: Signed::Unsigned, bits: 8 };
    pub const U16: IntTypeInfo = IntTypeInfo { signed: Signed::Unsigned, bits: 16 };
    pub const U32: IntTypeInfo = IntTypeInfo { signed: Signed::Unsigned, bits: 32 };

    pub const ISIZE: IntTypeInfo = IntTypeInfo { signed: Signed::Signed, bits: PTR_SIZE_BITS };
    pub const USIZE: IntTypeInfo = IntTypeInfo { signed: Signed::Unsigned, bits: PTR_SIZE_BITS };
}

impl<'ast, T: Copy> TypeInfo<'ast, T> {
    pub fn unwrap_int(&self) -> Option<IntTypeInfo> {
        match self {
            &TypeInfo::Int(info) => Some(info),
            _ => None,
        }
    }

    pub fn unwrap_ptr(&self) -> Option<T> {
        match self {
            TypeInfo::Pointer(inner) => Some(*inner),
            _ => None,
        }
    }
}

impl<'ast, T> TypeInfo<'ast, T> {
    pub fn unwrap_func(&self) -> Option<&FunctionTypeInfo<T>> {
        match self {
            TypeInfo::Function(inner) => Some(inner),
            _ => None,
        }
    }
}

impl<'ast, T> TypeInfo<'ast, T> {
    /// Map the representation for nested types while keeping the structure.
    pub fn map_ty<R>(&self, f: &mut impl FnMut(&T) -> R) -> TypeInfo<'ast, R> {
        match self {
            TypeInfo::Placeholder(_) => unreachable!(),
            TypeInfo::Wildcard => TypeInfo::Wildcard,
            TypeInfo::Void => TypeInfo::Void,
            TypeInfo::Bool => TypeInfo::Bool,
            &TypeInfo::Int(info) => TypeInfo::Int(info),
            TypeInfo::Pointer(inner) => TypeInfo::Pointer(f(inner)),
            TypeInfo::Tuple(info) => TypeInfo::Tuple(TupleTypeInfo {
                fields: info.fields.iter().map(f).collect()
            }),
            TypeInfo::Function(info) => TypeInfo::Function(FunctionTypeInfo {
                ret: f(&info.ret),
                params: info.params.iter().map(f).collect(),
            }),
            TypeInfo::Array(info) => TypeInfo::Array(ArrayTypeInfo {
                inner: f(&info.inner),
                length: info.length,
            }),
            TypeInfo::Struct(info) => TypeInfo::Struct(info.clone()),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct TupleTypeInfo<T> {
    pub fields: Vec<T>,
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct FunctionTypeInfo<T> {
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct ArrayTypeInfo<T> {
    pub inner: T,
    pub length: u32,
}

#[derive(Debug, Clone)]
pub struct StructTypeInfo<'ast> {
    pub decl: &'ast ast::Struct,
    pub fields: Vec<StructFieldInfo<'ast>>,
}

#[derive(Debug, Copy, Clone)]
pub struct StructFieldInfo<'ast> {
    pub id: &'ast str,
    pub ty: Type,
}

impl<'ast> StructTypeInfo<'ast> {
    pub fn find_field_index(&self, index: &str) -> Option<usize> {
        self.fields.iter()
            .position(|field| field.id == index)
    }
}

impl<'ast> Hash for StructTypeInfo<'ast> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.decl, state)
    }
}

impl<'ast> PartialEq for StructTypeInfo<'ast> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.decl, other.decl)
    }
}

impl<'ast> Eq for StructTypeInfo<'ast> {}

#[derive(Debug)]
pub struct FunctionDecl<'ast> {
    pub ty: Type,
    pub func_ty: FunctionTypeInfo<Type>,
    pub ast: &'ast ast::Function,
}

#[derive(Debug)]
pub struct ConstDecl<'ast> {
    pub ty: Type,
    pub ast: &'ast ast::Const,
}
