use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Index;

use itertools::Itertools;

use crate::front::{ast, error};
use crate::front::error::{Error, Result};
use crate::front::lower::LRValue;
use crate::front::scope::Scope;
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

type BasicTypeInfo<'a> = TypeInfo<Type, StructTypeInfo<'a>>;

#[derive(Debug)]
pub struct TypeStore<'a> {
    types: ArenaSet<Type, BasicTypeInfo<'a>>,

    ty_void: Type,
    ty_bool: Type,
    ty_byte: Type,
    ty_int: Type,
}

impl<'a> Default for TypeStore<'a> {
    fn default() -> Self {
        let mut types = ArenaSet::default();
        let ty_void = types.push(TypeInfo::Void);
        let ty_bool = types.push(TypeInfo::Bool);
        let ty_byte = types.push(TypeInfo::Byte);
        let ty_int = types.push(TypeInfo::Int);
        Self { types, ty_void, ty_bool, ty_byte, ty_int }
    }
}

impl<'a> TypeStore<'a> {
    pub fn type_void(&self) -> Type {
        self.ty_void
    }

    pub fn type_bool(&self) -> Type {
        self.ty_bool
    }

    pub fn type_byte(&self) -> Type {
        self.ty_byte
    }

    pub fn type_int(&self) -> Type {
        self.ty_int
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
                    TypeInfo::Placeholder(_) => panic!("tried to format placeholder type"),
                    TypeInfo::Void => write!(f, "void"),
                    TypeInfo::Bool => write!(f, "bool"),
                    TypeInfo::Byte => write!(f, "byte"),
                    TypeInfo::Int => write!(f, "int"),
                    TypeInfo::Pointer(inner) => write!(f, "&{}", self.store.format_type(*inner)),
                    TypeInfo::Tuple(info) => write_tuple(&self.store, f, &info.fields),
                    TypeInfo::Function(info) => {
                        write_tuple(&self.store, f, &info.params)?;
                        write!(f, " -> {}", self.store.format_type(info.ret))
                    }
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

    pub fn resolve_type(
        &self,
        scope_kind: ScopeKind,
        scope: &Scope<'static, ScopedItem>,
        types: &mut TypeStore,
        ty: &'a ast::Type,
    ) -> Result<'a, Type> {
        match &ty.kind {
            ast::TypeKind::Void => Ok(types.ty_void),
            ast::TypeKind::Bool => Ok(types.ty_bool),
            ast::TypeKind::Byte => Ok(types.ty_byte),
            ast::TypeKind::Int => Ok(types.ty_int),
            ast::TypeKind::Path(path) => {
                let item = self.resolve_path(scope_kind, scope, path)?;
                if let ScopedItem::Type(ty) = item {
                    Ok(ty)
                } else {
                    Err(item.err_unexpected_kind(error::ItemType::Type, path))
                }
            }
            ast::TypeKind::Ref(inner) => {
                let inner = self.resolve_type(scope_kind, scope, types, &*inner)?;
                Ok(types.types.push(TypeInfo::Pointer(inner)))
            }
            ast::TypeKind::Tuple { fields } => {
                let fields = fields.iter()
                    .map(|field| self.resolve_type(scope_kind, scope, types, field))
                    .try_collect()?;

                Ok(types.types.push(TypeInfo::Tuple(TupleTypeInfo { fields })))
            }
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|param| self.resolve_type(scope_kind, scope, types, param))
                    .try_collect()?;
                let ret = self.resolve_type(scope_kind, scope, types, ret)?;

                Ok(types.types.push(TypeInfo::Function(FunctionTypeInfo { params, ret })))
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

        error::Error::UnexpectedItemType { expected, actual, path }
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum TypeInfo<T, S> {
    Placeholder(usize),

    Void,
    Bool,
    Byte,
    Int,

    Pointer(T),

    Tuple(TupleTypeInfo<T>),
    Function(FunctionTypeInfo<T>),
    Struct(S),
}

impl<T: Copy, S> TypeInfo<T, S> {
    pub fn unwrap_ptr(&self) -> Option<T> {
        match self {
            TypeInfo::Pointer(inner) => Some(*inner),
            _ => None,
        }
    }
}

impl<T, S> TypeInfo<T, S> {
    pub fn unwrap_func(&self) -> Option<&FunctionTypeInfo<T>> {
        match self {
            TypeInfo::Function(inner) => Some(inner),
            _ => None,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct TupleTypeInfo<T> {
    pub fields: Vec<T>
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct FunctionTypeInfo<T> {
    pub params: Vec<T>,
    pub ret: T,
}

#[derive(Debug, Clone)]
pub struct StructTypeInfo<'a> {
    pub decl: &'a ast::Struct,
    pub fields: Vec<(&'a str, Type)>,
}

impl<'a> StructTypeInfo<'a> {
    pub fn fiend_field(&self, index: &str) -> Option<(u32, Type)> {
        self.fields.iter().enumerate()
            .find(|(_, (id, _))| *id == index)
            .map(|(i, (_, ty))| (i as u32, *ty))
    }
}

impl<'a> Hash for StructTypeInfo<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.decl, state)
    }
}

impl<'a> PartialEq for StructTypeInfo<'a> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.decl, other.decl)
    }
}

impl<'a> Eq for StructTypeInfo<'a> {}

#[derive(Debug)]
pub struct FunctionDecl<'a> {
    pub ty: Type,
    pub func_ty: FunctionTypeInfo<Type>,
    pub ast: &'a ast::Function,
}

#[derive(Debug)]
pub struct ConstDecl<'a> {
    pub ty: Type,
    pub ast: &'a ast::Const,
}
