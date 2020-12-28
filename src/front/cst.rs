use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Index;

use itertools::Itertools;

use crate::front::{ast, error};
use crate::front::error::{Error, Result};
use crate::front::lower_func::TypedValue;
use crate::front::scope::Scope;
use crate::util::arena::{Arena, ArenaSet};

new_index_type!(pub Module);
new_index_type!(pub Type);
new_index_type!(pub Function);

#[derive(Debug)]
pub struct TypeStore<'a> {
    types: ArenaSet<Type, TypeInfo<'a>>,

    ty_void: Type,
    ty_bool: Type,
}

impl<'a> TypeStore<'a> {
    pub fn new() -> Self {
        let mut types = ArenaSet::default();
        let ty_void = types.push(TypeInfo::Void);
        let ty_bool = types.push(TypeInfo::Bool);
        Self { types, ty_void, ty_bool }
    }

    pub fn type_void(&self) -> Type {
        self.ty_void
    }

    pub fn type_bool(&self) -> Type {
        self.ty_bool
    }

    pub fn define_type(&mut self, info: TypeInfo<'a>) -> Type {
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

        fn write_tuple(store: &TypeStore, f: &mut Formatter<'_>, fields: &Vec<Type>) -> std::fmt::Result {
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
    type Output = TypeInfo<'a>;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index]
    }
}

#[derive(Debug)]
pub struct CollectedProgram<'a> {
    pub modules: Arena<Module, CollectedModule>,
    pub funcs: Arena<Function, FunctionDecl<'a>>,
}

#[derive(Debug)]
pub struct CollectedModule {
    //the module scope, including imports
    pub scope: Scope<'static, ScopedItem>,
    pub funcs: Vec<Function>,
}

impl<'a> CollectedProgram<'a> {
    // Resolve a given path to a ScopedItem. This includes mapping primitive types.
    pub fn resolve_path<'p>(&self, scope: &Scope<'static, ScopedItem>, store: &mut TypeStore, path: &'p ast::Path) -> Result<'p, ScopedItem> {
        //TODO it would be nicer if primitive types were separate from paths, maybe change the parser
        //primitive types
        if path.parents.is_empty() {
            match &*path.id.string {
                "void" => return Ok(ScopedItem::Type(store.types.push(TypeInfo::Void))),
                "bool" => return Ok(ScopedItem::Type(store.types.push(TypeInfo::Bool))),
                "int" => return Ok(ScopedItem::Type(store.types.push(TypeInfo::Int))),
                _ => {}
            }
        }

        //real paths
        let scope = path.parents.iter().try_fold(scope, |scope, id| {
            let &item = scope.find(id)?;

            if let ScopedItem::Module(module) = item {
                Ok(&self.modules[module].scope)
            } else {
                Err(item.err_unexpected_kind(error::ItemType::Module, path))
            }
        })?;

        scope.find(&path.id).map(|&v| v)
    }

    pub fn resolve_type(&self, scope: &Scope<'static, ScopedItem>, store: &mut TypeStore, ty: &'a ast::Type) -> Result<'a, Type> {
        match &ty.kind {
            ast::TypeKind::Path(path) => {
                let item = self.resolve_path(scope, store, path)?;
                if let ScopedItem::Type(ty) = item {
                    Ok(ty)
                } else {
                    Err(item.err_unexpected_kind(error::ItemType::Type, path))
                }
            }
            ast::TypeKind::Ref(inner) => {
                let inner = self.resolve_type(scope, store, &*inner)?;
                Ok(store.types.push(TypeInfo::Pointer(inner)))
            }
            ast::TypeKind::Tuple { fields } => {
                let fields = fields.iter()
                    .map(|field| self.resolve_type(scope, store, field))
                    .try_collect()?;

                Ok(store.types.push(TypeInfo::Tuple(TupleTypeInfo { fields })))
            }
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|param| self.resolve_type(scope, store, param))
                    .try_collect()?;
                let ret = self.resolve_type(scope, store, ret)?;

                Ok(store.types.push(TypeInfo::Function(FunctionTypeInfo { params, ret })))
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ScopedItem {
    Module(Module),
    Type(Type),
    Value(TypedValue),
}

impl ScopedItem {
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
pub enum TypeInfo<'a> {
    Placeholder(usize),

    Void,
    Bool,
    Byte,
    Int,

    Pointer(Type),

    Tuple(TupleTypeInfo),
    Function(FunctionTypeInfo),
    Struct(StructTypeInfo<'a>),
}

impl<'a> TypeInfo<'a> {
    pub fn unwrap_ptr(&self) -> Option<Type> {
        match self {
            TypeInfo::Pointer(inner) => Some(*inner),
            _ => None,
        }
    }

    pub fn unwrap_func(&self) -> Option<&FunctionTypeInfo> {
        match self {
            TypeInfo::Function(inner) => Some(inner),
            _ => None,
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct TupleTypeInfo {
    pub fields: Vec<Type>
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct FunctionTypeInfo {
    pub params: Vec<Type>,
    pub ret: Type,
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

//TODO we need to break this up for lifetime purposes
#[derive(Debug)]
pub struct FunctionDecl<'a> {
    pub func: Function,
    //TODO do we actually need a 'ty' field here at all?
    pub ty: Type,
    pub func_ty: FunctionTypeInfo,
    pub ast: &'a ast::Function,
}