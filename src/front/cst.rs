use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::ops::Index;

use indexmap::map::IndexMap;
use itertools::Itertools;

use crate::front;
use crate::front::ast::{Declaration, Function, Struct, UseDecl};
use crate::front::scope::Scope;
use crate::mid::ir;
use crate::mid::ir::{FunctionType, TupleType};
use crate::util::arena::{Arena, ArenaSet};

new_index_type!(pub Type);
new_index_type!(pub StructType);
new_index_type!(pub Module);

#[derive(Debug, Default)]
pub struct Store<'a> {
    pub modules: Arena<Module, ModuleContent<'a>>,
    pub types: ArenaSet<Type, TypeInfo<'a>>,
    pub struct_types: Arena<StructType, StructTypeInfo<'a>>,
}

pub type Program<'a> = front::Program<Module>;

impl<'a> Store<'a> {
    ///Define the given (deduplicated) type.
    pub fn define_type(&mut self, info: TypeInfo<'a>) -> Type {
        self.types.push(info)
    }

    ///Define a new distinct placeholder type
    pub fn new_placeholder_type(&mut self) -> Type {
        self.types.push(TypeInfo::PlaceHolder(self.types.len()))
    }

    ///Replace a previously created placeholder with a real type.
    /// The new type must be distinct from all existing types.
    pub fn fill_placeholder_type(&mut self, ty: Type, info: TypeInfo<'a>) {
        let prev = self.types.replace(ty, info);
        assert!(matches!(prev, TypeInfo::PlaceHolder(_)), "Tried to replace non-placeholder type {:?}", prev);
    }

    //TODO maybe cache this mapping somewhere
    //Convert the given [cst::Type] to a [ir::Type].
    pub fn as_ir_type(&self, prog: &mut ir::Program, ty: Type) -> ir::Type {
        match &self.types[ty] {
            TypeInfo::Bool => prog.type_bool(),
            TypeInfo::Int => prog.define_type_int(32),
            TypeInfo::Void => prog.type_void(),
            TypeInfo::Struct(StructTypeInfo { fields, .. }) => {
                prog.define_type_tuple(TupleType {
                    fields: fields.values()
                        .map(|field| self.as_ir_type(prog, *field))
                        .collect_vec()
                })
            }
            TypeInfo::Func(func_type_info) => {
                prog.define_type_func(self.as_ir_type_func(prog, func_type_info))
            }
            TypeInfo::Tuple(fields) => {
                prog.define_type_tuple(TupleType {
                    fields: fields.iter()
                        .map(|field| self.as_ir_type(prog, *field))
                        .collect_vec()
                })
            }
            TypeInfo::PlaceHolder(_) => {
                panic!("Cannot convert placeholder type to ir type")
            }
        }
    }

    //TODO comment
    pub fn as_ir_type_func(&self, prog: &mut ir::Program, func: &FuncTypeInfo) -> ir::FunctionType {
        FunctionType {
            params: func.params.iter()
                .map(|param| self.as_ir_type(prog, *param))
                .collect_vec(),
            ret: self.as_ir_type(prog, func.ret),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum TypeInfo<'a, 'c> {
    Void,
    Bool,
    Int,
    //TODO consistently introduce subtypes or not
    Struct(StructTypeInfo),
    Func(FuncTypeInfo),
    Tuple(Vec<Type>),
    //has an index field to prevent deduplication
    PlaceHolder(usize),
}

#[derive(Debug, Clone)]
pub struct StructTypeInfo<'a, 'c> {
    pub decl: &'c StructDeclInfo<'a>,
    pub fields: IndexMap<&'a str, Type>,
}

impl PartialEq for StructTypeInfo<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.decl.item == other.decl.item
    }
}

impl Eq for StructTypeInfo<'_, '_> {}

impl Hash for StructTypeInfo<'_, '_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.decl.item.hash(state)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FuncTypeInfo {
    pub params: Vec<Type>,
    pub ret: Type,
}

#[derive(Debug, Copy, Clone)]
pub enum ItemInfo {
    //TODO what option should store what data here?
    FunctionDef(),
    TypeDef(Type),
    ConstDef(),
}

#[derive(Debug, Default)]
pub struct ModuleContent<'a> {
    //TODO don't forget to add imported items to scope before actually lowering
    //TODO populate this scope at some point
    pub scope_defines: Scope<'a, ScopedItem>,
    pub use_decls: Vec<&'a UseDecl>,
    pub struct_decls: Vec<StructDeclInfo<'a>>,
    pub func_decls: Vec<FuncDeclInfo<'a>>,
    pub const_decls: Vec<ConstDeclInfo<'a>>,
}

//TODO
pub enum ScopedItem {
    Module(Module),
    Type(Type),
    Value(ir::Value),
}