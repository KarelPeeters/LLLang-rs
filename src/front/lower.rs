use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use crate::front;
use crate::front::{ast, cst};
use crate::front::collect::collect;
use crate::front::cst::{FunctionTypeInfo, ScopedValue, StructTypeInfo, TupleTypeInfo, TypeInfo, TypeStore};
use crate::front::error::Result;
use crate::front::lower_func::LowerFuncState;
use crate::mid::ir;

#[derive(Debug, Copy, Clone)]
pub enum LRValue {
    Left(TypedValue),
    Right(TypedValue),
}

#[derive(Debug, Copy, Clone)]
pub struct TypedValue {
    pub ty: cst::Type,
    pub ir: ir::Value,
}

//TODO maybe move this structure somewhere else?
pub struct MappingTypeStore<'a> {
    pub inner: TypeStore<'a>,
    map: HashMap<cst::Type, ir::Type>,
}

impl<'a> Deref for MappingTypeStore<'a> {
    type Target = TypeStore<'a>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'a> DerefMut for MappingTypeStore<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<'a> MappingTypeStore<'a> {
    fn wrap(store: TypeStore<'a>) -> Self {
        Self { inner: store, map: Default::default() }
    }

    pub fn map_type_func(&mut self, prog: &mut ir::Program, ty: &FunctionTypeInfo) -> ir::FunctionType {
        let params = ty.params.iter()
            .map(|&p| self.map_type(prog, p))
            .collect();
        let ret = self.map_type(prog, ty.ret);

        ir::FunctionType { params, ret }
    }

    pub fn map_type(&mut self, prog: &mut ir::Program, ty: cst::Type) -> ir::Type {
        //TODO is there a way to avoid the clones here?
        if let Some(ir_ty) = self.map.get(&ty) {
            return *ir_ty;
        }

        let ir_ty = match &self.inner[ty] {
            TypeInfo::Placeholder(_) => panic!("tried to map placeholder type"),
            TypeInfo::Void => prog.type_void(),
            TypeInfo::Bool => prog.type_bool(),
            TypeInfo::Byte => prog.define_type_int(8),
            TypeInfo::Int => prog.define_type_int(32),
            &TypeInfo::Pointer(inner) => {
                let inner = self.map_type(prog, inner);
                prog.define_type_ptr(inner)
            }
            TypeInfo::Tuple(TupleTypeInfo { fields }) => {
                let fields = fields.clone().iter()
                    .map(|&f_ty| self.map_type(prog, f_ty))
                    .collect();
                prog.define_type_tuple(ir::TupleType { fields })
            }
            TypeInfo::Function(info) => {
                let info = info.clone();
                let func_ty = self.map_type_func(prog, &info);
                prog.define_type_func(func_ty)
            }
            TypeInfo::Struct(StructTypeInfo { decl: _, fields }) => {
                let fields = fields.clone().iter()
                    .map(|&(_, f_ty)| self.map_type(prog, f_ty))
                    .collect();
                prog.define_type_tuple(ir::TupleType { fields })
            }
        };

        self.map.insert(ty, ir_ty);
        return ir_ty;
    }
}


pub fn lower(prog: &front::Program<Option<ast::ModuleContent>>) -> Result<ir::Program> {
    let (store, cst) = collect(prog)?;
    let mut store = MappingTypeStore::wrap(store);

    let mut ir_prog = ir::Program::default();

    //create ir function for each cst function
    let all_funcs: HashMap<cst::Function, ir::Function> = cst.funcs.iter().map(|(cst_func, func_decl)| {
        assert!(!func_decl.ast.ext, "TODO implement extern funcs again");

        let ir_ty = store.map_type_func(&mut ir_prog, &func_decl.func_ty);
        let ir_func = ir::FunctionInfo::new(ir_ty, &mut ir_prog);
        let ir_func = ir_prog.define_func(ir_func);

        (cst_func, ir_func)
    }).collect();

    let map_value = &|value: ScopedValue| -> LRValue {
        match value {
            ScopedValue::Function(func) => {
                let ir_func = *all_funcs.get(&func).unwrap();
                LRValue::Right(TypedValue { ty: cst.funcs[func].ty, ir: ir::Value::Func(ir_func) })
            },
            ScopedValue::Immediate(value) => value,
        }
    };

    //actually generate code
    for (_, module) in &cst.modules {
        for &cst_func in &module.codegen_funcs {
            let func_decl = &cst.funcs[cst_func];
            assert!(func_decl.ast.body.is_some(), "TODO implement extern funcs without body again");

            let &ir_func = all_funcs.get(&cst_func).unwrap();

            let mut lower = LowerFuncState {
                prog: &mut ir_prog,
                cst: &cst,
                module_scope: &module.scope,
                store: &mut store,
                map_value,

                ret_ty: func_decl.func_ty.ret,
                ir_func,
                loop_stack: vec![],
            };
            lower.append_func(func_decl)?;
        }
    }

    Ok(ir_prog)
}