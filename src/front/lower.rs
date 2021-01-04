use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

use itertools::Itertools;

use crate::front::{ast, cst};
use crate::front::ast::ExpressionKind;
use crate::front::cst::{CollectedProgram, FunctionTypeInfo, ScopedValue, StructTypeInfo, TupleTypeInfo, TypeInfo, TypeStore};
use crate::front::error::{Error, Result};
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
            ph @ TypeInfo::Placeholder(_) => panic!("tried to map type {:?}", ph),
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

pub fn lower<'a>(store: TypeStore<'a>, cst: CollectedProgram<'a>, main_func: cst::Function) -> Result<'a, ir::Program> {
    let mut store = MappingTypeStore::wrap(store);

    let mut ir_prog = ir::Program::default();

    //create ir function for each cst function
    let all_funcs: HashMap<cst::Function, (ir::Function, LRValue)> = cst.funcs.iter().map(|(cst_func, decl)| {
        assert!(!decl.ast.ext, "TODO implement extern funcs again");

        let ir_ty = store.map_type_func(&mut ir_prog, &decl.func_ty);
        let ir_func = ir::FunctionInfo::new(ir_ty, &mut ir_prog);
        let ir_func = ir_prog.define_func(ir_func);

        let lr = LRValue::Right(TypedValue { ty: decl.ty, ir: ir::Value::Func(ir_func) });
        (cst_func, (ir_func, lr))
    }).collect();

    //create ir data for each cst const
    let all_consts: HashMap<cst::Const, LRValue> = cst.consts.iter()
        .map(|(cst_const, decl)| {
            let lr = create_constant(&mut store, &mut ir_prog, decl)?;
            Ok((cst_const, lr))
        }).try_collect()?;

    //set main function
    ir_prog.main = all_funcs.get(&main_func).unwrap().0;

    //mapping from cst values to ir values
    let map_value = &|value: ScopedValue| -> LRValue {
        match
        value {
            ScopedValue::Function(func) => all_funcs.get(&func).unwrap().1,
            ScopedValue::Const(cst) => *all_consts.get(&cst).unwrap(),
            ScopedValue::Immediate(value) => value,
        }
    };

    //actually generate code
    for (_, module) in &cst.modules {
        for &cst_func in &module.codegen_funcs {
            let func_decl = &cst.funcs[cst_func];
            assert!(func_decl.ast.body.is_some(), "TODO implement extern funcs without body again");

            let mut lower = LowerFuncState {
                prog: &mut ir_prog,
                cst: &cst,
                module_scope: &module.scope,
                store: &mut store,
                map_value,

                ret_ty: func_decl.func_ty.ret,
                ir_func: all_funcs.get(&cst_func).unwrap().0,
                loop_stack: vec![],
            };
            lower.append_func(func_decl)?;
        }
    }

    Ok(ir_prog)
}

fn create_constant<'a>(store: &mut MappingTypeStore<'a>, ir_prog: &mut ir::Program, decl: &cst::ConstDecl<'a>) -> Result<'a, LRValue> {
    let ty = decl.ty;
    let init = &decl.ast.init;

    let lr = match &init.kind {
        ExpressionKind::IntLit { value } => {
            check_integer_type(&store, init, ty)?;
            let value = value.parse::<i32>()
                .map_err(|_| Error::InvalidLiteral {
                    span: init.span,
                    lit: value.clone(),
                    ty: store.format_type(ty).to_string(),
                })?;
            let ty_ir = store.map_type(ir_prog, ty);
            LRValue::Right(TypedValue { ty, ir: ir::Value::Const(ir::Const { ty: ty_ir, value }) })
        }
        ExpressionKind::BoolLit { value } => {
            check_type_match(&store, init, store.type_bool(), ty)?;
            let ty_bool_ir = ir_prog.type_bool();
            let value = *value as i32;
            LRValue::Right(TypedValue { ty, ir: ir::Value::Const(ir::Const { ty: ty_bool_ir, value }) })
        }
        ExpressionKind::StringLit { value } => {
            let ty_byte = store.type_byte();
            let ty_byte_ptr = store.define_type_ptr(ty_byte);
            check_type_match(&store, init, ty_byte_ptr, ty)?;

            let ty_byte_ir = store.map_type(ir_prog, ty_byte);
            let ty_byte_ptr_ir = store.map_type(ir_prog, ty_byte_ptr);

            let bytes = value.bytes().collect_vec();
            let data = ir::DataInfo { ty: ty_byte_ptr_ir, inner_ty: ty_byte_ir, bytes };
            let data = ir_prog.define_data(data);
            LRValue::Right(TypedValue { ty, ir: ir::Value::Data(data) })
        },
        ExpressionKind::Null => {
            check_ptr_type(&store, init, ty)?;
            let ty_ir = store.map_type(ir_prog, ty);

            let cst = ir::Const { ty: ty_ir, value: 0 };
            LRValue::Right(TypedValue { ty, ir: ir::Value::Const(cst) })
        },
        _ => todo!("for now only simple literal constants are supported"),
    };

    Ok(lr)
}

fn check_type_match<'ast>(store: &TypeStore, expr: &'ast ast::Expression, expected: cst::Type, actual: cst::Type) -> Result<'ast, ()> {
    if expected != actual {
        return Err(Error::TypeMismatch {
            expression: expr,
            expected: store.format_type(expected).to_string(),
            actual: store.format_type(actual).to_string(),
        });
    }
    Ok(())
}

fn check_integer_type<'ast>(store: &TypeStore, expr: &'ast ast::Expression, actual: cst::Type) -> Result<'ast, ()> {
    match &store[actual] {
        TypeInfo::Byte | TypeInfo::Int => Ok(()),
        _ => Err(Error::ExpectIntegerType {
            expression: expr,
            actual: store.format_type(actual).to_string(),
        }),
    }
}

fn check_ptr_type<'ast>(store: &TypeStore, expr: &'ast ast::Expression, actual: cst::Type) -> Result<'ast, ()> {
    match &store[actual] {
        TypeInfo::Pointer(_) => Ok(()),
        _ => Err(Error::ExpectPointerType {
            expression: expr,
            actual: store.format_type(actual).to_string(),
        }),
    }
}