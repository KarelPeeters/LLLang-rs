use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use itertools::Itertools;

use crate::front::{ast, cst};
use crate::front::cst::{ArrayTypeInfo, FunctionTypeInfo, IntTypeInfo, ScopedValue, StructTypeInfo, TupleTypeInfo, TypeInfo, TypeStore};
use crate::front::error::{Error, InvalidLiteralReason, Result};
use crate::front::lower_func::LowerFuncState;
use crate::front::type_func::TypeFuncState;
use crate::mid::ir;
use crate::mid::ir::Signed;
use crate::mid::util::bit_int::{BitInt, IStorage, UStorage};

/// The main representation of values during lowering. Contains the actual `ir::Value`, the `cst::Type` and whether this
/// is an LValue of RValue. LValues are values that can appear on the left side of assignments, RValues are those that cannot.
/// This concept is orthogonal to mutability.
/// It's also possible to think of an LValue as a pointer that looks like it has the dereferenced type and is
/// dereferenced automatically when required.
#[derive(Debug, Copy, Clone)]
pub enum LRValue {
    Left(TypedValue),
    Right(TypedValue),
}

impl LRValue {
    /// Get the type of this value as seen by the end user, taking into account that LValues are automatically
    /// dereferenced.
    pub fn ty(self, types: &TypeStore) -> cst::Type {
        match self {
            LRValue::Left(value) => types[value.ty].unwrap_ptr()
                .unwrap_or_else(|| panic!("LRValue::Left({:?}) should have pointer type", value)),
            LRValue::Right(value) => value.ty,
        }
    }

    /// Get the IR type of this value as seen by the end user.
    /// For LValues we don't know the type, since pointers are untyped.
    pub fn ty_ir(self, prog: &ir::Program) -> Option<ir::Type> {
        match self {
            LRValue::Left(_) => None,
            LRValue::Right(typed_value) => Some(prog.type_of_value(typed_value.ir)),
        }
    }
}

/// A `ir::Value` with its corresponding `cst::Type`. The `ir::Value` itself doesn't contain enough information because
/// type information is lost when converting `cst::Type` to `ir::Type`.
#[derive(Debug, Copy, Clone)]
pub struct TypedValue {
    pub ty: cst::Type,
    pub ir: ir::Value,
}

/// A wrapped around `TypeStore` that can convert `cst::Type` to `ir::Type` and keeps a cache of this mapping.
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

    pub fn map_type_func(&mut self, prog: &mut ir::Program, ty: &FunctionTypeInfo<cst::Type>) -> ir::FunctionType {
        let params = ty.params.iter()
            .map(|&p| self.map_type(prog, p))
            .collect();
        let ret = self.map_type(prog, ty.ret);

        ir::FunctionType { params, ret }
    }

    pub fn map_type(&mut self, prog: &mut ir::Program, ty: cst::Type) -> ir::Type {
        if let Some(ir_ty) = self.map.get(&ty) {
            return *ir_ty;
        }

        let ir_ty = match &self.inner[ty] {
            ph @ TypeInfo::Placeholder(_) => panic!("tried to map type {:?}", ph),
            TypeInfo::Wildcard => panic!("tried to map wildcard to IR"),
            TypeInfo::Void => prog.ty_void(),
            TypeInfo::Bool => prog.ty_bool(),
            &TypeInfo::Int(IntTypeInfo { signed: _, bits }) => {
                // In the IR signed-ness is not a property of the type, only of the operations.
                prog.define_type_int(bits)
            }
            TypeInfo::Pointer(_) => prog.ty_ptr(),
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
                    .map(|field| self.map_type(prog, field.ty))
                    .collect();
                prog.define_type_tuple(ir::TupleType { fields })
            }
            &TypeInfo::Array(ArrayTypeInfo { inner, length }) => {
                let inner = self.map_type(prog, inner);
                prog.define_type_array(ir::ArrayType { inner, length })
            }
        };

        self.map.insert(ty, ir_ty);
        ir_ty
    }
}

/// The main entry point of the lowering pass that generates the `ir` code for a given `ResolvedProgram`.
pub fn lower(prog: cst::ResolvedProgram) -> Result<ir::Program> {
    let mut types = MappingTypeStore::wrap(prog.types);

    let mut ir_prog = ir::Program::default();

    //create ir function for each cst function
    let all_funcs: HashMap<cst::Function, (Option<ir::Function>, LRValue)> = prog.items.funcs.iter()
        .map(|(cst_func, decl)| {
            let r = map_function(&mut types, &mut ir_prog, &decl)?;
            Ok((cst_func, r))
        }).try_collect()?;

    //create ir data for each cst const
    let all_consts: HashMap<cst::Const, LRValue> = prog.items.consts.iter()
        .map(|(cst_const, decl)| {
            let value = lower_literal(&mut types, &mut ir_prog, &decl.ast.init, decl.ty)?;
            Ok((cst_const, value))
        }).try_collect()?;

    //set main function
    ir_prog.main = all_funcs.get(&prog.main_func).unwrap().0.ok_or(Error::MainFunctionMustHaveBody)?;

    //mapping from cst values to ir values
    let map_value = &|value: ScopedValue| -> LRValue {
        match value {
            ScopedValue::Function(func) => all_funcs.get(&func).unwrap().1,
            ScopedValue::Const(cst) => *all_consts.get(&cst).unwrap(),
            ScopedValue::Immediate(value) => value,
            ScopedValue::TypeVar(_) => panic!("tried to map TypeVar value to placeholder"),
        }
    };

    //type inference and code generation
    for (_, module) in &prog.items.modules {
        for &cst_func in &module.codegen_funcs {
            let func_decl = &prog.items.funcs[cst_func];

            if let Some(ir_func) = all_funcs.get(&cst_func).unwrap().0 {
                //build the type problem for expressions within the function
                let mut type_state = TypeFuncState {
                    items: &prog.items,
                    types: &mut types,

                    module_scope: &module.scope,
                    map_value,

                    ret_ty: func_decl.func_ty.ret,

                    expr_type_map: Default::default(),
                    decl_type_map: Default::default(),
                    problem: Default::default(),
                };
                type_state.visit_func(func_decl)?;

                let TypeFuncState {
                    problem,
                    expr_type_map,
                    decl_type_map,
                    ..
                } = type_state;

                //solve the problem
                let solution = problem.solve(&mut *types);

                //actually generate code
                LowerFuncState {
                    prog: &mut ir_prog,

                    items: &prog.items,
                    types: &mut types,

                    module_scope: &module.scope,
                    map_value,

                    ret_ty: func_decl.func_ty.ret,
                    ir_func,
                    loop_stack: vec![],

                    expr_type_map: &expr_type_map,
                    decl_type_map: &decl_type_map,
                    type_solution: solution,

                    func_debug_name: &func_decl.ast.id.string,
                }.lower_func(func_decl)?;
            }
        }
    }

    Ok(ir_prog)
}

fn map_function<'a>(
    store: &mut MappingTypeStore,
    prog: &mut ir::Program,
    decl: &cst::FunctionDecl<'a>,
) -> Result<'a, (Option<ir::Function>, LRValue)> {
    let ty_func_ir = store.map_type_func(prog, &decl.func_ty);

    let (func_ir, value_ir) = match (decl.ast.ext, decl.ast.body.is_some()) {
        (false, false) => Err(Error::MissingFunctionBody(decl.ast)),
        (true, false) => {
            let ir_ty = prog.define_type_func(ty_func_ir);
            let ext = ir::ExternInfo {
                name: decl.ast.id.string.clone(),
                ty: ir_ty,
            };
            Ok((None, ir::Value::Extern(prog.define_ext(ext))))
        }
        (ext, true) => {
            let mut func_ir = ir::FunctionInfo::new(ty_func_ir, prog);

            func_ir.debug_name = Some(decl.ast.id.string.clone());
            if ext {
                func_ir.global_name = Some(decl.ast.id.string.clone())
            }

            let func_ir = prog.define_func(func_ir);
            Ok((Some(func_ir), ir::Value::Func(func_ir)))
        }
    }?;

    Ok((func_ir, LRValue::Right(TypedValue { ty: decl.ty, ir: value_ir })))
}

// This is used both for const lowering and during lowering of literals in functions.
// This means we do some superfluous type checking for the latter but that's not a big deal.
// TODO use the full type solver for type checking constants as well at some point
//   (but still don't propagate between functions, just do something per-const so we at least emit the same errors)
pub fn lower_literal<'a>(
    types: &mut MappingTypeStore<'a>,
    ir_prog: &mut ir::Program,
    expr: &'a ast::Expression,
    ty: cst::Type,
) -> Result<'a, LRValue> {
    let result = match &expr.kind {
        ast::ExpressionKind::Null => {
            check_ptr_type(&types, expr, ty)?;

            let value_ir = ir_prog.const_null_ptr();
            LRValue::Right(TypedValue { ty, ir: value_ir.into() })
        }
        &ast::ExpressionKind::BoolLit { value } => {
            check_type_match(&types, expr, types.type_bool(), ty)?;

            let value_ir = ir_prog.const_bool(value);
            LRValue::Right(TypedValue { ty, ir: value_ir.into() })
        }
        ast::ExpressionKind::IntLit { value, ty: _ } => {
            let build_error = |types: &mut MappingTypeStore, reason: InvalidLiteralReason| {
                Error::InvalidLiteral {
                    expr,
                    lit: value.clone(),
                    ty: types.format_type(ty).to_string(),
                    reason,
                }
            };

            let info = check_integer_type(&types, expr, ty)?;

            let value_raw = if value.starts_with("0x") {
                IStorage::from_str_radix(&value[2..], 16)
            } else {
                // this handles the "max negative value" edge case for us
                IStorage::from_str(value)
            };
            let value_raw = value_raw.map_err(|e| build_error(types, e.into()))?;

            let value = match info.signed {
                Signed::Signed => BitInt::from_signed(info.bits, value_raw),
                Signed::Unsigned => BitInt::from_unsigned(info.bits, value_raw as UStorage),
            };
            let value = value.map_err(|e| build_error(types, e.into()))?;

            let ty_ir = types.map_type(ir_prog, ty);
            let value_ir = ir::Const { ty: ty_ir, value };
            LRValue::Right(TypedValue { ty, ir: value_ir.into() })
        }
        ast::ExpressionKind::StringLit { value } => {
            let ty_byte = types.define_type(TypeInfo::Int(IntTypeInfo::U8));
            let ty_byte_ptr = types.define_type_ptr(ty_byte);
            check_type_match(&types, expr, ty_byte_ptr, ty)?;

            let ty_byte_ir = types.map_type(ir_prog, ty_byte);
            let ty_byte_ptr_ir = types.map_type(ir_prog, ty_byte_ptr);

            let data = value.bytes().collect_vec();
            let data_ir = ir::DataInfo { ty: ty_byte_ptr_ir, inner_ty: ty_byte_ir, bytes: data };
            let data_ir = ir_prog.define_data(data_ir);

            LRValue::Right(TypedValue { ty, ir: data_ir.into() })
        }
        _ => return Err(Error::ExpectedLiteral(expr)),
    };

    Ok(result)
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

fn check_integer_type<'ast>(store: &TypeStore, expr: &'ast ast::Expression, actual: cst::Type) -> Result<'ast, IntTypeInfo> {
    match &store[actual] {
        &TypeInfo::Int(info) => Ok(info),
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
