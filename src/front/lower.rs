use std::collections::HashMap;
use std::panic::resume_unwind;

use itertools::Itertools;

use crate::CompileError::Lower;
use crate::front;
use crate::front::{ast, cst};
use crate::front::collect::collect;
use crate::front::cst::{FuncTypeInfo, ItemInfo, Store, StructTypeInfo, TypeInfo};
use crate::front::error::{Error, Result};
use crate::front::lower_func::LowerFuncState;
use crate::front::scope::Scope;
use crate::mid::ir;

fn resolve_type<'a>(
    store: &mut Store,
    cst: &cst::Program,
    ty: &'a ast::Type,
) -> Result<'a, cst::Type> {
    match &ty.kind {
        ast::TypeKind::Path(path) => {
            let module = path.parents.iter()
                .try_fold(&cst.root, |module, elem| {
                    module.submodules.get(&elem.string).ok_or(Error::ModuleNotFound { module: elem })
                })?;

            let item = *module.content.root_scope.find(&path.id)?;
            match store[item] {
                ItemInfo::TypeDef(ty) => Ok(ty),
                _ => Err(Error::ExpectTypeGotItem { path }),
            }
        }
        ast::TypeKind::Ref(inner) => {
            resolve_type(store, cst, &*inner)
        }
        ast::TypeKind::Func { params, ret } => {
            let params = params.iter()
                .map(|param| resolve_type(store, cst, param))
                .try_collect()?;
            let ret = resolve_type(store, cst, ret)?;

            Ok(store.define_type(TypeInfo::Func(FuncTypeInfo { params, ret })))
        }
        ast::TypeKind::Tuple { fields } => {
            let fields = fields.iter()
                .map(|field| resolve_type(store, cst, field))
                .try_collect()?;

            Ok(store.define_type(TypeInfo::Tuple(fields)))
        }
    }
}

//TODO rename
pub fn lower(prog: &front::Program<Option<ast::Module>>) -> Result<ir::Program> {
    //TODO split store fields out, they're just always empty for now
    let (mut store, cst) = collect(prog)?;
    let ty_void = store.define_type(TypeInfo::Void);

    let mut ir_prog = ir::Program::default();

    cst.try_for_each(&mut |module| {
        //create all struct types
        for struct_decl in &module.struct_decls {
            let field_tys = struct_decl.ast.fields.iter()
                .map(|field| Ok((&*field.id.string, resolve_type(&mut store, &cst, &field.ty)?)))
                .try_collect()?;

            let info = cst::TypeInfo::Struct(StructTypeInfo { decl: struct_decl, fields: field_tys });
            store.fill_placeholder_type(struct_decl.ty, info);
        }

        //create functions
        for func_decl in &module.func_decls {
            let param_tys: Vec<cst::Type> = func_decl.ast.params.iter()
                .map(|param| resolve_type(&mut store, &cst, &param.ty))
                .try_collect()?;
            let ret_ty = func_decl.ast.ret_ty.as_ref()
                .map(|ret_ty| resolve_type(&mut store, &cst, ret_ty))
                .transpose()?.unwrap_or(ty_void);

            // TODO what information about a function needs to be stored for later? the full cst function type?
            let func_type_info = FuncTypeInfo { params: param_tys, ret: ret_ty };

            let ir_func = ir_prog.define_func(ir::FunctionInfo::new(
                store.as_ir_type_func(&mut ir_prog, &func_type_info),
                &mut ir_prog,
            ));

            store.functions.insert(func_decl.item, ir_func);
        }

        //create constants
        for const_decl in &module.const_decls {
            //TODO also where to fill in constant bodies?
            todo!()
        }

        Ok(())
    })?;

    //TODO give error for cyclic types somewhere
    //   but first (for fun) try without to see where it crashes right now, prob stackoverflow in x86::size_of_type

    //TODO actually resolve use statements somewhere

    cst.try_for_each(&mut |module| {
        let mut module_scope = Scope::default();

        todo!("populate scope");

        for func_decl in &module.func_decls {
            let ir_func = *store.functions.get(&func_decl.item).unwrap();

            let mut lower = LowerFuncState {
                prog: &mut ir_prog,
                cst: &cst,
                module_scope: &module_scope,
                curr_func: ir_func,
                loop_stack: vec![],
            };
            lower.append_func(func_decl.ast, ir_func)?;
        }

        Ok(())
    })?;

    Ok(ir_prog)
}