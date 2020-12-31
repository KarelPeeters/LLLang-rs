use std::collections::HashMap;

use itertools::Itertools;

use crate::front;
use crate::front::{ast, cst};
use crate::front::ast::Item;
use crate::front::cst::{CollectedModule, CollectedProgram, FunctionDecl, FunctionTypeInfo, ScopedItem, ScopedValue, ScopeKind, StructTypeInfo, TypeInfo, TypeStore};
use crate::front::error::Result;

//TODO split this behemoth into multiple functions

/// Collect all items in the program into a format more suitable for codegen.
pub fn collect<'a>(prog: &'a front::Program<Option<ast::ModuleContent>>) -> Result<(TypeStore, CollectedProgram<'a>)> {
    let mut store = TypeStore::default();
    let mut collected = CollectedProgram::default();

    let mut func_map: HashMap<*const ast::Function, cst::Function> = Default::default();
    let mut struct_map: HashMap<*const ast::Struct, cst::Type> = Default::default();

    //first pass: collect all declared items into local_scope
    let mapped_prog = prog.try_map(&mut |content| {
        let mut collected_module = CollectedModule::default();

        if let Some(content) = content {
            for item in &content.items {
                match item {
                    Item::Struct(struct_ast) => {
                        let ph = store.new_placeholder();
                        collected_module.local_scope.declare(&struct_ast.id, ScopedItem::Type(ph))?;
                        struct_map.insert(struct_ast, ph);
                    }
                    Item::Function(func_ast) => {
                        let ph = store.new_placeholder();

                        //construct a decl with placeholder types, will be filled in during the second pass
                        let decl = FunctionDecl {
                            ty: ph,
                            func_ty: FunctionTypeInfo { params: vec![], ret: ph },
                            ast: func_ast,
                        };

                        let func = collected.funcs.push(decl);
                        collected_module.local_scope.declare(&func_ast.id, ScopedItem::Value(ScopedValue::Function(func)))?;
                        func_map.insert(func_ast, func);
                    }
                    Item::Const(_) => todo!("implement consts again"),
                    //handled in a later pass
                    Item::UseDecl(_) => {}
                }
            }
        }

        Ok((content, collected.modules.push(collected_module)))
    })?;

    //populate the root scope with op level modules
    //this separate scope allows those modules to be overridden by locally defined items
    for (name, module) in &mapped_prog.root.submodules {
        collected.root_scope.declare_str(name, ScopedItem::Module(module.content.1))
    }

    //second pass: fill in placeholder types and construct the real modules scopes
    mapped_prog.try_for_each(&mut |&(content, module)| {
        assert_eq!(0, collected.modules[module].scope.size(), "scope should still be empty at this point");

        //TODO should you be allowed to import stuff from your own module? no, right? should we explicitly disallow it?
        //  what actually happens if you try currently?

        if let Some(content) = content {
            //add items to local scope, in order of appearance for nicer error messages
            for item in &content.items {
                let (id, item) = match item {
                    Item::UseDecl(use_ast) => {
                        let item = collected.resolve_path(ScopeKind::Local, &collected.root_scope, &mut store, &use_ast.path)?;
                        (&use_ast.path.id, item)
                    }
                    Item::Struct(struct_ast) => {
                        let item = ScopedItem::Type(*struct_map.get(&(struct_ast as *const _)).unwrap());
                        (&struct_ast.id, item)
                    }
                    Item::Function(func_ast) => {
                        let func = *func_map.get(&(func_ast as *const _)).unwrap();
                        let item = ScopedItem::Value(ScopedValue::Function(func));
                        (&func_ast.id, item)
                    }
                    Item::Const(_) => todo!("implement consts again"),
                };

                collected.modules[module].scope.declare(id, item)?;
            }

            // fill in placeholder types
            for item in &content.items {
                match item {
                    //already handled
                    Item::UseDecl(_) => {}
                    Item::Struct(struct_ast) => {
                        let fields: Vec<(&str, cst::Type)> = struct_ast.fields.iter().map(|field| {
                            let ty = collected.resolve_type(ScopeKind::Real, &collected.modules[module].scope, &mut store, &field.ty)?;
                            Ok((&*field.id.string, ty))
                        }).try_collect()?;

                        let info = TypeInfo::Struct(StructTypeInfo { decl: struct_ast, fields });

                        let ph = *struct_map.get(&(struct_ast as *const _)).unwrap();
                        store.replace_placeholder(ph, info)
                    }
                    Item::Function(func_ast) => {
                        let params: Vec<cst::Type> = func_ast.params.iter().map(|param| {
                            collected.resolve_type(ScopeKind::Real, &collected.modules[module].scope, &mut store, &param.ty)
                        }).try_collect()?;

                        let ret = func_ast.ret_ty.as_ref()
                            .map(|ret| {
                                collected.resolve_type(ScopeKind::Real, &collected.modules[module].scope, &mut store, ret)
                            }).transpose()?
                            .unwrap_or(store.type_void());

                        let info = FunctionTypeInfo { params, ret };

                        let func = *func_map.get(&(func_ast as *const _)).unwrap();
                        let func = &mut collected.funcs[func];

                        func.func_ty = info.clone();
                        func.ty = store.define_type(TypeInfo::Function(info));
                    }
                    Item::Const(_) => todo!("implement consts again"),
                };
            }
        }

        Ok(())
    })?;

    Ok((store, collected))
}
