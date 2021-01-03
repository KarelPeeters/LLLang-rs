use std::collections::HashMap;

use itertools::Itertools;

use crate::front;
use crate::front::{ast, cst};
use crate::front::ast::Item;
use crate::front::cst::{CollectedModule, CollectedProgram, FunctionDecl, FunctionTypeInfo, ScopedItem, ScopedValue, ScopeKind, StructTypeInfo, TypeInfo, TypeStore};
use crate::front::error::{Error, Result};

//TODO split this behemoth into multiple functions

//TODO should you be allowed to import stuff from your own module? no, right? should we explicitly disallow it?
//  what actually happens if you try currently?

/// Collect all items in the program into a format more suitable for codegen.
pub fn collect<'a>(prog: &'a front::Program<Option<ast::ModuleContent>>) -> Result<(TypeStore, CollectedProgram<'a>, cst::Function)> {
    let mut store = TypeStore::default();
    let mut collected = CollectedProgram::default();

    let mut func_map: HashMap<*const ast::Function, cst::Function> = Default::default();
    let mut struct_map: HashMap<*const ast::Struct, cst::Type> = Default::default();

    //first pass: collect all declared items into local_scope
    let mapped_prog = prog.try_map(&mut |module| {
        let mut collected_module = CollectedModule::default();

        let item_count = module.content.as_ref().map_or(0, |content| content.items.len());
        let child_count = module.submodules.len();
        println!("First pass for {} with {} items and {} children", collected.modules.len(), item_count, child_count);

        if let Some(content) = &module.content {
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
                        collected_module.codegen_funcs.push(func);
                        collected_module.local_scope.declare(&func_ast.id, ScopedItem::Value(ScopedValue::Function(func)))?;
                        func_map.insert(func_ast, func);
                    }
                    Item::Const(_) => todo!("Implement consts again"),
                    //handled in a later pass
                    Item::UseDecl(_) => {}
                }
            }
        }

        let module_id = collected.modules.push(collected_module);
        Ok((&module.content, module_id))
    })?;

    //populate the root scope with top level modules
    //this separate scope allows those modules to be overridden by locally defined items
    for (name, module) in &mapped_prog.root.submodules {
        collected.root_scope.declare_str(name, ScopedItem::Module(module.content.1))
    }

    //second pass: add child modules to parent module scope
    mapped_prog.try_for_each(&mut |module| {
        let module_id = module.content.1;
        let scope = &mut collected.modules[module_id].local_scope;

        for (name, child) in &module.submodules {
            let child_id = child.content.1;
            scope.declare_str(&*name, ScopedItem::Module(child_id));
        }

        Ok(())
    })?;

    //third pass: fill in placeholder types and construct the final, real modules scopes
    mapped_prog.try_for_each(&mut |module| {
        let (content, module_id) = module.content;
        assert_eq!(0, collected.modules[module_id].scope.size(), "scope should still be empty at this point");

        //add child modules to scope
        let scope = &mut collected.modules[module_id].scope;
        for (name, child) in &module.submodules {
            let child_id = child.content.1;
            scope.declare_str(&*name, ScopedItem::Module(child_id));
        }

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

                collected.modules[module_id].scope.declare(id, item)?;
            }

            // fill in placeholder types
            for item in &content.items {
                match item {
                    //already handled
                    Item::UseDecl(_) => {}
                    Item::Struct(struct_ast) => {
                        let fields: Vec<(&str, cst::Type)> = struct_ast.fields.iter().map(|field| {
                            let ty = collected.resolve_type(ScopeKind::Real, &collected.modules[module_id].scope, &mut store, &field.ty)?;
                            Ok((&*field.id.string, ty))
                        }).try_collect()?;

                        let info = TypeInfo::Struct(StructTypeInfo { decl: struct_ast, fields });

                        let ph = *struct_map.get(&(struct_ast as *const _)).unwrap();
                        store.replace_placeholder(ph, info)
                    }
                    Item::Function(func_ast) => {
                        let params: Vec<cst::Type> = func_ast.params.iter().map(|param| {
                            collected.resolve_type(ScopeKind::Real, &collected.modules[module_id].scope, &mut store, &param.ty)
                        }).try_collect()?;

                        let ret = func_ast.ret_ty.as_ref()
                            .map(|ret| {
                                collected.resolve_type(ScopeKind::Real, &collected.modules[module_id].scope, &mut store, ret)
                            }).transpose()?
                            .unwrap_or(store.type_void());

                        let info = FunctionTypeInfo { params, ret };

                        let func = *func_map.get(&(func_ast as *const _)).unwrap();
                        let func = &mut collected.funcs[func];

                        println!("Replacing types for {}", func.ast.id.string);

                        func.func_ty = info.clone();
                        func.ty = store.define_type(TypeInfo::Function(info));
                    }
                    Item::Const(_) => todo!("implement consts again"),
                };
            }
        }

        Ok(())
    })?;

    //find the main function
    let main_module = mapped_prog.root.submodules.get("main")
        .ok_or(Error::NoMainModule)?;

    let main_item = collected.modules[main_module.content.1].local_scope.find_immediate_str("main")
        .ok_or(Error::NoMainFunction)?;

    let main_func = if let &ScopedItem::Value(ScopedValue::Function(main_func)) = main_item {
        let actual_ty = collected.funcs[main_func].ty;
        let expected_ty = store.define_type(TypeInfo::Function(FunctionTypeInfo {
            params: vec![],
            ret: store.type_int(),
        }));

        if actual_ty != expected_ty {
            return Err(Error::MainFunctionWrongType {
                expected: store.format_type(expected_ty).to_string(),
                actual: store.format_type(actual_ty).to_string(),
            });
        }

        main_func
    } else {
        return Err(Error::MainWrongItem);
    };


    Ok((store, collected, main_func))
}
