use std::collections::HashMap;

use itertools::Itertools;

use crate::front;
use crate::front::{ast, cst};
use crate::front::ast::{Item, ModuleContent};
use crate::front::cst::{CollectedModule, ConstDecl, FunctionDecl, FunctionTypeInfo, ItemStore, ResolvedProgram, ScopedItem, ScopedValue, ScopeKind, StructTypeInfo, TypeInfo, TypeStore};
use crate::front::error::{Error, Result};

type AstProgram = front::Program<Option<ast::ModuleContent>>;
type CstProgram<'a> = front::Program<(&'a Option<ModuleContent>, cst::Module)>;

/// Resolve all items in the program into a format more suitable for codegen.
pub fn resolve(ast: &front::Program<Option<ast::ModuleContent>>) -> Result<ResolvedProgram> {
    let (mut state, mapped) = first_pass(ast)?;

    second_pass(&mut state, &mapped)?;
    third_pass(&mut state, &mapped)?;

    let main_func = find_main_function(&mut state, &mapped)?;

    Ok(ResolvedProgram {
        types: state.types,
        items: state.items,
        main_func,
    })
}

#[derive(Debug)]
struct ResolveState<'a> {
    types: TypeStore<'a>,
    items: ItemStore<'a>,

    func_map: HashMap<*const ast::Function, cst::Function>,
    const_map: HashMap<*const ast::Const, cst::Const>,
    struct_map: HashMap<*const ast::Struct, cst::Type>,
}

//TODO proper doc comments

//first pass: collect all declared items into local_scope
fn first_pass<'a>(ast: &'a AstProgram) -> Result<(ResolveState<'a>, CstProgram<'a>)> {
    let mut store = TypeStore::default();
    let common_ph_type = store.new_placeholder();

    let mut cst = ItemStore::default();

    let mut func_map: HashMap<*const ast::Function, cst::Function> = Default::default();
    let mut cst_map: HashMap<*const ast::Const, cst::Const> = Default::default();
    let mut struct_map: HashMap<*const ast::Struct, cst::Type> = Default::default();

    let mapped = ast.try_map(&mut |module| {
        let mut collected_module = CollectedModule::default();

        let item_count = module.content.as_ref().map_or(0, |content| content.items.len());
        let child_count = module.submodules.len();
        println!("First pass for {} with {} items and {} children", cst.modules.len(), item_count, child_count);

        if let Some(content) = &module.content {
            for item in &content.items {
                match item {
                    Item::Struct(struct_ast) => {
                        let ph = store.new_placeholder();
                        collected_module.local_scope.declare(&struct_ast.id, ScopedItem::Type(ph))?;
                        struct_map.insert(struct_ast, ph);
                    }
                    Item::Function(func_ast) => {
                        //construct a decl with placeholder types, will be filled in during the second pass
                        let decl = FunctionDecl {
                            ty: common_ph_type,
                            func_ty: FunctionTypeInfo { params: vec![], ret: common_ph_type },
                            ast: func_ast,
                        };

                        let func = cst.funcs.push(decl);
                        collected_module.codegen_funcs.push(func);
                        collected_module.local_scope.declare(&func_ast.id, ScopedItem::Value(ScopedValue::Function(func)))?;
                        func_map.insert(func_ast, func);
                    }
                    Item::Const(cst_ast) => {
                        let decl = ConstDecl {
                            ty: common_ph_type,
                            ast: cst_ast,
                        };

                        let cst = cst.consts.push(decl);
                        collected_module.local_scope.declare(&cst_ast.id, ScopedItem::Value(ScopedValue::Const(cst)))?;
                        cst_map.insert(cst_ast, cst);
                    }
                    //handled in a later pass
                    Item::UseDecl(_) => {}
                }
            }
        }

        let module_id = cst.modules.push(collected_module);
        Ok((&module.content, module_id))
    })?;

    let state = ResolveState {
        types: store,
        items: cst,
        func_map,
        const_map: cst_map,
        struct_map,
    };
    Ok((state, mapped))
}

//second pass: add child modules to parent module scope
//populate the root scope with top level modules
//this separate scope allows those modules to be overridden by locally defined items
fn second_pass<'a>(state: &mut ResolveState<'a>, mapped: &CstProgram<'a>) -> Result<'a, ()> {
    for (name, module) in &mapped.root.submodules {
        state.items.root_scope.declare_str(name, ScopedItem::Module(module.content.1))
    }

    mapped.try_for_each(&mut |module| {
        let module_id = module.content.1;
        let scope = &mut state.items.modules[module_id].local_scope;

        for (name, child) in &module.submodules {
            let child_id = child.content.1;
            scope.declare_str(&*name, ScopedItem::Module(child_id));
        }

        Ok(())
    })
}

//third pass: by this point all items will have been put into the local_scope of their module
//now we replace placeholder types with the proper types and construct the final modules scopes
fn third_pass<'a>(state: &mut ResolveState<'a>, mapped: &CstProgram<'a>) -> Result<'a, ()> {
    mapped.try_for_each(&mut |module| {
        let (content, module_id) = module.content;
        assert_eq!(0, state.items.modules[module_id].scope.size(), "scope should still be empty at this point");

        //add child modules to scope
        let scope = &mut state.items.modules[module_id].scope;
        for (name, child) in &module.submodules {
            let child_id = child.content.1;
            scope.declare_str(&*name, ScopedItem::Module(child_id));
        }

        let items = &mut state.items;
        let types = &mut state.types;

        if let Some(content) = content {
            //add items to scope, in order of appearance for nicer error messages
            for item in &content.items {
                let (id, item) = match item {
                    Item::UseDecl(use_ast) => {
                        let item = items.resolve_path(ScopeKind::Local, &items.root_scope, &use_ast.path)?;
                        (&use_ast.path.id, item)
                    }
                    Item::Struct(struct_ast) => {
                        let item = ScopedItem::Type(*state.struct_map.get(&(struct_ast as *const _)).unwrap());
                        (&struct_ast.id, item)
                    }
                    Item::Function(func_ast) => {
                        let func = *state.func_map.get(&(func_ast as *const _)).unwrap();
                        let item = ScopedItem::Value(ScopedValue::Function(func));
                        (&func_ast.id, item)
                    }
                    Item::Const(cst_ast) => {
                        let cst = *state.const_map.get(&(cst_ast as *const _)).unwrap();
                        let item = ScopedItem::Value(ScopedValue::Const(cst));
                        (&cst_ast.id, item)
                    }
                };

                items.modules[module_id].scope.declare(id, item)?;
            }

            let module_scope = &items.modules[module_id].scope;

            // fill in placeholder types
            for item in &content.items {
                match item {
                    //already handled
                    Item::UseDecl(_) => {}
                    Item::Struct(struct_ast) => {
                        let fields: Vec<(&str, cst::Type)> = struct_ast.fields.iter().map(|field| {
                            let ty = items.resolve_type(ScopeKind::Real, module_scope, types, &field.ty)?;
                            Ok((&*field.id.string, ty))
                        }).try_collect()?;

                        let info = TypeInfo::Struct(StructTypeInfo { decl: struct_ast, fields });

                        let ph = *state.struct_map.get(&(struct_ast as *const _)).unwrap();
                        types.replace_placeholder(ph, info)
                    }
                    Item::Function(func_ast) => {
                        let params: Vec<cst::Type> = func_ast.params.iter().map(|param| {
                            items.resolve_type(ScopeKind::Real, module_scope, types, &param.ty)
                        }).try_collect()?;

                        let ret = func_ast.ret_ty.as_ref()
                            .map(|ret| {
                                items.resolve_type(ScopeKind::Real, module_scope, types, ret)
                            }).transpose()?
                            .unwrap_or(types.type_void());

                        let info = FunctionTypeInfo { params, ret };

                        let func = *state.func_map.get(&(func_ast as *const _)).unwrap();
                        let func = &mut items.funcs[func];

                        func.func_ty = info.clone();
                        func.ty = types.define_type(TypeInfo::Function(info));
                    }
                    Item::Const(cst_ast) => {
                        let ty = items.resolve_type(ScopeKind::Real, module_scope, types, &cst_ast.ty)?;

                        let cst = *state.const_map.get(&(cst_ast as *const _)).unwrap();
                        items.consts[cst].ty = ty;
                    }
                };
            }
        }

        Ok(())
    })
}

fn find_main_function<'a>(state: &mut ResolveState<'a>, mapped: &CstProgram<'a>) -> Result<'a, cst::Function> {
    //find the main function
    let main_module = mapped.root.submodules.get("main")
        .ok_or(Error::NoMainModule)?;

    let main_item = state.items.modules[main_module.content.1].local_scope.find_immediate_str("main")
        .ok_or(Error::NoMainFunction)?;

    if let &ScopedItem::Value(ScopedValue::Function(main_func)) = main_item {
        let actual_ty = state.items.funcs[main_func].ty;
        let expected_ty = state.types.define_type(TypeInfo::Function(FunctionTypeInfo {
            params: vec![],
            ret: state.types.type_int(),
        }));

        if actual_ty != expected_ty {
            return Err(Error::MainFunctionWrongType {
                expected: state.types.format_type(expected_ty).to_string(),
                actual: state.types.format_type(actual_ty).to_string(),
            });
        }

        Ok(main_func)
    } else {
        Err(Error::MainWrongItem)
    }
}
