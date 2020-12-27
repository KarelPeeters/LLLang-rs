use crate::front;
use crate::front::cst::{Store, ModuleContent, ScopedItem};
use crate::front::{ast, cst};
use crate::front::error::Result;
use crate::util::arena::ArenaSet;
use crate::front::ast::Item;

struct CollectedProgram<'a> {
    store: Store<'a>,
    struct_decls: Vec<StructDeclInfo<'a>>,
    cst: cst::Program<'a>,
}

struct StructDeclInfo<'a> {
    ty: cst::Type,
    ast: &'a ast::Struct,
}

///Collect all items in the program into a format more suitable for following steps.
pub fn collect<'a>(prog: &front::Program<Option<ast::Module>>) -> Result<CollectedProgram> {
    let mut store = Store::default();
    let mut struct_decls = Vec::default();

    let mut map_module = |module: &'a ast::Module| -> Result<ModuleContent> {
        let mut content = ModuleContent::default();

        for item in &module.items {
            match item {
                Item::UseDecl(d) => content.use_decls.push(d),
                Item::Struct(s) => {
                    let ty = store.new_placeholder_type();
                    struct_decls.push(StructDeclInfo { ty, ast: s });
                }
                Item::Function(func) => {
                    content.func_decls.push(FuncDeclInfo { ast: func, item })
                }
                Item::Const(cst) => {
                    let item = store.new_item(ItemInfo::ConstDef());
                    content.scope_defines.declare(&cst.id, item)?;
                    content.const_decls.push(ConstDeclInfo { ast: cst, item })
                }
            }
        }

        Ok(content)
    };

    let prog = prog.try_map(&mut |module| {
        match module {
            None => Ok(ModuleContent::default()),
            Some(module) => map_module(module),
        }
    })?;

    Ok((store, prog))
}