use crate::front::ast;
use crate::mid::ir;

type Result<T> = std::result::Result<T, &'static str>;

pub fn resolve(root: &ast::Function) -> Result<ir::Function> {
    //TODO
    // typecheck, figure our symbols, collect declared types, ...
    // then convert to ir

    if &root.name != "main" { return Err("function should be called main"); };
    if root.body.statements.len() != 1 { return Err("body can only have one statement"); };

    let value = match root.body.statements[0] {
        ast::Statement::Return { value } => value
    };

    Ok(ir::Function {
        entry: ir::BasicBlock {
            terminator: ir::Terminator::Return { value }
        }
    })
}