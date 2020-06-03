use crate::front::ast;
use crate::mid::ir;
use crate::mid::ir::Type;

type Result<T> = std::result::Result<T, &'static str>;

pub fn resolve(root: &ast::Function) -> Result<ir::Function> {
    //TODO
    // typecheck, figure our symbols, collect declared types, ...
    // then convert to ir

    if &root.name != "main" { return Err("function should be called main"); };
    if root.body.statements.len() != 1 { return Err("body can only have one statement"); };

    let ret_type = match root.ret_type.string.as_ref() {
        "int" => ir::Type::Int,
        "bool" => ir::Type::Bool,
        _ => return Err("invalid return type"),
    };

    //TODO parse literals here
    // technically we can only fully parse them after type inference but that doesn't exist yet
    let value = match &root.body.statements[0] {
        ast::Statement::Return { value } => value
    };

    let value = match ret_type {
        Type::Bool => {
            value.parse::<bool>().expect("Failed to parse bool") as i32
        },
        Type::Int => {
            value.parse::<i32>().expect("Failed to parse int")
        },
    };

    Ok(ir::Function {
        ret_type,
        entry: ir::BasicBlock {
            terminator: ir::Terminator::Return { value }
        }
    })
}