use crate::front::ast;
use crate::front::ast::{ExpressionKind, StatementKind};
use crate::mid::ir;
use crate::mid::ir::{TerminatorInfo, Type};

type Result<T> = std::result::Result<T, &'static str>;

//Find the final return value in a bunch of nested return expressions
fn find_ret_value(expr: &ast::Expression) -> Result<&String> {
    match &expr.kind {
        ExpressionKind::Literal { value } => Ok(value),
        ExpressionKind::Return { value } => find_ret_value(value),
    }
}

pub fn lower(root: &ast::Function) -> Result<ir::Program> {
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

    let mut ir_program = ir::Program::new();

    let ret_value = match &root.body.statements[0].kind {
        StatementKind::Declaration(_) => todo!(),
        StatementKind::Expression(expr) => {
            match &expr.kind {
                ExpressionKind::Literal { .. } => return Err("expected a return statement, got a literal"),
                ExpressionKind::Return { value } => find_ret_value(expr)?,
            }
        }
    };

    let ret_value = match ret_type {
        Type::Bool =>
            ret_value.parse::<bool>().map_err(|_| "failed to parse bool")? as i32,
        Type::Int =>
            ret_value.parse::<i32>().map_err(|_| "failed to parse int")?,
    };

    let ret = ir_program.define_terminator(TerminatorInfo::Return { value: ret_value });

    ir_program.func_mut(ir_program.entry).ret_type = ret_type;
    ir_program.block_mut(ir_program.func(ir_program.entry).entry).terminator = ret;

    Ok(ir_program)
}