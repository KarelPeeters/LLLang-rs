use std::collections::HashMap;

use crate::front::ast;
use crate::mid::ir;

type Result<T> = std::result::Result<T, &'static str>;

struct Lower {
    variables: HashMap<String, ir::Const>,
    prog: ir::Program,
}

impl Lower {
    fn parse_type(&mut self, ty: &ast::Type) -> Result<ir::Type> {
        match ty.string.as_ref() {
            "int" => Ok(self.prog.get_type_int(32)),
            "bool" => Ok(self.prog.get_type_int(1)),
            _ => Err("invalid return type"),
        }
    }

    fn parse_literal(&mut self, lit: &str, ty: Option<ir::Type>) -> Result<ir::Const> {
        if let Some(ty) = ty {
            match self.prog.get_type(ty) {
                ir::TypeInfo::Integer { bits: 1 } => Ok(ir::Const {
                    ty,
                    value: lit.parse::<bool>().map_err(|_| "failed to parse bool")? as i32,
                }),
                ir::TypeInfo::Integer { bits: 32 } => Ok(ir::Const {
                    ty,
                    value: lit.parse::<bool>().map_err(|_| "failed to parse bool")? as i32,
                }),
                _ => Err("unknown literal type")
            }
        } else {
            match lit {
                "true" => Ok(ir::Const { ty: self.prog.get_type_int(1), value: true as i32 }),
                "false" => Ok(ir::Const { ty: self.prog.get_type_int(1), value: false as i32 }),
                _ => Err("cannot infer type for literal"),
            }
        }
    }

    // (x, true) -> the function should return x
    // (x, false) -> the result of this expression is x
    fn eval(&mut self, value: &ast::Expression, expect_ty: Option<ir::Type>, ret_type: ir::Type) -> Result<(ir::Const, bool)> {
        match &value.kind {
            ast::ExpressionKind::Literal { value } => {
                self.parse_literal(&value, expect_ty)
                    .map(|v| (v, false))
            }
            ast::ExpressionKind::Identifier { id } => {
                self.variables.get(&id.string)
                    .ok_or("undeclared variable")
                    .and_then(|&v| {
                        if expect_ty.map(|et| et == v.ty).unwrap_or(true) {
                            Ok((v, false))
                        } else {
                            Err("type mismatch")
                        }
                    })
            }
            ast::ExpressionKind::Return { value } => {
                self.eval(value, Some(ret_type),ret_type)
                    .map(|(v, _)| (v, true))
            }
        }
    }

    fn lower(mut self, root: &ast::Function) -> Result<ir::Program> {
        if &root.id.string != "main" { return Err("function should be called main"); };

        let ret_type = self.parse_type(&root.ret_type)?;
        self.prog.get_func_mut(self.prog.entry).ret_type = ret_type;

        let mut return_value: Option<ir::Const> = None;

        for stmt in &root.body.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "mutable variables not supported");
                    let init = decl.init.as_ref().ok_or("variables must have initializers for now")?;
                    let ty = decl.ty.as_ref().map(|ty| self.parse_type(ty)).transpose()?;

                    let (value, should_ret) = self.eval(&init, ty, ret_type)?;
                    if should_ret && return_value.is_none() {
                        return_value = Some(value);
                    };

                    //the value stored if should_ret doesn't matter but it still needs to exist to allow
                    //the (dead) code after the return to compile
                    let value = if should_ret {
                        if let Some(ty) = ty {
                            ir::Const { ty, value: -1 }
                        } else {
                            return Err("cannot infer type for variable");
                        }
                    } else {
                        value
                    };

                    if self.variables.insert(decl.id.string.clone(), value).is_some() {
                        return Err("variable declared twice");
                    }
                }
                ast::StatementKind::Expression(expr) => {
                    let (value, should_ret) = self.eval(expr, None, ret_type)?;
                    if should_ret && return_value.is_none() {
                        return_value = Some(value)
                    }
                }
            }
        }

        match return_value {
            None => return Err("missing return statement"),
            Some(cst) => {
                let value = ir::Value::Const(ir::Const { ty: cst.ty, value: cst.value });
                let ret = self.prog.define_term(ir::TerminatorInfo::Return { value });
                self.prog.get_block_mut(self.prog.get_func(self.prog.entry).entry).terminator = ret;
            }
        }

        println!("Variables: {:?}", self.variables);

        Ok(self.prog)
    }
}

pub fn lower(root: &ast::Function) -> Result<ir::Program> {
    let lower = Lower {
        variables: HashMap::new(),
        prog: ir::Program::new(),
    };
    lower.lower(root)
}