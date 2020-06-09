use std::collections::HashMap;

use crate::front::ast;
use crate::mid::ir;

type Result<T> = std::result::Result<T, &'static str>;

struct Lower {
    variables: HashMap<String, ir::StackSlot>,
    prog: ir::Program,

    curr_func: ir::Function,
    curr_block: ir::Block,
}

impl Lower {
    fn parse_type(&mut self, ty: &ast::Type) -> Result<ir::Type> {
        match ty.string.as_ref() {
            "int" => Ok(self.prog.define_type_int(32)),
            "bool" => Ok(self.prog.define_type_int(1)),
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
                    value: lit.parse::<i32>().map_err(|_| "failed to parse int")?,
                }),
                _ => Err("unknown literal type")
            }
        } else {
            match lit {
                "true" => Ok(ir::Const { ty: self.prog.define_type_int(1), value: true as i32 }),
                "false" => Ok(ir::Const { ty: self.prog.define_type_int(1), value: false as i32 }),
                _ => Err("cannot infer type for literal"),
            }
        }
    }

    fn start_new_block(&mut self) {
        self.curr_block = self.prog.define_block(ir::BlockInfo {
            instructions: vec![],
            terminator: ir::Terminator::Unreachable,
        });
    }

    fn new_slot(&mut self, inner_ty: ir::Type) -> ir::StackSlot {
        let ty = self.prog.define_type_ptr(inner_ty);
        self.prog.define_slot(ir::StackSlotInfo { inner_ty, ty })
    }

    fn append_instr(&mut self, instr: ir::InstructionInfo) -> ir::Instruction {
        let instr = self.prog.define_instr(instr);
        self.prog.get_block_mut(self.curr_block).instructions.push(instr);
        instr
    }

    // None means this expression doesn't return control, eg. it returns from the function or breaks
    fn append_expr(&mut self, expr: &ast::Expression, expect_ty: Option<ir::Type>) -> Result<Option<ir::Value>> {
        match &expr.kind {
            ast::ExpressionKind::Literal { value } => {
                let value = self.parse_literal(&value, expect_ty)?;
                Ok(Some(ir::Value::Const(value)))
            }
            ast::ExpressionKind::Identifier { id } => {
                let slot = *self.variables.get(&id.string)
                    .ok_or("undeclared variable")?;

                //check type
                if let Some(expect_ty) = expect_ty {
                    let actual_ty = self.prog.get_slot(slot).inner_ty;
                    if expect_ty != actual_ty {
                        return Err("type mismatch")
                    }
                }

                //load
                let load = ir::InstructionInfo::Load {
                    addr: ir::Value::Slot(slot)
                };
                let load = self.append_instr(load);
                Ok(Some(ir::Value::Instr(load)))
            }
            ast::ExpressionKind::Return { value } => {
                let ret_type = self.prog.get_func(self.curr_func).ret_type;

                if let Some(value) = self.append_expr(value, Some(ret_type))? {
                    let ret = ir::Terminator::Return { value };
                    self.prog.get_block_mut(self.curr_block).terminator = ret;

                    //start new block so we can continue lowering without actually affecting anything
                    self.start_new_block();
                }

                Ok(None)
            }
        }
    }

    fn lower(mut self, root: &ast::Function) -> Result<ir::Program> {
        if &root.id.string != "main" { return Err("function should be called main"); };

        let ret_type = self.parse_type(&root.ret_type)?;
        self.prog.get_func_mut(self.prog.main).ret_type = ret_type;

        let entry_block = self.prog.get_func(self.prog.main).entry;

        for stmt in &root.body.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "mutable variables not supported");
                    //TODO we can now easily remove this limitation
                    let init = decl.init.as_ref().ok_or("variables must have initializers for now")?;
                    let ty = decl.ty.as_ref().map(|ty| self.parse_type(ty)).transpose()?;

                    let slot;
                    if let Some(value) = self.append_expr(&init, ty)? {
                        let ty = self.prog.type_of_value(value);
                        slot = self.new_slot(ty);
                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                        self.append_instr(store);
                    } else {
                        let ty = ty.ok_or("cannot infer type for declaration without value")?;
                        slot = self.new_slot(ty);
                    }

                    self.prog.get_func_mut(self.prog.main).slots.push(slot);
                    if self.variables.insert(decl.id.string.clone(), slot).is_some() {
                        return Err("variable declared twice");
                    }
                }
                ast::StatementKind::Assignment(assign) => {
                    let id = if let ast::ExpressionKind::Identifier { id } = &assign.left.kind {
                        id
                    } else {
                        return Err("target of assignment should be identifier");
                    };

                    let slot = *self.variables.get(&id.string)
                        .ok_or("use of undeclared variable")?;
                    let ty = self.prog.get_slot(slot).inner_ty;

                    if let Some(value) = self.append_expr(&assign.right, Some(ty))? {
                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                        self.append_instr(store);
                    }
                }
                ast::StatementKind::Expression(expr) => {
                    self.append_expr(expr, None)?;
                }
            }
        }

        if entry_block == self.curr_block {
            panic!("missing return")
        }

        println!("Variables: {:?}", self.variables);

        Ok(self.prog)
    }
}

pub fn lower(root: &ast::Function) -> Result<ir::Program> {
    let prog = ir::Program::new();
    let lower = Lower {
        variables: HashMap::new(),
        curr_func: prog.main,
        curr_block: prog.get_func(prog.main).entry,
        prog,
    };
    lower.lower(root)
}