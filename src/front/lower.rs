use std::collections::HashMap;

use crate::front::ast;
use crate::front::ast::TypeKind;
use crate::mid::ir;

type Result<T> = std::result::Result<T, &'static str>;

struct Lower {
    variables: HashMap<String, ir::StackSlot>,
    prog: ir::Program,

    curr_func: ir::Function,
    curr_block: ir::Block,
}

#[derive(Debug, Copy, Clone)]
enum LRValue {
    Left(ir::Value),
    Right(ir::Value),
}

impl Lower {
    fn parse_type(&mut self, ty: &ast::Type) -> Result<ir::Type> {
        match &ty.kind {
            TypeKind::Simple(string) => match string.as_ref() {
                "int" => Ok(self.prog.define_type_int(32)),
                "bool" => Ok(self.prog.define_type_int(1)),
                _ => Err("invalid return type"),
            },
            TypeKind::Ref(inner) => {
                let inner = self.parse_type(inner)?;
                Ok(self.prog.define_type_ptr(inner))
            },
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

    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type {
        match value {
            LRValue::Left(value) => {
                let ty = self.prog.type_of_value(value);
                self.prog.get_type(ty).as_ptr().expect("lvalue should have pointer type")
            },
            LRValue::Right(value) => {
                self.prog.type_of_value(value)
            },
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

    fn append_load(&mut self, value: LRValue) -> ir::Value {
        match value {
            LRValue::Left(value) =>
                ir::Value::Instr(self.append_instr(ir::InstructionInfo::Load { addr: value })),
            LRValue::Right(value) =>
                value,
        }
    }

    fn append_store(&mut self, addr: LRValue, value: ir::Value) -> Result<ir::Value> {
        match addr {
            LRValue::Left(addr) =>
                Ok(ir::Value::Instr(self.append_instr(ir::InstructionInfo::Store { addr, value }))),
            LRValue::Right(_) =>
                Err("attempt to store into rvalue"),
        }
    }

    /// None means this expression doesn't return control, eg. it returns from the function or breaks
    fn append_expr(&mut self, expr: &ast::Expression, expect_ty: Option<ir::Type>) -> Result<Option<LRValue>> {
        match &expr.kind {
            ast::ExpressionKind::Literal { value } => {
                let value = self.parse_literal(&value, expect_ty)?;
                Ok(Some(LRValue::Right(ir::Value::Const(value))))
            }
            ast::ExpressionKind::Identifier { id } => {
                let slot = *self.variables.get(&id.string)
                    .ok_or("use of undeclared variable")?;

                //check type
                if let Some(expect_ty) = expect_ty {
                    let actual_ty = self.prog.get_slot(slot).inner_ty;
                    if expect_ty != actual_ty {
                        return Err("type mismatch")
                    }
                }

                Ok(Some(LRValue::Left(ir::Value::Slot(slot))))
            }
            ast::ExpressionKind::Ref { inner } => {
                let expect_ty_inner = expect_ty.map(|ty| self.prog.get_type(ty).as_ptr()
                    .ok_or("expected non-pointer type, got reference"))
                    .transpose()?;

                let inner = self.append_expr(inner, expect_ty_inner)?;
                if let Some(inner) = inner {
                    match inner {
                        //ref turns an lvalue into an rvalue
                        LRValue::Left(inner) => Ok(Some(LRValue::Right(inner))),
                        LRValue::Right(_) => Err("attempt to take reference of lvalue"),
                    }
                } else {
                    Ok(None)
                }
            }
            ast::ExpressionKind::DeRef { inner } => {
                let expect_ty_inner = expect_ty.map(|ty| self.prog.define_type_ptr(ty));

                //load to get the value and wrap as lvalue again
                self.append_expr_loaded(inner, expect_ty_inner)
                    .map(|v| v.map(LRValue::Left))
            }
            ast::ExpressionKind::Return { value } => {
                let ret_type = self.prog.get_func(self.curr_func).ret_type;

                if let Some(value) = self.append_expr_loaded(value, Some(ret_type))? {
                    let ret = ir::Terminator::Return { value };
                    self.prog.get_block_mut(self.curr_block).terminator = ret;

                    //start new block so we can continue lowering without actually affecting anything
                    self.start_new_block();
                }

                Ok(None)
            }
        }
    }

    fn append_expr_loaded(&mut self, expr: &ast::Expression, expect_ty: Option<ir::Type>) -> Result<Option<ir::Value>> {
        let value = self.append_expr(expr, expect_ty)?;
        Ok(value.map(|value| self.append_load(value)))
    }

    fn lower(mut self, root: &ast::Function) -> Result<ir::Program> {
        if &root.id.string != "main" { return Err("function should be called main"); };

        let ret_type = self.parse_type(&root.ret_type)?;
        self.prog.get_func_mut(self.prog.main).ret_type = ret_type;

        let entry_block = self.prog.get_func(self.prog.main).entry;

        for stmt in &root.body.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "everything is mutable for now");
                    let expect_ty = decl.ty.as_ref().map(|ty| self.parse_type(ty)).transpose()?;

                    let value = decl.init.as_ref()
                        .map(|init| self.append_expr_loaded(init, expect_ty))
                        .transpose()?.flatten();

                    //figure out the type
                    let value_ty = value.map(|v| self.prog.type_of_value(v));
                    let ty = expect_ty.or(value_ty).ok_or("cannot infer type for variable")?;

                    //define the slot
                    let slot = self.new_slot(ty);
                    self.prog.get_func_mut(self.prog.main).slots.push(slot);
                    if self.variables.insert(decl.id.string.clone(), slot).is_some() {
                        return Err("variable declared twice");
                    }

                    //optionally store the value
                    if let Some(value) = value {
                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                        self.append_instr(store);
                    }
                }
                ast::StatementKind::Assignment(assign) => {
                    let addr = self.append_expr(&assign.left, None)?
                        .expect("left side of assignment can't be a 'never' value");
                    let ty = self.type_of_lrvalue(addr);

                    if let Some(value) = self.append_expr_loaded(&assign.right, Some(ty))? {
                        self.append_store(addr, value)?;
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