use std::collections::HashMap;

use crate::front::ast;
use crate::front::ast::TypeKind;
use crate::mid::ir;

type Result<T> = std::result::Result<T, &'static str>;

struct Lower {
    prog: ir::Program,

    //TODO replace this global state with parameters
    curr_func: ir::Function,
    curr_func_vars: HashMap<String, ir::StackSlot>,
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
                "bool" => Ok(self.prog.type_bool()),
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
                "true" => Ok(ir::Const { ty: self.prog.type_bool(), value: true as i32 }),
                "false" => Ok(ir::Const { ty: self.prog.type_bool(), value: false as i32 }),
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
    fn append_expr(&mut self, expr: &ast::Expression, expect_ty: Option<ir::Type>) -> Result<LRValue> {
        match &expr.kind {
            ast::ExpressionKind::Literal { value } => {
                let value = self.parse_literal(&value, expect_ty)?;
                Ok(LRValue::Right(ir::Value::Const(value)))
            }
            ast::ExpressionKind::Identifier { id } => {
                let slot = *self.curr_func_vars.get(&id.string)
                    .ok_or("use of undeclared variable")?;

                //check type
                if let Some(expect_ty) = expect_ty {
                    let actual_ty = self.prog.get_slot(slot).inner_ty;
                    if expect_ty != actual_ty {
                        return Err("type mismatch")
                    }
                }

                Ok(LRValue::Left(ir::Value::Slot(slot)))
            }
            ast::ExpressionKind::Ref { inner } => {
                let expect_ty_inner = expect_ty.map(|ty| self.prog.get_type(ty).as_ptr()
                    .ok_or("expected non-pointer type, got reference"))
                    .transpose()?;

                let inner = self.append_expr(inner, expect_ty_inner)?;
                match inner {
                    //ref turns an lvalue into an rvalue
                    LRValue::Left(inner) => Ok(LRValue::Right(inner)),
                    LRValue::Right(_) => Err("attempt to take reference of lvalue"),
                }
            }
            ast::ExpressionKind::DeRef { inner } => {
                let expect_ty_inner = expect_ty.map(|ty| self.prog.define_type_ptr(ty));

                //load to get the value and wrap as lvalue again
                self.append_expr_loaded(inner, expect_ty_inner)
                    .map(LRValue::Left)
            }
            ast::ExpressionKind::Return { value } => {
                let ret_type = self.prog.get_func(self.curr_func).ret_type;
                let value = self.append_expr_loaded(value, Some(ret_type))?;

                let ret = ir::Terminator::Return { value };
                self.prog.get_block_mut(self.curr_block).terminator = ret;

                //start block and return undef so we can continue as if nothing happened
                self.start_new_block();
                let ty = expect_ty.ok_or("cannot infer type for !")?;
                Ok(LRValue::Left(ir::Value::Undef(self.prog.define_type_ptr(ty))))
            }
        }
    }

    fn append_expr_loaded(&mut self, expr: &ast::Expression, expect_ty: Option<ir::Type>) -> Result<ir::Value> {
        let value = self.append_expr(expr, expect_ty)?;
        Ok(self.append_load(value))
    }

    fn lower(mut self, main: &ast::Function) -> Result<ir::Program> {
        if &main.id.string != "main" { return Err("function should be called main") };

        let ret_type = self.parse_type(&main.ret_type)?;
        self.prog.get_func_mut(self.prog.main).ret_type = ret_type;

        let entry_block = self.curr_block;
        self.append_block(&main.body)?;
        if entry_block == self.curr_block {
            //TODO this return check has lots of false negatives
            return Err("missing return")
        }

        Ok(self.prog)
    }

    fn append_block(&mut self, block: &ast::Block) -> Result<()> {
        for stmt in &block.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "everything is mutable for now");
                    let expect_ty = decl.ty.as_ref().map(|ty| self.parse_type(ty)).transpose()?;

                    let value = decl.init.as_ref()
                        .map(|init| self.append_expr_loaded(init, expect_ty))
                        .transpose()?;

                    //figure out the type
                    let value_ty = value.map(|v| self.prog.type_of_value(v));
                    let ty = expect_ty.or(value_ty).ok_or("cannot infer type for variable")?;

                    //define the slot
                    let slot = self.new_slot(ty);
                    self.prog.get_func_mut(self.curr_func).slots.push(slot);
                    if self.curr_func_vars.insert(decl.id.string.clone(), slot).is_some() {
                        return Err("variable declared twice")
                    }

                    //optionally store the value
                    if let Some(value) = value {
                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                        self.append_instr(store);
                    }
                }
                ast::StatementKind::Assignment(assign) => {
                    let addr = self.append_expr(&assign.left, None)?;
                    let ty = self.type_of_lrvalue(addr);

                    let value = self.append_expr_loaded(&assign.right, Some(ty))?;
                    self.append_store(addr, value)?;
                }
                ast::StatementKind::If(if_stmt) => {
                    //condition
                    let cond = self.append_expr_loaded(&if_stmt.cond, Some(self.prog.type_bool()))?;
                    let cond_end_block = self.curr_block;

                    //then
                    self.start_new_block();
                    let then_start_block = self.curr_block;
                    self.append_block(&if_stmt.then_block)?;
                    let then_end_block = self.curr_block;

                    //else
                    self.start_new_block();
                    let else_start_block = self.curr_block;
                    if let Some(else_block) = &if_stmt.else_block {
                        self.append_block(else_block)?;
                    }
                    let else_end_block = self.curr_block;

                    //end
                    self.start_new_block();
                    let end_block = self.curr_block;

                    //connect everything
                    let branch = ir::Terminator::Branch { cond, targets: [then_start_block, else_start_block] };
                    let jump_end = ir::Terminator::Jump { target: end_block };

                    self.prog.get_block_mut(cond_end_block).terminator = branch;
                    self.prog.get_block_mut(then_end_block).terminator = jump_end;
                    self.prog.get_block_mut(else_end_block).terminator = jump_end;
                }
                ast::StatementKind::Expression(expr) => {
                    self.append_expr(expr, Some(self.prog.type_void()))?;
                }
            }
        }

        Ok(())
    }
}

pub fn lower(root: &ast::Function) -> Result<ir::Program> {
    let prog = ir::Program::new();
    let lower = Lower {
        curr_func_vars: HashMap::new(),
        curr_func: prog.main,
        curr_block: prog.get_func(prog.main).entry,
        prog,
    };
    lower.lower(root)
}