use std::marker::PhantomData;

use indexmap::map::IndexMap;

use crate::front::{ast, Span};
use crate::mid::ir;

type Result<'a, T> = std::result::Result<T, Error<'a>>;

struct Lower<'a> {
    prog: ir::Program,
    functions: IndexMap<&'a str, ir::Function>,

    //TODO replace this global state with parameters
    curr_func: ir::Function,
    curr_block: ir::Block,

    ph: PhantomData<&'a ()>,
}

#[derive(Default)]
struct Scope<'p> {
    parent: Option<&'p Scope<'p>>,
    variables: IndexMap<String, LRValue>,
}

impl Scope<'_> {
    fn nest(&self) -> Scope {
        Scope { parent: Some(self), variables: Default::default() }
    }

    fn declare_variable<'a>(&mut self, id: &'a ast::Identifier, var: LRValue) -> Result<'a, ()> {
        if self.variables.insert(id.string.to_owned(), var).is_some() {
            Err(Error::IdentifierDeclaredTwice(id))
        } else { Ok(()) }
    }

    fn find_variable<'a>(&self, id: &'a ast::Identifier) -> Result<'a, LRValue> {
        if let Some(&s) = self.variables.get(&id.string) {
            Ok(s)
        } else if let Some(p) = self.parent {
            p.find_variable(id)
        } else {
            Err(Error::UndeclaredIdentifier(id))
        }
    }
}


#[derive(Debug, Copy, Clone)]
enum LRValue {
    Left(ir::Value),
    Right(ir::Value),
}

impl<'a> Lower<'a> {
    fn parse_type(&mut self, ty: &'a ast::Type) -> Result<'a, ir::Type> {
        match &ty.kind {
            ast::TypeKind::Simple(string) => match string.as_ref() {
                "int" => Ok(self.prog.define_type_int(32)),
                "bool" => Ok(self.prog.type_bool()),
                "void" => Ok(self.prog.type_void()),
                _ => Err(Error::InvalidType(ty)),
            },
            ast::TypeKind::Ref(inner) => {
                let inner = self.parse_type(inner)?;
                Ok(self.prog.define_type_ptr(inner))
            },
        }
    }

    fn parse_literal(&mut self, span: Span, lit: &str, expect_ty: Option<ir::Type>) -> Result<'static, ir::Const> {
        if let Some(ty) = expect_ty {
            if ty != self.prog.type_void() {
                let value = match self.prog.get_type(ty) {
                    ir::TypeInfo::Integer { bits: 1 } =>
                        lit.parse::<bool>().map(|b| b as i32).map_err(|_| ()),
                    ir::TypeInfo::Integer { bits: 32 } =>
                        lit.parse::<i32>().map_err(|_| ()),
                    _ => {
                        return Err(Error::InvalidLiteralType {
                            span,
                            ty: self.prog.format_type(ty).to_string(),
                        })
                    }
                };

                return value
                    .map(|value| ir::Const::new(ty, value))
                    .map_err(|()| Error::InvalidLiteral {
                        span,
                        lit: lit.to_owned(),
                        ty: self.prog.format_type(ty).to_string(),
                    });
            }
        }

        match lit {
            "true" => Ok(ir::Const::new(self.prog.type_bool(), true as i32)),
            "false" => Ok(ir::Const::new(self.prog.type_bool(), false as i32)),
            _ => Err(Error::CannotInferType(span)),
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

    fn check_type_match(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()> {
        if let Some(expected) = expected {
            if expected == self.prog.type_void() {
                return Ok(())
            }

            if expected != actual {
                return Err(Error::TypeMismatch {
                    expression: expr,
                    expected: self.prog.format_type(expected).to_string(),
                    actual: self.prog.format_type(actual).to_string(),
                })
            }
        }
        Ok(())
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

    fn append_store(&mut self, span: Span, addr: LRValue, value: ir::Value) -> Result<'static, ir::Value> {
        match addr {
            LRValue::Left(addr) =>
                Ok(ir::Value::Instr(self.append_instr(ir::InstructionInfo::Store { addr, value }))),
            LRValue::Right(_) =>
                Err(Error::StoreIntoRValue(span)),
        }
    }

    /// None means this expression doesn't return control, eg. it returns from the function or breaks
    fn append_expr(&mut self,
                       scope: &mut Scope,
                       expr: &'a ast::Expression,
                       expect_ty: Option<ir::Type>,
    ) -> Result<'a, LRValue> {
        match &expr.kind {
            ast::ExpressionKind::Literal { value } => {
                let value = self.parse_literal(expr.span, &value, expect_ty)?;
                Ok(LRValue::Right(ir::Value::Const(value)))
            }
            ast::ExpressionKind::Identifier { id } => {
                let var = scope.find_variable(id)?;
                self.check_type_match(expr, expect_ty, self.type_of_lrvalue(var))?;
                Ok(var)
            }
            ast::ExpressionKind::Ref { inner } => {
                let expect_ty_inner = expect_ty
                    .map(|ty| {
                        self.prog
                            .get_type(ty)
                            .as_ptr()
                            .ok_or(Error::ExpectPointerType { actual: self.prog.format_type(ty).to_string() })
                    }).transpose()?;

                let inner = self.append_expr(scope, inner, expect_ty_inner)?;
                match inner {
                    //ref turns an lvalue into an rvalue
                    LRValue::Left(inner) => Ok(LRValue::Right(inner)),
                    LRValue::Right(_) => Err(Error::ReferenceOfLValue(expr.span)),
                }
            }
            ast::ExpressionKind::DeRef { inner } => {
                let expect_ty_inner = expect_ty.map(|ty| self.prog.define_type_ptr(ty));

                //load to get the value and wrap as lvalue again
                self.append_expr_loaded(scope, inner, expect_ty_inner)
                    .map(LRValue::Left)
            }
            ast::ExpressionKind::Call { target } => {
                let expect_ty = expect_ty.and_then(|ty|
                    if ty == self.prog.type_void() {
                        //we don't care about the return type of the function here
                        None
                    } else {
                        Some(self.prog.define_type_func(ty))
                    }
                );
                let target = self.append_expr_loaded(scope, target, expect_ty)?;

                //we still need to verify that target was indeed a function
                let ty = self.prog.type_of_value(target);
                self.prog.get_type(ty).as_func()
                    .ok_or_else(|| Error::ExpectFunctionType { actual: self.prog.format_type(ty).to_string() })?;

                let call = self.append_instr(ir::InstructionInfo::Call { target });
                Ok(LRValue::Right(ir::Value::Instr(call)))
            },
            ast::ExpressionKind::Return { value } => {
                let ret_ty = self.prog.get_func(self.curr_func).ret_ty;

                let value = if let Some(value) = value {
                    self.append_expr_loaded(scope, value, Some(ret_ty))?
                } else {
                    //check that function return type is indeed void
                    let void = self.prog.type_void();
                    self.check_type_match(expr, Some(ret_ty), void)?;
                    ir::Value::Undef(void)
                };

                let ret = ir::Terminator::Return { value };
                self.prog.get_block_mut(self.curr_block).terminator = ret;

                //start block and return undef so we can continue as if nothing happened
                self.start_new_block();
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                Ok(LRValue::Left(ir::Value::Undef(self.prog.define_type_ptr(ty))))
            }
        }
    }

    fn append_expr_loaded(&mut self,
                              scope: &mut Scope,
                              expr: &'a ast::Expression,
                              expect_ty: Option<ir::Type>,
    ) -> Result<'a, ir::Value> {
        let value = self.append_expr(scope, expr, expect_ty)?;
        Ok(self.append_load(value))
    }

    fn append_func(&mut self, scope: &Scope, func: &'a ast::Function) -> Result<'a, ()> {
        let ir_func = *self.functions.get(&*func.id.string).unwrap();
        self.curr_func = ir_func;

        self.start_new_block();
        self.prog.get_func_mut(ir_func).entry = self.curr_block;

        self.append_block(&mut scope.nest(), &func.body)?;

        if self.prog.get_func(self.curr_func).entry == self.curr_block {
            //TODO this return check has lots of false negatives
            return Err(Error::MissingReturn(func))
        }

        Ok(())
    }

    fn lower(mut self, prog: &'a ast::Program) -> Result<ir::Program> {
        let mut scope = Scope::default();

        //temporary entry block, will be overwritten later
        let tmp_entry = self.prog.get_func(self.prog.main).entry;

        //parse all function headers and create ir equivalents
        let mut main = None;
        for item in &prog.items {
            match item {
                ast::Item::Function(func) => {
                    let ret_ty = self.parse_type(&func.ret_ty)?;
                    let ir_func = ir::FunctionInfo::new(ret_ty, tmp_entry, &mut self.prog);
                    let ir_func = self.prog.define_func(ir_func);

                    scope.declare_variable(&func.id, LRValue::Right(ir::Value::Func(ir_func)))?;
                    assert!(self.functions.insert(&func.id.string, ir_func).is_none());

                    if &func.id.string == "main" {
                        main = Some(ir_func);
                    }
                },
            }
        }

        for item in &prog.items {
            match item {
                ast::Item::Function(func) => {
                    self.append_func(&scope, func)?;
                },
            }
        }

        if let Some(main) = main {
            self.prog.main = main;
        } else {
            return Err(Error::NoMainFunction)
        }

        Ok(self.prog)
    }

    fn append_block(&mut self, scope: &Scope, block: &'a ast::Block) -> Result<'a, ()> {
        let scope = &mut scope.nest();

        for stmt in &block.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "everything is mutable for now");
                    let expect_ty = decl.ty.as_ref()
                        .map(|ty| self.parse_type(ty))
                        .transpose()?;

                    let value = decl.init.as_ref()
                        .map(|init| self.append_expr_loaded(scope, init, expect_ty))
                        .transpose()?;

                    //figure out the type
                    let value_ty = value.map(|v| self.prog.type_of_value(v));
                    let ty = expect_ty.or(value_ty).ok_or(Error::CannotInferType(decl.span))?;

                    //define the slot
                    let slot = self.new_slot(ty);
                    self.prog.get_func_mut(self.curr_func).slots.push(slot);
                    scope.declare_variable(&decl.id, LRValue::Left(ir::Value::Slot(slot)))?;

                    //optionally store the value
                    if let Some(value) = value {
                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                        self.append_instr(store);
                    }
                }
                ast::StatementKind::Assignment(assign) => {
                    let addr = self.append_expr(scope, &assign.left, None)?;
                    let ty = self.type_of_lrvalue(addr);

                    let value = self.append_expr_loaded(scope, &assign.right, Some(ty))?;
                    self.append_store(assign.span, addr, value)?;
                }
                ast::StatementKind::If(if_stmt) => {
                    //condition
                    let cond = self.append_expr_loaded(scope, &if_stmt.cond, Some(self.prog.type_bool()))?;
                    let cond_end_block = self.curr_block;

                    //then
                    self.start_new_block();
                    let then_start_block = self.curr_block;
                    self.append_block(scope, &if_stmt.then_block)?;
                    let then_end_block = self.curr_block;

                    //else
                    self.start_new_block();
                    let else_start_block = self.curr_block;
                    if let Some(else_block) = &if_stmt.else_block {
                        self.append_block(scope, else_block)?;
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
                ast::StatementKind::Block(block) => {
                    self.append_block(scope, block)?;
                }
                ast::StatementKind::Expression(expr) => {
                    self.append_expr(scope, expr, Some(self.prog.type_void()))?;
                }
            }
        }

        Ok(())
    }
}

type TypeString = String;

#[derive(Debug)]
pub enum Error<'a> {
    //types
    InvalidType(&'a ast::Type),
    CannotInferType(Span),
    TypeMismatch {
        expression: &'a ast::Expression,
        expected: TypeString,
        actual: TypeString,
    },
    ExpectPointerType {
        actual: TypeString
    },
    ExpectFunctionType {
        actual: TypeString
    },

    //literals
    InvalidLiteralType {
        span: Span,
        ty: TypeString,
    },
    InvalidLiteral {
        span: Span,
        lit: String,
        ty: TypeString,
    },

    //lrvalue
    StoreIntoRValue(Span),
    ReferenceOfLValue(Span),

    //other
    UndeclaredIdentifier(&'a ast::Identifier),
    IdentifierDeclaredTwice(&'a ast::Identifier),
    NoMainFunction,
    MissingReturn(&'a ast::Function),
}

pub fn lower(prog: &ast::Program) -> Result<ir::Program> {
    let ir_prog = ir::Program::new();
    let lower = Lower {
        functions: Default::default(),
        curr_func: ir_prog.main,
        curr_block: ir_prog.get_func(ir_prog.main).entry,
        prog: ir_prog,
        ph: PhantomData
    };
    lower.lower(prog)
}