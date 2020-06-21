use std::marker::PhantomData;

use indexmap::map::IndexMap;

use crate::front::{ast, Span};
use crate::mid::ir;

type Error<'a> = LowerError<'a>;
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

fn binary_op_map_kind(ast_kind: ast::BinaryOp) -> ir::BinaryOp {
    match ast_kind {
        ast::BinaryOp::Add => ir::BinaryOp::Add,
        ast::BinaryOp::Sub => ir::BinaryOp::Sub,
        ast::BinaryOp::Mul => ir::BinaryOp::Mul,
        ast::BinaryOp::Div => ir::BinaryOp::Div,
        ast::BinaryOp::Mod => ir::BinaryOp::Mod,
        ast::BinaryOp::Eq => ir::BinaryOp::Eq,
        ast::BinaryOp::Neq => ir::BinaryOp::Neq,
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
                "byte" => Ok(self.prog.define_type_int(8)),
                _ => Err(Error::InvalidType(ty)),
            },
            ast::TypeKind::Ref(inner) => {
                let inner = self.parse_type(inner)?;
                Ok(self.prog.define_type_ptr(inner))
            },
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|p| self.parse_type(p))
                    .collect::<Result<_>>()?;
                let ret = self.parse_type(ret)?;
                Ok(self.prog.define_type_func(ir::FunctionType { params, ret, }))
            }
        }
    }

    fn parse_literal(&mut self, span: Span, lit: &str, expect_ty: Option<ir::Type>) -> Result<'static, ir::Const> {
        if lit == "null" {
            let void_ptr_ty = self.prog.define_type_ptr(self.prog.type_void());
            let null_ptr_const = ir::Const::new(void_ptr_ty, 0);

            return if let Some(ty) = expect_ty {
                if ty != void_ptr_ty {
                    Err(Error::InvalidLiteral {
                        span,
                        lit: lit.to_owned(),
                        ty: self.prog.format_type(ty).to_string(),
                    })
                } else {
                    Ok(null_ptr_const)
                }
            } else {
                Ok(null_ptr_const)
            }
        }


        if let Some(ty) = expect_ty {
            let value = match self.prog.get_type(ty) {
                ir::TypeInfo::Integer { bits: 1 } =>
                    lit.parse::<bool>().map(|b| b as i32).map_err(|_| ()),
                ir::TypeInfo::Integer { bits: 8 } =>
                    lit.parse::<i8>().map(|v| v as i32).map_err(|_| ()),
                ir::TypeInfo::Integer { bits: 32 } =>
                    lit.parse::<i32>().map_err(|_| ()),
                _ => {
                    return Err(Error::InvalidLiteralType {
                        span,
                        ty: self.prog.format_type(ty).to_string(),
                    })
                }
            };

            match value {
                Ok(value) => Ok(ir::Const::new(ty, value)),
                Err(()) => Err(Error::InvalidLiteral {
                    span,
                    lit: lit.to_owned(),
                    ty: self.prog.format_type(ty).to_string(),
                }),
            }
        } else {
            match lit {
                "true" => Ok(ir::Const::new(self.prog.type_bool(), true as i32)),
                "false" => Ok(ir::Const::new(self.prog.type_bool(), false as i32)),
                _ => Err(Error::CannotInferType(span)),
            }
        }
    }

    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type {
        match value {
            LRValue::Left(value) => {
                let ty = self.prog.type_of_value(value);
                self.prog.get_type(ty).unwrap_ptr().expect("lvalue should have pointer type")
            },
            LRValue::Right(value) => {
                self.prog.type_of_value(value)
            },
        }
    }

    fn check_type_match(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()> {
        if let Some(expected) = expected {
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

    fn check_integer_type(&self, expr: &'a ast::Expression, actual: ir::Type) -> Result<'a, ()> {
        match self.prog.get_type(actual).unwrap_int() {
            Some(_) => Ok(()),
            None => Err(Error::ExpectIntegerType {
                expression: expr,
                actual: self.prog.format_type(actual).to_string(),
            })
        }
    }

    fn start_new_block(&mut self) {
        self.curr_block = self.prog.define_block(ir::BlockInfo {
            instructions: vec![],
            terminator: ir::Terminator::Unreachable,
        });
    }

    fn define_slot(&mut self, inner_ty: ir::Type) -> ir::StackSlot {
        let slot = ir::StackSlotInfo::new(inner_ty, &mut self.prog);
        self.prog.define_slot(slot)
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
        let result_value = match &expr.kind {
            ast::ExpressionKind::Literal { value } => {
                let value = self.parse_literal(expr.span, &value, expect_ty)?;
                Ok(LRValue::Right(ir::Value::Const(value)))
            }
            ast::ExpressionKind::Identifier { id } => {
                let var = scope.find_variable(id)?;
                self.check_type_match(expr, expect_ty, self.type_of_lrvalue(var))?;
                Ok(var)
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let expect_ty = match kind {
                    ast::BinaryOp::Add | ast::BinaryOp::Sub | ast::BinaryOp::Mul |
                    ast::BinaryOp::Div | ast::BinaryOp::Mod => {
                        expect_ty
                    },
                    ast::BinaryOp::Eq | ast::BinaryOp::Neq => {
                        self.check_type_match(expr, expect_ty, self.prog.type_bool())?;
                        None
                    }
                };

                let ir_left = self.append_expr_loaded(scope, left, expect_ty)?;
                self.check_integer_type(left, self.prog.type_of_value(ir_left))?;

                //use the left type for both inference and correctness checking
                let expect_ty = self.prog.type_of_value(ir_left);
                let ir_right = self.append_expr_loaded(scope, right, Some(expect_ty))?;

                let instr = self.append_instr(ir::InstructionInfo::Binary {
                    kind: binary_op_map_kind(*kind),
                    left: ir_left,
                    right: ir_right,
                });
                Ok(LRValue::Right(ir::Value::Instr(instr)))
            }
            ast::ExpressionKind::Unary { kind, inner } => {
                match kind {
                    ast::UnaryOp::Ref => {
                        //error if expect_ty is not a pointer, otherwise unwrap it
                        let expect_ty_inner = expect_ty
                            .map(|ty| {
                                self.prog
                                    .get_type(ty)
                                    .unwrap_ptr()
                                    .ok_or_else(|| Error::ExpectPointerType {
                                        expression: expr,
                                        actual: self.prog.format_type(ty).to_string(),
                                    })
                            }).transpose()?;

                        let inner = self.append_expr(scope, inner, expect_ty_inner)?;
                        match inner {
                            //ref turns an lvalue into an rvalue
                            LRValue::Left(inner) => Ok(LRValue::Right(inner)),
                            LRValue::Right(_) => Err(Error::ReferenceOfLValue(expr.span)),
                        }
                    },
                    ast::UnaryOp::Deref => {
                        let expect_ty_inner = expect_ty.map(|ty| self.prog.define_type_ptr(ty));

                        //load to get the value and wrap as lvalue again
                        self.append_expr_loaded(scope, inner, expect_ty_inner)
                            .map(LRValue::Left)
                    },
                    ast::UnaryOp::Neg => {
                        let inner = self.append_expr_loaded(scope, inner, expect_ty)?;
                        let ty = self.prog.type_of_value(inner);
                        self.check_integer_type(expr, ty)?;

                        let instr = self.append_instr(ir::InstructionInfo::Binary {
                            kind: ir::BinaryOp::Sub,
                            left: ir::Value::Const(ir::Const::new(ty, 0)),
                            right: inner,
                        });
                        Ok(LRValue::Right(ir::Value::Instr(instr)))
                    },
                }
            },
            ast::ExpressionKind::Call { target, args } => {
                let target = self.append_expr_loaded(scope, target, None)?;

                //check that the target is a function
                let target_ty = self.prog.type_of_value(target);
                let target_ty = self.prog.get_type(target_ty).as_func()
                    .ok_or_else(|| Error::ExpectFunctionType {
                        expression: expr,
                        actual: self.prog.format_type(target_ty).to_string(),
                    })?;


                //check return type and arg count
                self.check_type_match(expr, expect_ty, target_ty.ret)?;
                if target_ty.params.len() != args.len() {
                    return Err(Error::WrongArgCount {
                        call: expr, expected: target_ty.params.len(), actual: args.len(),
                    })
                }

                //append arg expressions and typecheck them
                let target_param_types = target_ty.params.clone();
                let ir_args =  args.iter()
                    .enumerate()
                    .map(|(i, arg)|
                        self.append_expr_loaded(scope, arg, Some(target_param_types[i]))
                    )
                    .collect::<Result<_>>()?;

                let call = ir::InstructionInfo::Call {
                    target,
                    args: ir_args,
                };
                let call = self.append_instr(call);
                Ok(LRValue::Right(ir::Value::Instr(call)))
            },
            ast::ExpressionKind::Return { value } => {
                let ret_ty = self.prog.get_func(self.curr_func).func_ty.ret;

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
                //TODO ideally ir would have a "never" type which we could use here
                //  or even more ideally we'd have proper typechecking in lower!
                let ty = expect_ty.unwrap_or(self.prog.type_void());
                Ok(LRValue::Left(ir::Value::Undef(self.prog.define_type_ptr(ty))))
            }
        }?;

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let ty = self.type_of_lrvalue(result_value);
            self.check_type_match(expr, expect_ty, ty).expect("bug in lower")
        }

        Ok(result_value)
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

        let mut scope = scope.nest();

        for param in &func.params {
            let ty = self.parse_type(&param.ty)?;
            let ir_param = self.prog.define_param(ir::ParameterInfo { ty });

            //allocate slots for parameters so their address can be taken
            let slot = self.define_slot(ty);
            self.append_instr(ir::InstructionInfo::Store {
                addr: ir::Value::Slot(slot),
                value: ir::Value::Param(ir_param),
            });

            //push slot and param to function
            let curr_func = self.prog.get_func_mut(self.curr_func);
            curr_func.params.push(ir_param);
            curr_func.slots.push(slot);

            scope.declare_variable(&param.id, LRValue::Left(ir::Value::Slot(slot)))?;
        }

        let body = func.body.as_ref().expect("can only generate code for functions with body");
        self.append_block(&mut scope, body)?;

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
                    let ret_ty = func.ret_ty.as_ref()
                        .map_or(Ok(self.prog.type_void()), |t| self.parse_type(t))?;

                    let param_tys = func.params.iter()
                        .map(|param| self.parse_type(&param.ty))
                        .collect::<Result<_>>()?;
                    let func_ty = ir::FunctionType { params: param_tys, ret: ret_ty };

                    let value = match (func.ext, &func.body) {
                        (true, None) => {
                            //external function, leave this for the backend to figure out
                            let func_ty = self.prog.define_type_func(func_ty);
                            let ir_ext = ir::ExternInfo { name: func.id.string.clone(), ty: func_ty };
                            let ir_ext = self.prog.define_ext(ir_ext);
                            ir::Value::Extern(ir_ext)
                        }
                        (false, None) => {
                            //functions need bodies
                            return Err(Error::MissingFunctionBody(func))
                        }
                        (ext, Some(_)) => {
                            //standard function, maybe marked extern
                            let mut ir_func = ir::FunctionInfo::new(func_ty, tmp_entry, &mut self.prog);
                            if ext {
                                ir_func.global_name = Some(func.id.string.clone());
                            }
                            let ir_func = self.prog.define_func(ir_func);

                            if self.functions.insert(&func.id.string, ir_func).is_some() {
                                return Err(Error::IdentifierDeclaredTwice(&func.id));
                            }
                            if &func.id.string == "main" {
                                let type_int = self.prog.define_type_int(32);
                                let main_func_ty = self.prog.define_type_func(ir::FunctionType {
                                    params: Vec::new(),
                                    ret: type_int,
                                });

                                let func_ty = self.prog.get_func(ir_func).ty;

                                if func_ty != main_func_ty {
                                    return Err(Error::MainFunctionWrongType {
                                        expected: self.prog.format_type(main_func_ty).to_string(),
                                        actual: self.prog.format_type(func_ty).to_string(),
                                    })
                                }

                                main = Some(ir_func);
                            }

                            ir::Value::Func(ir_func)
                        }
                    };

                    scope.declare_variable(&func.id, LRValue::Right(value))?;
                },
            }
        }

        //actually generate code for functions
        for item in &prog.items {
            match item {
                ast::Item::Function(func) => {
                    if func.body.is_some() {
                        self.append_func(&scope, func)?;
                    }
                },
            }
        }

        if let Some(main) = main {
            //typecheck
            let type_int = self.prog.define_type_int(32);
            let main_func_ty = self.prog.define_type_func(ir::FunctionType {
                params: Vec::new(),
                ret: type_int,
            });

            let func_ty = self.prog.get_func(main).ty;

            if func_ty != main_func_ty {
                return Err(Error::MainFunctionWrongType {
                    expected: self.prog.format_type(main_func_ty).to_string(),
                    actual: self.prog.format_type(func_ty).to_string(),
                })
            }

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
                    let slot = self.define_slot(ty);
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
                ast::StatementKind::While(while_stmt) => {
                    let start_block = self.curr_block;

                    //condition
                    self.start_new_block();
                    let cond_start_block = self.curr_block;
                    let cond = self.append_expr_loaded(scope, &while_stmt.cond, Some(self.prog.type_bool()))?;
                    let cond_end_block = self.curr_block;

                    //body
                    self.start_new_block();
                    let body_start_block = self.curr_block;
                    self.append_block(scope, &while_stmt.body)?;
                    let body_end_block = self.curr_block;

                    //end
                    self.start_new_block();
                    let end_block = self.curr_block;

                    //connect everything
                    let branch = ir::Terminator::Branch { cond, targets: [body_start_block, end_block] };
                    let jump_cond = ir::Terminator::Jump { target: cond_start_block };

                    self.prog.get_block_mut(start_block).terminator = jump_cond;
                    self.prog.get_block_mut(cond_end_block).terminator = branch;
                    self.prog.get_block_mut(body_end_block).terminator = jump_cond;
                }
                ast::StatementKind::Block(block) => {
                    self.append_block(scope, block)?;
                }
                ast::StatementKind::Expression(expr) => {
                    self.append_expr(scope, expr, None)?;
                }
            }
        }

        Ok(())
    }
}

type TypeString = String;

#[derive(Debug)]
pub enum LowerError<'a> {
    //types
    InvalidType(&'a ast::Type),
    CannotInferType(Span),
    TypeMismatch {
        expression: &'a ast::Expression,
        expected: TypeString,
        actual: TypeString,
    },
    ExpectIntegerType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },
    ExpectPointerType {
        expression: &'a ast::Expression,
        actual: TypeString,
    },
    ExpectFunctionType {
        expression: &'a ast::Expression,
        actual: TypeString,
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

    //identifier
    UndeclaredIdentifier(&'a ast::Identifier),
    IdentifierDeclaredTwice(&'a ast::Identifier),

    //other
    NoMainFunction,
    MainFunctionWrongType {
        expected: TypeString,
        actual: TypeString,
    },
    MissingReturn(&'a ast::Function),
    MissingFunctionBody(&'a ast::Function),
    WrongArgCount {
        call: &'a ast::Expression,
        expected: usize,
        actual: usize,
    }
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