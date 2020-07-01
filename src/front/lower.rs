use std::collections::HashSet;

use indexmap::map::IndexMap;

use crate::front::{ast, Span};
use crate::mid::ir;

type Error<'a> = LowerError<'a>;
type Result<'a, T> = std::result::Result<T, Error<'a>>;

struct LoopInfo {
    cond: ir::Block,
    end: ir::Block,
}

struct Lower<'m, 'a> {
    prog: &'m mut ir::Program,

    module_skeleton: &'m ModuleSkeleton<'m>,
    modules: &'m IndexMap<&'a str, ModuleSkeleton<'m>>,

    //TODO replace this global state with parameters
    curr_func: ir::Function,
    curr_block: ir::Block,

    curr_loops: Vec<LoopInfo>,
}

#[derive(Debug, Default)]
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

//utility functions on ir::Program
trait ProgramExt {
    fn parse_type<'a>(&mut self, ty: &'a ast::Type) -> Result<'a, ir::Type>;
    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type;
    fn check_type_match<'a>(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()>;
    fn check_integer_type<'a>(&self, expr: &'a ast::Expression, actual: ir::Type) -> Result<'a, ()>;
}

impl ProgramExt for ir::Program {
    fn parse_type<'a>(&mut self, ty: &'a ast::Type) -> Result<'a, ir::Type> {
        match &ty.kind {
            ast::TypeKind::Simple(string) => match string.as_ref() {
                "int" => Ok(self.define_type_int(32)),
                "bool" => Ok(self.type_bool()),
                "void" => Ok(self.type_void()),
                "byte" => Ok(self.define_type_int(8)),
                _ => Err(Error::InvalidType(ty)),
            },
            ast::TypeKind::Ref(inner) => {
                let inner = self.parse_type(inner)?;
                Ok(self.define_type_ptr(inner))
            },
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|p| self.parse_type(p))
                    .collect::<Result<_>>()?;
                let ret = self.parse_type(ret)?;
                Ok(self.define_type_func(ir::FunctionType { params, ret }))
            }
        }
    }

    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type {
        match value {
            LRValue::Left(value) => {
                let ty = self.type_of_value(value);
                self.get_type(ty).unwrap_ptr().expect("lvalue should have pointer type")
            },
            LRValue::Right(value) => {
                self.type_of_value(value)
            },
        }
    }

    fn check_type_match<'a>(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()> {
        if let Some(expected) = expected {
            if expected != actual {
                return Err(Error::TypeMismatch {
                    expression: expr,
                    expected: self.format_type(expected).to_string(),
                    actual: self.format_type(actual).to_string(),
                })
            }
        }
        Ok(())
    }

    fn check_integer_type<'a>(&self, expr: &'a ast::Expression, actual: ir::Type) -> Result<'a, ()> {
        match self.get_type(actual).unwrap_int() {
            Some(_) => Ok(()),
            None => Err(Error::ExpectIntegerType {
                expression: expr,
                actual: self.format_type(actual).to_string(),
            })
        }
    }
}

fn new_target(block: ir::Block) -> ir::Target {
    ir::Target { block, phi_values: Vec::new() }
}

fn new_branch(cond: ir::Value, true_block: ir::Block, false_block: ir::Block) -> ir::Terminator {
    ir::Terminator::Branch {
        cond,
        targets: [
            new_target(true_block),
            new_target(false_block)
        ],
    }
}

impl<'m, 'a> Lower<'m, 'a> {
    fn start_new_block(&mut self) {
        self.curr_block = self.prog.define_block(ir::BlockInfo {
            phis: Vec::new(),
            instructions: Vec::new(),
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
            ast::ExpressionKind::Null => {
                // flexible, null can take on any pointer type
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                self.prog.get_type(ty).unwrap_ptr()
                    .ok_or(Error::ExpectPointerType {
                        expression: expr,
                        actual: self.prog.format_type(ty).to_string(),
                    })?;

                Ok(LRValue::Right(ir::Value::Const(ir::Const { ty, value: 0 })))
            }
            ast::ExpressionKind::BoolLit { value } => {
                let ty_bool = self.prog.type_bool();
                self.prog.check_type_match(expr, expect_ty, ty_bool)?;
                Ok(LRValue::Right(ir::Value::Const(ir::Const { ty: ty_bool, value: *value as i32 })))
            }
            ast::ExpressionKind::IntLit { value } => {
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                self.prog.get_type(ty).unwrap_int()
                    .ok_or(Error::ExpectIntegerType {
                        expression: expr,
                        actual: self.prog.format_type(ty).to_string(),
                    })?;

                let value = value.parse::<i32>()
                    .map_err(|_| Error::InvalidLiteral {
                        span: expr.span,
                        lit: value.clone(),
                        ty: self.prog.format_type(ty).to_string(),
                    })?;

                Ok(LRValue::Right(ir::Value::Const(ir::Const { ty, value })))
            }
            ast::ExpressionKind::StringLit { .. } => {
                panic!("string literals only supported in consts for now")
            }
            ast::ExpressionKind::Identifier { id } => {
                let value = scope.find_variable(id)?;
                self.prog.check_type_match(expr, expect_ty, self.prog.type_of_lrvalue(value))?;
                Ok(value)
            }
            ast::ExpressionKind::ModuleIdentifier { module, id } => {
                //find the module
                let module_skeleton: &ModuleSkeleton = self.modules.get(&*module.string)
                    .ok_or(Error::ModuleNotFound { module })?;

                //check that it's actually used
                if !self.module_skeleton.used_modules.contains(&*module.string) {
                    return Err(Error::ModuleNotUsed { module })
                }

                //find the value itself
                let value = module_skeleton.scope.find_variable(id)?;
                self.prog.check_type_match(expr, expect_ty, self.prog.type_of_lrvalue(value))?;
                Ok(value)
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let expect_ty = match kind {
                    ast::BinaryOp::Add | ast::BinaryOp::Sub | ast::BinaryOp::Mul |
                    ast::BinaryOp::Div | ast::BinaryOp::Mod => {
                        expect_ty
                    },
                    ast::BinaryOp::Eq | ast::BinaryOp::Neq => {
                        self.prog.check_type_match(expr, expect_ty, self.prog.type_bool())?;
                        None
                    }
                };

                let ir_left = self.append_expr_loaded(scope, left, expect_ty)?;
                self.prog.check_integer_type(left, self.prog.type_of_value(ir_left))?;

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
                        self.prog.check_integer_type(expr, ty)?;

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
                self.prog.check_type_match(expr, expect_ty, target_ty.ret)?;
                if target_ty.params.len() != args.len() {
                    return Err(Error::WrongArgCount {
                        call: expr,
                        expected: target_ty.params.len(),
                        actual: args.len(),
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
                    self.prog.check_type_match(expr, Some(ret_ty), void)?;
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
            },
            ast::ExpressionKind::Continue =>
                self.append_break_or_continue(expr, expect_ty, |info| info.cond),
            ast::ExpressionKind::Break =>
                self.append_break_or_continue(expr, expect_ty, |info| info.end),
        }?;

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let ty = self.prog.type_of_lrvalue(result_value);
            self.prog.check_type_match(expr, expect_ty, ty).expect("bug in lower")
        }

        Ok(result_value)
    }

    fn append_break_or_continue<F: FnOnce(&LoopInfo) -> ir::Block>(
        &mut self,
        expr: &'a ast::Expression,
        expect_ty: Option<ir::Type>,
        target: F,
    ) -> Result<'a, LRValue> {
        let loop_info = self.curr_loops.last()
            .ok_or(Error::NotInLoop { expr })?;

        let jump_cond = ir::Terminator::Jump { target: new_target(target(loop_info)) };
        self.prog.get_block_mut(self.curr_block).terminator = jump_cond;

        self.start_new_block();
        let ty = expect_ty.unwrap_or(self.prog.type_void());
        Ok(LRValue::Left(ir::Value::Undef(self.prog.define_type_ptr(ty))))
    }

    fn append_expr_loaded(
        &mut self,
        scope: &mut Scope,
        expr: &'a ast::Expression,
        expect_ty: Option<ir::Type>,
    ) -> Result<'a, ir::Value> {
        let value = self.append_expr(scope, expr, expect_ty)?;
        Ok(self.append_load(value))
    }

    fn append_block(&mut self, scope: &Scope, block: &'a ast::Block) -> Result<'a, ()> {
        let scope = &mut scope.nest();

        for stmt in &block.statements {
            match &stmt.kind {
                ast::StatementKind::Declaration(decl) => {
                    assert!(!decl.mutable, "everything is mutable for now");
                    let expect_ty = decl.ty.as_ref()
                        .map(|ty| self.prog.parse_type(ty))
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
                    let ty = self.prog.type_of_lrvalue(addr);

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
                    let branch = new_branch(cond, then_start_block, else_start_block);
                    let jump_end = ir::Terminator::Jump { target: new_target(end_block) };

                    self.prog.get_block_mut(cond_end_block).terminator = branch;
                    self.prog.get_block_mut(then_end_block).terminator = jump_end.clone();
                    self.prog.get_block_mut(else_end_block).terminator = jump_end;
                }
                ast::StatementKind::While(while_stmt) => {
                    let start_block = self.curr_block;

                    //condition
                    self.start_new_block();
                    let cond_start_block = self.curr_block;
                    let cond = self.append_expr_loaded(scope, &while_stmt.cond, Some(self.prog.type_bool()))?;
                    let cond_end_block = self.curr_block;

                    //end
                    self.start_new_block();
                    let end_block = self.curr_block;

                    let info = LoopInfo {
                        cond: cond_start_block,
                        end: end_block,
                    };
                    self.curr_loops.push(info);

                    //body
                    self.start_new_block();
                    let body_start_block = self.curr_block;
                    self.append_block(scope, &while_stmt.body)?;
                    let body_end_block = self.curr_block;

                    self.curr_loops.pop().unwrap();

                    //connect everything
                    let branch = new_branch(cond, body_start_block, end_block);
                    let jump_cond = ir::Terminator::Jump { target: new_target(cond_start_block) };

                    self.prog.get_block_mut(start_block).terminator = jump_cond.clone();
                    self.prog.get_block_mut(cond_end_block).terminator = branch;
                    self.prog.get_block_mut(body_end_block).terminator = jump_cond;

                    //continue withing code to end
                    self.curr_block = end_block;
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

    fn append_func(&mut self, ast_func: &'a ast::Function, ir_func: ir::Function) -> Result<'a, ()> {
        self.curr_func = ir_func;

        self.start_new_block();
        self.prog.get_func_mut(ir_func).entry = self.curr_block;

        let mut scope = self.module_skeleton.scope.nest();

        for param in &ast_func.params {
            let ty = self.prog.parse_type(&param.ty)?;
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

        let body = ast_func.body.as_ref().expect("can only generate code for functions with body");
        self.append_block(&mut scope, body)?;

        if self.prog.get_func(self.curr_func).entry == self.curr_block {
            //TODO this return check has lots of false negatives
            return Err(Error::MissingReturn(ast_func))
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

    //main
    NoMainFunction,
    MainFunctionWrongType {
        expected: TypeString,
        actual: TypeString,
    },

    //functions
    MissingReturn(&'a ast::Function),
    MissingFunctionBody(&'a ast::Function),
    WrongArgCount {
        call: &'a ast::Expression,
        expected: usize,
        actual: usize,
    },

    //modules
    ModuleNotFound {
        module: &'a ast::Identifier,
    },
    ModuleNotUsed {
        module: &'a ast::Identifier,
    },

    //other
    NotInLoop {
        expr: &'a ast::Expression,
    }
}

#[derive(Debug, Default)]
struct ModuleSkeleton<'a> {
    scope: Scope<'static>,
    used_modules: HashSet<&'a str>,
    functions_to_lower: Vec<(&'a ast::Function, ir::Function)>,
}

fn build_module_skeleton<'a>(prog: &mut ir::Program, module: &'a ast::Module, is_root: bool) -> Result<'a, ModuleSkeleton<'a>> {
    let mut skeleton = ModuleSkeleton::default();

    for item in &module.items {
        match item {
            ast::Item::UseDecl(decl) => {
                skeleton.used_modules.insert(&decl.name.string);
            }
            ast::Item::Function(ast_func) => {
                let ret_ty = ast_func.ret_ty.as_ref()
                    .map_or(Ok(prog.type_void()), |t| prog.parse_type(t))?;

                let param_tys = ast_func.params.iter()
                    .map(|param| prog.parse_type(&param.ty))
                    .collect::<Result<_>>()?;
                let func_ty = ir::FunctionType { params: param_tys, ret: ret_ty };

                let value = match (ast_func.ext, &ast_func.body) {
                    (true, None) => {
                        //external function, leave this for the backend to figure out
                        let func_ty = prog.define_type_func(func_ty);
                        let ir_ext = ir::ExternInfo { name: ast_func.id.string.clone(), ty: func_ty };
                        let ir_ext = prog.define_ext(ir_ext);
                        ir::Value::Extern(ir_ext)
                    }
                    (false, None) => {
                        //functions need bodies
                        return Err(Error::MissingFunctionBody(ast_func))
                    }
                    (ext, Some(_)) => {
                        //standard function, maybe marked extern
                        let mut ir_func = ir::FunctionInfo::new(func_ty, prog);
                        if ext {
                            ir_func.global_name = Some(ast_func.id.string.clone());
                        }
                        let ir_func = prog.define_func(ir_func);
                        let func_value = ir::Value::Func(ir_func);
                        skeleton.functions_to_lower.push((ast_func, ir_func));

                        //check if this is the main function
                        if is_root && ast_func.id.string == "main" {
                            //typecheck
                            let int_ty = prog.define_type_int(32);
                            let expected_main_ty = ir::FunctionType { params: Vec::new(), ret: int_ty };
                            let expected_main_ty = prog.define_type_func(expected_main_ty);
                            let actual_func_ty = prog.type_of_value(func_value);

                            if expected_main_ty != actual_func_ty {
                                return Err(Error::MainFunctionWrongType {
                                    expected: prog.format_type(expected_main_ty).to_string(),
                                    actual: prog.format_type(actual_func_ty).to_string(),
                                })
                            }

                            prog.main = ir_func;
                        }
                        func_value
                    }
                };

                skeleton.scope.declare_variable(&ast_func.id, LRValue::Right(value))?;
            }
            ast::Item::Const(decl) => {
                let ty = decl.ty.as_ref().map(|ty| prog.parse_type(ty)).transpose()?;
                let init = decl.init.as_ref().expect("consts need initialized for now");

                match &init.kind {
                    ast::ExpressionKind::StringLit { value } => {
                        let ty_byte = prog.define_type_int(8);
                        let ty_byte_ptr = prog.define_type_ptr(ty_byte);
                        prog.check_type_match(&init, ty, ty_byte_ptr)?;

                        let data = prog.define_data(ir::DataInfo {
                            ty: ty_byte_ptr,
                            bytes: value.clone().into_bytes(),
                        });

                        skeleton.scope.declare_variable(&decl.id, LRValue::Right(ir::Value::Data(data)))?;
                    },
                    kind => {
                        panic!("This kind of const initializer is not supported for now: {:?}", kind)
                    }
                }
            }
        }
    }

    Ok(skeleton)
}

pub fn lower(ast_prog: &ast::Program) -> Result<ir::Program> {
    let mut prog = ir::Program::new();

    //keep these as placeholders
    let tmp_func = prog.main;
    let tmp_block = prog.get_func(prog.main).entry;

    //build skeletons
    let mut modules: IndexMap<&str, ModuleSkeleton> = IndexMap::new();

    for (module_name, ast_module) in &ast_prog.modules {
        let is_root = module_name == "";
        let module_info = build_module_skeleton(&mut prog, ast_module, is_root)?;

        modules.insert(module_name, module_info);
    }

    //actually generate code
    for (_, module_skeleton) in &modules {
        let mut lower = Lower {
            prog: &mut prog,
            module_skeleton,
            modules: &modules,
            curr_func: tmp_func,
            curr_block: tmp_block,
            curr_loops: Vec::new(),
        };

        for (ast_func, ir_func) in &module_skeleton.functions_to_lower {
            lower.append_func(ast_func, *ir_func)?;
        }
    }

    //check that we have a main function
    if prog.main == tmp_func {
        return Err(Error::NoMainFunction);
    }

    Ok(prog)
}