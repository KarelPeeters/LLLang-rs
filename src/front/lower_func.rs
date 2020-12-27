use std::collections::{HashMap, HashSet};

use indexmap::map::IndexMap;

use crate::front::{ast, cst};
use crate::front::cst::Item;
use crate::front::error::{Error, Result};
use crate::front::pos::Span;
use crate::front::scope::Scope;
use crate::mid::ir;
use itertools::Itertools;

struct LoopInfo {
    cond: ir::Block,
    end: ir::Block,
    end_needs_return: bool,
}

pub struct LowerFuncState<'m, 'a, 's> {
    pub prog: &'m mut ir::Program,
    pub cst: &'a cst::Program<'a>,

    pub module_scope: &'s Scope<'static, ScopedItem<'a>>,

    pub curr_func: ir::Function,
    pub loop_stack: Vec<LoopInfo>,
}

pub enum ScopedItem<'a> {
    Type(cst::Type),
    Module(cst::Module),
    Value(ir::Value),
}

fn binary_op_to_instr(ast_kind: ast::BinaryOp, left: ir::Value, right: ir::Value) -> ir::InstructionInfo {
    match ast_kind {
        ast::BinaryOp::Add => ir::InstructionInfo::Arithmetic { kind: ir::ArithmeticOp::Add, left, right },
        ast::BinaryOp::Sub => ir::InstructionInfo::Arithmetic { kind: ir::ArithmeticOp::Sub, left, right },
        ast::BinaryOp::Mul => ir::InstructionInfo::Arithmetic { kind: ir::ArithmeticOp::Mul, left, right },
        ast::BinaryOp::Div => ir::InstructionInfo::Arithmetic { kind: ir::ArithmeticOp::Div, left, right },
        ast::BinaryOp::Mod => ir::InstructionInfo::Arithmetic { kind: ir::ArithmeticOp::Mod, left, right },
        ast::BinaryOp::Eq => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Eq, left, right },
        ast::BinaryOp::Neq => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Neq, left, right },
        ast::BinaryOp::Gte => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Gte, left, right },
        ast::BinaryOp::Gt => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Gt, left, right },
        ast::BinaryOp::Lte => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Lte, left, right },
        ast::BinaryOp::Lt => ir::InstructionInfo::Comparison { kind: ir::LogicalOp::Lt, left, right },
    }
}

#[derive(Debug, Copy, Clone)]
enum LRValue {
    Left(ir::Value),
    Right(ir::Value),
}

//utility functions on ir::Program
trait ProgramExt {
    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type;
    fn check_type_match<'a>(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()>;
    fn check_integer_type<'a>(&self, expr: &'a ast::Expression, actual: ir::Type) -> Result<'a, ()>;
}

impl ProgramExt for ir::Program {
    fn type_of_lrvalue(&self, value: LRValue) -> ir::Type {
        match value {
            LRValue::Left(value) => {
                let ty = self.type_of_value(value);
                self.get_type(ty).unwrap_ptr().expect("lvalue should have pointer type")
            }
            LRValue::Right(value) => {
                self.type_of_value(value)
            }
        }
    }

    fn check_type_match<'a>(&self, expr: &'a ast::Expression, expected: Option<ir::Type>, actual: ir::Type) -> Result<'a, ()> {
        if let Some(expected) = expected {
            if expected != actual {
                return Err(Error::TypeMismatch {
                    expression: expr,
                    expected: self.format_type(expected).to_string(),
                    actual: self.format_type(actual).to_string(),
                });
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
        true_target: new_target(true_block),
        false_target: new_target(false_block),
    }
}

enum ContinueOrBreak {
    Break,
    Continue,
}

/// Represents the a point the the program where more code can be appended to.
/// This type intentionally doesn't implement Copy so it's easy to spot when it is accidentally used
/// twice.
struct Flow {
    block: ir::Block,
    needs_return: bool,
}

//TODO general code cleanup: split the code that deals with lowering a single function into a
//  separate module, this file is getting a bit too large and confusing
impl<'m, 'a, 's> LowerFuncState<'m, 'a, 's> {
    fn resolve_path(&self, path: &ast::Path) -> Result<&ScopedItem> {
        path.parents.iter().try_fold()
    }

    fn parse_type(&mut self, ty: &'a ast::Type) -> Result<'a, ir::Type> {
        match &ty.kind {
            ast::TypeKind::Path(path) => {
                match &*path.parents {
                    [module] => {
                        self.cst.root

                        let module = self.find_module(module)?;
                        let declared_struct = module.declared_structs.get(&*path.id.string)
                            .ok_or(Error::UndeclaredIdentifier(&path.id))?;
                        Ok(declared_struct.ty)
                    }
                    _ => self.module_skeleton.parse_local_type(&mut self.prog, ty),
                }
            }
            ast::TypeKind::Ref(_) | ast::TypeKind::Func { .. } | ast::TypeKind::Tuple { .. } =>
                self.module_skeleton.parse_local_type(&mut self.prog, ty)
        }
    }

    #[must_use]
    fn new_flow(&mut self, needs_return: bool) -> Flow {
        Flow {
            block: self.prog.define_block(ir::BlockInfo::new()),
            needs_return,
        }
    }

    fn define_slot(&mut self, inner_ty: ir::Type) -> ir::StackSlot {
        let slot = ir::StackSlotInfo::new(inner_ty, &mut self.prog);
        let slot = self.prog.define_slot(slot);
        self.prog.get_func_mut(self.curr_func).slots.push(slot);
        slot
    }

    fn append_instr(&mut self, block: ir::Block, instr: ir::InstructionInfo) -> ir::Instruction {
        let instr = self.prog.define_instr(instr);
        self.prog.get_block_mut(block).instructions.push(instr);
        instr
    }

    fn append_load(&mut self, block: ir::Block, value: LRValue) -> ir::Value {
        match value {
            LRValue::Left(value) =>
                ir::Value::Instr(self.append_instr(block, ir::InstructionInfo::Load { addr: value })),
            LRValue::Right(value) =>
                value,
        }
    }

    fn append_store(&mut self, block: ir::Block, span: Span, addr: LRValue, value: ir::Value) -> Result<'static, ir::Value> {
        match addr {
            LRValue::Left(addr) =>
                Ok(ir::Value::Instr(self.append_instr(block, ir::InstructionInfo::Store { addr, value }))),
            LRValue::Right(_) =>
                Err(Error::StoreIntoRValue(span)),
        }
    }

    fn append_if<
        T: FnOnce(&mut Self, Flow) -> Result<'a, Flow>,
        E: FnOnce(&mut Self, Flow) -> Result<'a, Flow>
    >(&mut self, flow: Flow, cond: ir::Value, then_func: T, else_func: E) -> Result<'a, Flow> {
        //create flows
        let then_start = self.new_flow(flow.needs_return);
        let then_start_block = then_start.block;
        let then_end = then_func(self, then_start)?;

        let else_start = self.new_flow(flow.needs_return);
        let else_start_block = else_start.block;
        let else_end = else_func(self, else_start)?;

        let end_start = self.new_flow(then_end.needs_return || else_end.needs_return);

        //connect everything
        let branch = new_branch(cond, then_start_block, else_start_block);
        let jump_end = ir::Terminator::Jump { target: new_target(end_start.block) };

        self.prog.get_block_mut(flow.block).terminator = branch;
        self.prog.get_block_mut(then_end.block).terminator = jump_end.clone();
        self.prog.get_block_mut(else_end.block).terminator = jump_end;

        Ok(end_start)
    }

    fn append_expr(
        &mut self,
        flow: Flow,
        scope: &Scope<LRValue>,
        expr: &'a ast::Expression,
        expect_ty: Option<ir::Type>,
    ) -> Result<'a, (Flow, LRValue)> {
        let result: (Flow, LRValue) = match &expr.kind {
            ast::ExpressionKind::Null => {
                // flexible, null can take on any pointer type
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                self.prog.get_type(ty).unwrap_ptr()
                    .ok_or(Error::ExpectPointerType {
                        expression: expr,
                        actual: self.prog.format_type(ty).to_string(),
                    })?;

                (flow, LRValue::Right(ir::Value::Const(ir::Const { ty, value: 0 })))
            }
            ast::ExpressionKind::BoolLit { value } => {
                let ty_bool = self.prog.type_bool();
                self.prog.check_type_match(expr, expect_ty, ty_bool)?;
                let cst = ir::Value::Const(ir::Const { ty: ty_bool, value: *value as i32 });
                (flow, LRValue::Right(cst))
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
                let cst = ir::Value::Const(ir::Const { ty, value });

                (flow, LRValue::Right(cst))
            }
            ast::ExpressionKind::StringLit { .. } => {
                panic!("string literals only supported in consts for now")
            }
            ast::ExpressionKind::Path(path) => {
                let value = match &*path.parents {
                    [] => *scope.find(&path.id)?,
                    [module] => *self.find_module(module)?.scope.find(&path.id)?,
                    _ => panic!("Only paths with depth 1 allowed for now")
                };
                self.prog.check_type_match(expr, expect_ty, self.prog.type_of_lrvalue(value))?;
                (flow, value)
            }
            ast::ExpressionKind::Ternary { condition, then_value, else_value } => {
                //TODO remove this once there is better type inference
                let expect_ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;

                let result_slot = self.define_slot(expect_ty);
                let (after_cond, cond) =
                    self.append_expr_loaded(flow, scope, condition, Some(self.prog.type_bool()))?;

                //TODO is it possible to do append_expr here instead? is an LValue ternary operator useful?
                //  and how does this interact with LRValue? we need to propagate the LR-ness
                //  eg (c ? a : b)[6] = 3
                let end_start = self.append_if(
                    after_cond,
                    cond,
                    //TODO any way to remove this code duplication?
                    |s: &mut Self, then_start: Flow| {
                        let (then_end, then_value) =
                            s.append_expr_loaded(then_start, scope, then_value, Some(expect_ty))?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: then_value };
                        s.append_instr(then_end.block, store);

                        Ok(then_end)
                    },
                    |s: &mut Self, else_start: Flow| {
                        let (else_end, else_value) =
                            s.append_expr_loaded(else_start, scope, else_value, Some(expect_ty))?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: else_value };
                        s.append_instr(else_end.block, store);

                        Ok(else_end)
                    },
                )?;

                let load = ir::InstructionInfo::Load { addr: ir::Value::Slot(result_slot) };
                let load = self.append_instr(end_start.block, load);
                let result_value = ir::Value::Instr(load);

                (end_start, LRValue::Right(result_value))
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let expect_ty = match kind {
                    ast::BinaryOp::Add | ast::BinaryOp::Sub | ast::BinaryOp::Mul |
                    ast::BinaryOp::Div | ast::BinaryOp::Mod => {
                        expect_ty
                    }
                    ast::BinaryOp::Eq | ast::BinaryOp::Neq |
                    ast::BinaryOp::Gte | ast::BinaryOp::Gt |
                    ast::BinaryOp::Lte | ast::BinaryOp::Lt => {
                        self.prog.check_type_match(expr, expect_ty, self.prog.type_bool())?;
                        None
                    }
                };

                let (after_left, ir_left) = self.append_expr_loaded(flow, scope, left, expect_ty)?;
                self.prog.check_integer_type(left, self.prog.type_of_value(ir_left))?;

                //use the left type for both inference and correctness checking
                let expect_ty = self.prog.type_of_value(ir_left);
                let (after_right, ir_right) = self.append_expr_loaded(after_left, scope, right, Some(expect_ty))?;

                let instr = binary_op_to_instr(*kind, ir_left, ir_right);
                let instr = self.append_instr(after_right.block, instr);

                (after_right, LRValue::Right(ir::Value::Instr(instr)))
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

                        let (flow, inner) = self.append_expr(flow, scope, inner, expect_ty_inner)?;
                        let inner = match inner {
                            //ref turns an lvalue into an rvalue
                            LRValue::Left(inner) => LRValue::Right(inner),
                            LRValue::Right(_) => return Err(Error::ReferenceOfLValue(expr.span)),
                        };

                        (flow, inner)
                    }
                    ast::UnaryOp::Deref => {
                        let expect_ty_inner = expect_ty.map(|ty| self.prog.define_type_ptr(ty));

                        //load to get the value and wrap as lvalue again
                        let (after_value, value) = self.append_expr_loaded(flow, scope, inner, expect_ty_inner)?;
                        (after_value, LRValue::Left(value))
                    }
                    ast::UnaryOp::Neg => {
                        let (after_inner, inner) = self.append_expr_loaded(flow, scope, inner, expect_ty)?;
                        let ty = self.prog.type_of_value(inner);
                        self.prog.check_integer_type(expr, ty)?;

                        let instr = self.append_instr(after_inner.block, ir::InstructionInfo::Arithmetic {
                            kind: ir::ArithmeticOp::Sub,
                            left: ir::Value::Const(ir::Const::new(ty, 0)),
                            right: inner,
                        });

                        (after_inner, LRValue::Right(ir::Value::Instr(instr)))
                    }
                }
            }
            ast::ExpressionKind::Call { target, args } => {
                let (after_target, target) = self.append_expr_loaded(flow, scope, target, None)?;

                //check that the target is a function
                let target_ty = self.prog.type_of_value(target);
                let target_ty = self.prog.get_type(target_ty).unwrap_func()
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
                    });
                }

                //append arg expressions and typecheck them
                let target_param_types = target_ty.params.clone();
                let mut ir_args = Vec::with_capacity(args.len());

                let after_args = args.iter().enumerate().try_fold(after_target, |flow, (i, arg)| {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, arg, Some(target_param_types[i]))?;
                    ir_args.push(value);
                    Ok(after_value)
                })?;

                let call = ir::InstructionInfo::Call {
                    target,
                    args: ir_args,
                };

                let call = self.append_instr(after_args.block, call);
                (after_args, LRValue::Right(ir::Value::Instr(call)))
            }
            ast::ExpressionKind::DotIndex { target, index } => {
                //TODO typechecking?
                //TODO proper errors
                //TODO allow reference to struct too?

                let (after_target, target) = self.append_expr(flow, scope, target, None)?;
                let struct_ty = self.prog.get_type(self.prog.type_of_lrvalue(target)).unwrap_tuple()
                    .expect("dot indexing only works on structs");

                match target {
                    LRValue::Left(target) => {
                        //TODO we need to know the ast struct type here, but we only get the ir type
                        let index = index.parse::<usize>().unwrap();

                        let result_inner_ty = struct_ty.fields[index];
                        let result_ty = self.prog.define_type_ptr(result_inner_ty);

                        let struct_sub_ptr = ir::InstructionInfo::StructSubPtr { base: target, index, result_ty };
                        let struct_sub_ptr = self.append_instr(after_target.block, struct_sub_ptr);

                        (after_target, LRValue::Left(ir::Value::Instr(struct_sub_ptr)))
                    }
                    LRValue::Right(_) => {
                        panic!("dot indexing only works for LValues")
                    }
                }
            }
            ast::ExpressionKind::Return { value } => {
                let ret_ty = self.prog.get_func(self.curr_func).func_ty.ret;

                let (after_value, value) = if let Some(value) = value {
                    self.append_expr_loaded(flow, scope, value, Some(ret_ty))?
                } else {
                    //check that function return type is indeed void
                    let void = self.prog.type_void();
                    self.prog.check_type_match(expr, Some(ret_ty), void)?;
                    (flow, ir::Value::Undef(void))
                };

                let ret = ir::Terminator::Return { value };
                self.prog.get_block_mut(after_value.block).terminator = ret;

                //start block and return undef so we can continue generating (and checking!) code
                let next_flow = self.new_flow(false);

                let ty = expect_ty.unwrap_or(self.prog.type_void());
                let undef = ir::Value::Undef(self.prog.define_type_ptr(ty));

                (next_flow, LRValue::Left(undef))
            }
            ast::ExpressionKind::Continue =>
                self.append_break_or_continue(flow, expr, expect_ty, ContinueOrBreak::Continue)?,
            ast::ExpressionKind::Break =>
                self.append_break_or_continue(flow, expr, expect_ty, ContinueOrBreak::Break)?,
        };

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let ty = self.prog.type_of_lrvalue(result.1);
            self.prog.check_type_match(expr, expect_ty, ty).expect("bug in lower")
        }

        Ok(result)
    }

    fn append_break_or_continue(
        &mut self,
        flow: Flow,
        expr: &'a ast::Expression,
        expect_ty: Option<ir::Type>,
        kind: ContinueOrBreak,
    ) -> Result<'a, (Flow, LRValue)> {
        let loop_info = self.loop_stack.last_mut()
            .ok_or(Error::NotInLoop { expr })?;

        let target = match kind {
            ContinueOrBreak::Continue => {
                loop_info.cond
            }
            ContinueOrBreak::Break => {
                loop_info.end_needs_return |= flow.needs_return;
                loop_info.end
            }
        };

        let jump_cond = ir::Terminator::Jump { target: new_target(target) };
        self.prog.get_block_mut(flow.block).terminator = jump_cond;

        let next_flow = self.new_flow(false);

        let ty = expect_ty.unwrap_or(self.prog.type_void());
        let undef = ir::Value::Undef(self.prog.define_type_ptr(ty));

        Ok((next_flow, LRValue::Left(undef)))
    }

    fn append_expr_loaded(
        &mut self,
        flow: Flow,
        scope: &Scope<LRValue>,
        expr: &'a ast::Expression,
        expect_ty: Option<ir::Type>,
    ) -> Result<'a, (Flow, ir::Value)> {
        let (after_value, value) = self.append_expr(flow, scope, expr, expect_ty)?;
        let loaded_value = self.append_load(after_value.block, value);

        Ok((after_value, loaded_value))
    }

    fn append_loop<
        C: FnOnce(&mut Self, Flow) -> Result<'a, (Flow, ir::Value)>,
        B: FnOnce(&mut Self, Flow) -> Result<'a, Flow>
    >(&mut self, flow: Flow, cond: C, body: B) -> Result<'a, Flow> {
        //condition
        let cond_start = self.new_flow(flow.needs_return);
        let cond_start_block = cond_start.block;
        let (cond_end, cond) = cond(self, cond_start)?;

        //end
        //needs_return will be set incrementally by all blocks that jump to end
        let mut end_start = self.new_flow(false);

        let loop_info = LoopInfo {
            cond: cond_start_block,
            end: end_start.block,
            end_needs_return: false,
        };
        self.loop_stack.push(loop_info);

        //body
        let body_start = self.new_flow(cond_end.needs_return);
        let body_start_block = body_start.block;
        let body_end = body(self, body_start)?;

        let loop_info = self.loop_stack.pop().unwrap();
        end_start.needs_return |= loop_info.end_needs_return;

        //connect everything
        let branch = new_branch(cond, body_start_block, end_start.block);
        end_start.needs_return |= cond_end.needs_return;
        let jump_cond = ir::Terminator::Jump { target: new_target(cond_start_block) };

        self.prog.get_block_mut(flow.block).terminator = jump_cond.clone();
        self.prog.get_block_mut(cond_end.block).terminator = branch;
        self.prog.get_block_mut(body_end.block).terminator = jump_cond;

        //continue withing code to end
        Ok(end_start)
    }

    fn append_statement(&mut self, flow: Flow, scope: &mut Scope<LRValue>, stmt: &'a ast::Statement) -> Result<'a, Flow> {
        match &stmt.kind {
            ast::StatementKind::Declaration(decl) => {
                assert!(!decl.mutable, "everything is mutable for now");
                let expect_ty = decl.ty.as_ref()
                    .map(|ty| self.parse_type(ty))
                    .transpose()?;

                let (after_value, value) = if let Some(init) = &decl.init {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, &init, expect_ty)?;
                    (after_value, Some(value))
                } else {
                    (flow, None)
                };

                //figure out the type
                let value_ty = value.map(|v| self.prog.type_of_value(v));
                let ty = expect_ty.or(value_ty).ok_or(Error::CannotInferType(decl.span))?;

                //define the slot
                let slot = self.define_slot(ty);
                scope.declare(&decl.id, LRValue::Left(ir::Value::Slot(slot)))?;

                //optionally store the value
                if let Some(value) = value {
                    let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value };
                    self.append_instr(after_value.block, store);
                }

                Ok(after_value)
            }
            ast::StatementKind::Assignment(assign) => {
                let (after_addr, addr) = self.append_expr(flow, scope, &assign.left, None)?;
                let ty = self.prog.type_of_lrvalue(addr);

                let (after_value, value) = self.append_expr_loaded(after_addr, scope, &assign.right, Some(ty))?;
                self.append_store(after_value.block, assign.span, addr, value)?;

                Ok(after_value)
            }
            ast::StatementKind::If(if_stmt) => {
                let (cond_end, cond) =
                    self.append_expr_loaded(flow, scope, &if_stmt.cond, Some(self.prog.type_bool()))?;

                self.append_if(
                    cond_end,
                    cond,
                    |s: &mut Self, then_flow: Flow| {
                        s.append_nested_block(then_flow, scope, &if_stmt.then_block)
                    },
                    |s: &mut Self, else_flow: Flow| {
                        if let Some(else_block) = &if_stmt.else_block {
                            s.append_nested_block(else_flow, scope, else_block)
                        } else {
                            Ok(else_flow)
                        }
                    },
                )
            }
            ast::StatementKind::While(while_stmt) => {
                self.append_loop(
                    flow,
                    |s: &mut Self, cond_start: Flow| {
                        s.append_expr_loaded(cond_start, scope, &while_stmt.cond, Some(s.prog.type_bool()))
                    },
                    |s: &mut Self, body_start: Flow| {
                        s.append_nested_block(body_start, scope, &while_stmt.body)
                    },
                )
            }
            ast::StatementKind::For(for_stmt) => {
                //figure out the index type
                let index_ty = for_stmt.index_ty.as_ref()
                    .map(|var_ty| self.parse_type(var_ty))
                    .transpose()?;
                if let Some(index_ty) = index_ty {
                    self.prog.check_integer_type(&for_stmt.start, index_ty)?;
                }

                //evaluate the range
                let (flow, start_value) = self.append_expr_loaded(flow, scope, &for_stmt.start, index_ty)?;
                let index_ty = self.prog.type_of_value(start_value);
                self.prog.check_integer_type(&for_stmt.start, index_ty)?;
                let (flow, end_value) = self.append_expr_loaded(flow, scope, &for_stmt.end, Some(index_ty))?;

                //declare slot for index
                let mut index_scope = scope.nest();
                let index_slot = self.define_slot(index_ty);
                //TODO this allows the index to be mutated, which is fine for now, but it should be marked immutable when that is implemented
                //TODO maybe consider changing the increment to use the index loaded at the beginning so it can't really be mutated after all
                index_scope.declare(&for_stmt.index, LRValue::Left(ir::Value::Slot(index_slot)))?;

                //index = start
                self.append_instr(flow.block, ir::InstructionInfo::Store { addr: ir::Value::Slot(index_slot), value: start_value });

                //index < end
                let cond = |s: &mut Self, cond_start: Flow| {
                    let load = s.append_instr(cond_start.block, ir::InstructionInfo::Load {
                        addr: ir::Value::Slot(index_slot),
                    });
                    let cond = s.append_instr(cond_start.block, ir::InstructionInfo::Comparison {
                        kind: ir::LogicalOp::Lt,
                        left: ir::Value::Instr(load),
                        right: end_value,
                    });

                    Ok((cond_start, ir::Value::Instr(cond)))
                };

                //body; index = index + 1
                let body = |s: &mut Self, body_start: Flow| {
                    let body_end = s.append_nested_block(body_start, &index_scope, &for_stmt.body)?;

                    let load = s.append_instr(body_end.block, ir::InstructionInfo::Load {
                        addr: ir::Value::Slot(index_slot),
                    });
                    let inc = s.append_instr(body_end.block, ir::InstructionInfo::Arithmetic {
                        kind: ir::ArithmeticOp::Add,
                        left: ir::Value::Instr(load),
                        right: ir::Value::Const(ir::Const { ty: index_ty, value: 1 }),
                    });
                    s.append_instr(body_end.block, ir::InstructionInfo::Store {
                        addr: ir::Value::Slot(index_slot),
                        value: ir::Value::Instr(inc),
                    });

                    Ok(body_end)
                };

                self.append_loop(flow, cond, body)
            }
            ast::StatementKind::Block(block) => {
                self.append_nested_block(flow, scope, block)
            }
            ast::StatementKind::Expression(expr) => {
                let (after_value, _) = self.append_expr(flow, scope, expr, None)?;
                Ok(after_value)
            }
        }
    }

    fn append_nested_block(&mut self, flow: Flow, scope: &Scope<LRValue>, block: &'a ast::Block) -> Result<'a, Flow> {
        let mut inner_scope = scope.nest();

        block.statements.iter()
            .try_fold(flow, |flow, stmt| {
                self.append_statement(flow, &mut inner_scope, stmt)
            })
    }

    pub fn append_func(&mut self, ast_func: &'a ast::Function, ir_func: ir::Function) -> Result<'a, ()> {
        self.curr_func = ir_func;

        let ret_ty = self.prog.get_func(ir_func).func_ty.ret;

        let start = self.new_flow(true);
        self.prog.get_func_mut(ir_func).entry = start.block;

        let mut scope = self.module_skeleton.scope.nest();

        for (i, param) in ast_func.params.iter().enumerate() {
            let ir_param = self.prog.get_func(ir_func).params[i];

            //allocate a slot for the parameter so its address can be taken
            let slot = self.define_slot(self.prog.get_param(ir_param).ty);

            //immediately copy the param into the slot
            self.append_instr(start.block, ir::InstructionInfo::Store {
                addr: ir::Value::Slot(slot),
                value: ir::Value::Param(ir_param),
            });

            scope.declare(&param.id, LRValue::Left(ir::Value::Slot(slot)))?;
        }

        let body = ast_func.body.as_ref().
            expect("can only generate code for functions with a body");
        let end = self.append_nested_block(start, &mut scope, body)?;

        if end.needs_return {
            if ret_ty == self.prog.type_void() {
                //automatically insert return
                let ret = ir::Terminator::Return { value: ir::Value::Undef(self.prog.type_void()) };
                self.prog.get_block_mut(end.block).terminator = ret;
            } else {
                return Err(Error::MissingReturn(ast_func));
            }
        }

        Ok(())
    }
}

/*
#[derive(Debug)]
struct DeclaredStruct<'a> {
    ty: ir::Type,
    field_names: Vec<&'a str>,
}

#[derive(Debug, Default)]
struct ModuleSkeleton<'a> {
    scope: Scope<'static, LRValue>,
    used_modules: HashSet<&'a str>,
    declared_structs: HashMap<&'a str, DeclaredStruct<'a>>,
    functions_to_lower: Vec<(&'a ast::Function, ir::Function)>,
}

impl<'a> ModuleSkeleton<'a> {
    ///parse basic types and types that are already declared in this module
    ///this is temporary and will be replaced by something that supports reordering
    fn parse_local_type<'ta>(&self, prog: &mut ir::Program, ty: &'ta ast::Type) -> Result<'ta, ir::Type> {
        match &ty.kind {
            ast::TypeKind::Path(path) => {
                match &*path.parents {
                    [] => {
                        match &*path.id.string {
                            "int" => Ok(prog.define_type_int(32)),
                            "bool" => Ok(prog.type_bool()),
                            "void" => Ok(prog.type_void()),
                            "byte" => Ok(prog.define_type_int(8)),
                            string => {
                                let declared_struct = self.declared_structs.get(string)
                                    .ok_or(Error::UndeclaredIdentifier(&path.id))?;
                                Ok(declared_struct.ty)
                            }
                        }
                    }
                    _ => {
                        //error here
                        panic!("Path types not supported yet here")
                    }
                }
            }
            ast::TypeKind::Ref(inner) => {
                let inner = self.parse_local_type(prog, inner)?;
                Ok(prog.define_type_ptr(inner))
            }
            ast::TypeKind::Func { params, ret } => {
                let params = params.iter()
                    .map(|p| self.parse_local_type(prog, p))
                    .collect::<Result<_>>()?;
                let ret = self.parse_local_type(prog, ret)?;
                Ok(prog.define_type_func(ir::FunctionType { params, ret }))
            }
            ast::TypeKind::Tuple { fields } => {
                let tuple_type = ir::TupleType {
                    fields: fields.iter()
                        .map(|field| self.parse_local_type(prog, field))
                        .collect::<Result<_>>()?
                };
                Ok(prog.define_type_tuple(tuple_type))
            }
        }
    }
}

fn build_module_skeleton<'a>(
    prog: &mut ir::Program,
    module: &'a ast::Module,
    is_root: bool,
    all_modules: &IndexMap<String, ast::Module>,
) -> Result<'a, ModuleSkeleton<'a>> {
    let mut skeleton = ModuleSkeleton::default();

    for item in &module.items {
        match item {
            ast::Item::UseDecl(decl) => {
                if !all_modules.contains_key(&*decl.module.string) {
                    return Err(Error::ModuleNotFound { module: &decl.module });
                }

                skeleton.used_modules.insert(&decl.module.string);
            }
            ast::Item::Struct(ast_struct) => {
                if skeleton.declared_structs.contains_key(&*ast_struct.id.string) {
                    return Err(Error::IdentifierDeclaredTwice(&ast_struct.id));
                } else {
                    let field_tys = ast_struct.fields.iter()
                        .map(|field| skeleton.parse_local_type(prog, &field.ty))
                        .collect::<Result<_>>()?;
                    let tuple_ty = prog.define_type_tuple(ir::TupleType { fields: field_tys });
                    let declared_struct = DeclaredStruct {
                        ty: tuple_ty,
                        field_names: ast_struct.fields.iter()
                            .map(|field| field.id.string.as_ref())
                            .collect(),
                    };

                    skeleton.declared_structs.insert(&*ast_struct.id.string, declared_struct);
                }
            }
            ast::Item::Function(ast_func) => {
                let ret_ty = ast_func.ret_ty.as_ref()
                    .map_or(Ok(prog.type_void()), |t| skeleton.parse_local_type(prog, t))?;

                let param_tys = ast_func.params.iter()
                    .map(|param| skeleton.parse_local_type(prog, &param.ty))
                    .collect::<Result<_>>()?;
                let func_ty = ir::FunctionType { params: param_tys, ret: ret_ty };

                let value = match (ast_func.ext, &ast_func.body) {
                    //external function, leave this for the backend to figure out
                    (true, None) => {
                        let func_ty = prog.define_type_func(func_ty);
                        let ir_ext = ir::ExternInfo { name: ast_func.id.string.clone(), ty: func_ty };
                        let ir_ext = prog.define_ext(ir_ext);
                        ir::Value::Extern(ir_ext)
                    }
                    //functions need bodies
                    (false, None) => {
                        return Err(Error::MissingFunctionBody(ast_func));
                    }
                    //standard function, maybe marked extern
                    (ext, Some(_)) => {
                        let mut ir_func = ir::FunctionInfo::new(func_ty, prog);
                        if ext {
                            ir_func.global_name = Some(ast_func.id.string.clone());
                        }

                        //add the parameters
                        ir_func.params.extend(
                            ir_func.func_ty.params.iter()
                                .map(|&ty| prog.define_param(ir::ParameterInfo { ty }))
                        );

                        //define and register the function
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
                                });
                            }

                            prog.main = ir_func;
                        }
                        func_value
                    }
                };

                skeleton.scope.declare(&ast_func.id, LRValue::Right(value))?;
            }
            ast::Item::Const(decl) => {
                let ty = decl.ty.as_ref().map(|ty| skeleton.parse_local_type(prog, ty)).transpose()?;
                let init = decl.init.as_ref().expect("consts need initialized for now");

                let value = match &init.kind {
                    ast::ExpressionKind::StringLit { value } => {
                        let ty_byte = prog.define_type_int(8);
                        let ty_byte_ptr = prog.define_type_ptr(ty_byte);
                        prog.check_type_match(&init, ty, ty_byte_ptr)?;

                        let data = prog.define_data(ir::DataInfo {
                            ty: ty_byte_ptr,
                            bytes: value.clone().into_bytes(),
                        });

                        LRValue::Right(ir::Value::Data(data))
                    }
                    ast::ExpressionKind::BoolLit { value } => {
                        let ty_bool = prog.type_bool();
                        prog.check_type_match(init, ty, ty_bool)?;
                        LRValue::Right(ir::Value::Const(ir::Const { ty: ty_bool, value: *value as i32 }))
                    }
                    ast::ExpressionKind::IntLit { value } => {
                        let ty = ty.ok_or(Error::CannotInferType(init.span))?;
                        prog.get_type(ty).unwrap_int()
                            .ok_or(Error::ExpectIntegerType {
                                expression: init,
                                actual: prog.format_type(ty).to_string(),
                            })?;

                        let value = value.parse::<i32>()
                            .map_err(|_| Error::InvalidLiteral {
                                span: init.span,
                                lit: value.clone(),
                                ty: prog.format_type(ty).to_string(),
                            })?;

                        LRValue::Right(ir::Value::Const(ir::Const { ty, value }))
                    }
                    kind => {
                        panic!("This kind of const initializer is not supported for now: {:?}", kind)
                    }
                };

                skeleton.scope.declare(&decl.id, value)?;
            }
        }
    }

    Ok(skeleton)
}

pub fn lower(ast_prog: &ast::Program) -> Result<ir::Program> {
    let mut prog = ir::Program::new();

    //keep these as placeholders
    let tmp_func = prog.main;

    //build skeletons
    let mut modules: IndexMap<&str, ModuleSkeleton> = IndexMap::new();

    for (module_name, ast_module) in &ast_prog.modules {
        let is_root = module_name == "";
        let module_skeleton = build_module_skeleton(&mut prog, ast_module, is_root, &ast_prog.modules)?;

        modules.insert(module_name, module_skeleton);
    }

    //actually generate code
    for (_, module_skeleton) in &modules {
        let mut lower = LowerState {
            prog: &mut prog,
            module_skeleton,
            modules: &modules,
            curr_func: tmp_func,
            loop_stack: Vec::new(),
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

*/