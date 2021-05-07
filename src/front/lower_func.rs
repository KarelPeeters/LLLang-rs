use std::collections::HashMap;

use crate::front::{ast, cst};
use crate::front::cst::{ItemStore, ScopedItem, ScopedValue, ScopeKind, TypeInfo};
use crate::front::error::{Error, Result};
use crate::front::lower::{LRValue, MappingTypeStore, TypedValue};
use crate::front::scope::Scope;
use crate::front::type_solver::{TypeSolution, TypeVar};
use crate::mid::ir;

/// The state necessary to lower a single function.
pub struct LowerFuncState<'ir, 'ast, 'cst, 'ts, F: Fn(ScopedValue) -> LRValue> {
    pub prog: &'ir mut ir::Program,

    pub items: &'cst ItemStore<'ast>,
    pub types: &'cst mut MappingTypeStore<'ast>,
    pub map_value: F,

    pub module_scope: &'cst Scope<'static, ScopedItem>,

    pub ir_func: ir::Function,
    pub ret_ty: cst::Type,

    pub expr_type_map: &'ts HashMap<*const ast::Expression, TypeVar>,
    pub decl_type_map: &'ts HashMap<*const ast::Declaration, TypeVar>,
    pub type_solution: TypeSolution,

    pub loop_stack: Vec<LoopInfo>,
}

/// Information about the innermost loop, used for `break` and `continue` statements.
pub struct LoopInfo {
    cond: ir::Block,
    end: ir::Block,
    end_needs_return: bool,
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

/// Represents a point in the program where more code can be appended to. This type intentionally
/// doesn't implement Copy so it's easy to spot when it is accidentally used twice.
struct Flow {
    block: ir::Block,
    needs_return: bool,
}

impl<'ir, 'ast, 'cst, 'ts, F: Fn(ScopedValue) -> LRValue> LowerFuncState<'ir, 'ast, 'cst, 'ts, F> {
    fn expr_type(&self, expr: &ast::Expression) -> cst::Type {
        self.type_solution[*self.expr_type_map.get(&(expr as *const _)).unwrap()]
    }

    #[must_use]
    fn new_flow(&mut self, needs_return: bool) -> Flow {
        Flow {
            block: self.prog.define_block(ir::BlockInfo::new()),
            needs_return,
        }
    }

    #[must_use]
    fn define_slot(&mut self, inner_ty: ir::Type) -> ir::StackSlot {
        let slot = ir::StackSlotInfo { inner_ty };
        let slot = self.prog.define_slot(slot);
        self.prog.get_func_mut(self.ir_func).slots.push(slot);
        slot
    }

    fn append_instr(&mut self, block: ir::Block, instr: ir::InstructionInfo) -> ir::Instruction {
        let instr = self.prog.define_instr(instr);
        self.prog.get_block_mut(block).instructions.push(instr);
        instr
    }

    #[must_use]
    fn append_load(&mut self, block: ir::Block, value: LRValue) -> TypedValue {
        match value {
            LRValue::Left(value) => {
                let inner_ty = self.types[value.ty].unwrap_ptr()
                    .expect("Left should have pointer type");
                let inner_ty_ir = self.types.map_type(self.prog, inner_ty);

                let load_instr = ir::InstructionInfo::Load { ty: inner_ty_ir, addr: value.ir };
                let load_instr = self.append_instr(block, load_instr);

                TypedValue { ty: inner_ty, ir: ir::Value::Instr(load_instr) }
            }
            LRValue::Right(value) =>
                value,
        }
    }

    //Return the "never" value returned by expressions like break, continue and return
    #[must_use]
    fn never_value(&mut self, ty: cst::Type) -> LRValue {
        //TODO replace this with actual "never" value
        let ty_ptr = self.types.define_type_ptr(ty);
        let ty_ptr_ir = self.types.map_type(self.prog, ty_ptr);

        LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Undef(ty_ptr_ir) })
    }

    fn append_if<
        T: FnOnce(&mut Self, Flow) -> Result<'ast, Flow>,
        E: FnOnce(&mut Self, Flow) -> Result<'ast, Flow>
    >(&mut self, flow: Flow, cond: ir::Value, then_func: T, else_func: E) -> Result<'ast, Flow> {
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
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, (Flow, LRValue)> {
        let result: (Flow, LRValue) = match &expr.kind {
            ast::ExpressionKind::Null => {
                let ty = self.expr_type(expr);
                let ir_ty = self.types.map_type(self.prog, ty);

                let cst = ir::Value::Const(ir::Const { ty: ir_ty, value: 0 });
                (flow, LRValue::Right(TypedValue { ty, ir: cst }))
            }
            ast::ExpressionKind::BoolLit { value } => {
                let ty_bool = self.types.type_bool();
                let ty_bool_ir = self.prog.ty_bool();

                let cst = ir::Value::Const(ir::Const { ty: ty_bool_ir, value: *value as i32 });
                (flow, LRValue::Right(TypedValue { ty: ty_bool, ir: cst }))
            }
            ast::ExpressionKind::IntLit { value } => {
                let ty = self.expr_type(expr);

                let size_in_bits = match self.types[ty] {
                    TypeInfo::Byte => Ok(8),
                    TypeInfo::Int => Ok(32),
                    _ => Err(Error::ExpectIntegerType {
                        expression: expr,
                        actual: self.types.format_type(ty).to_string(),
                    }),
                }?;

                let ty_ir = self.prog.define_type_int(size_in_bits);

                //TODO this is not correct, what about negative values? also disallow byte overflow
                let value = value.parse::<i32>()
                    .map_err(|_| Error::InvalidLiteral {
                        span: expr.span,
                        lit: value.clone(),
                        ty: self.types.format_type(ty).to_string(),
                    })?;

                let cst = ir::Value::Const(ir::Const { ty: ty_ir, value });

                (flow, LRValue::Right(TypedValue { ty, ir: cst }))
            }
            ast::ExpressionKind::StringLit { value } => {
                let ty_byte = self.types.type_byte();
                let ty_byte_ptr = self.types.define_type_ptr(ty_byte);

                let data = ir::DataInfo {
                    ty: self.types.map_type(self.prog, ty_byte_ptr),
                    inner_ty: self.types.map_type(self.prog, ty_byte),
                    bytes: value.bytes().collect(),
                };
                let data = self.prog.define_data(data);
                let data = ir::Value::Data(data);

                (flow, LRValue::Right(TypedValue { ty: ty_byte_ptr, ir: data }))
            }
            ast::ExpressionKind::Path(path) => {
                let item = self.items.resolve_path(ScopeKind::Real, scope, path)?;

                let value = if let ScopedItem::Value(value) = item {
                    (self.map_value)(value)
                } else {
                    unreachable!()
                };

                (flow, value)
            }
            ast::ExpressionKind::Ternary { condition, then_value, else_value } => {
                let ty = self.expr_type(expr);
                let ty_ir = self.types.map_type(self.prog, ty);

                let result_slot = self.define_slot(ty_ir);
                let (after_cond, cond) =
                    self.append_expr_loaded(flow, scope, condition)?;

                //TODO is it possible to do append_expr here instead? is an LValue ternary operator useful?
                //  and how does this interact with LRValue? we need to propagate the LR-ness
                //  eg (c ? a : b)[6] = 3
                let end_start = self.append_if(
                    after_cond,
                    cond.ir,
                    //TODO any way to remove this code duplication?
                    |s: &mut Self, then_start: Flow| {
                        let (then_end, then_value) =
                            s.append_expr_loaded(then_start, scope, then_value)?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: then_value.ir };
                        s.append_instr(then_end.block, store);

                        Ok(then_end)
                    },
                    |s: &mut Self, else_start: Flow| {
                        let (else_end, else_value) =
                            s.append_expr_loaded(else_start, scope, else_value)?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: else_value.ir };
                        s.append_instr(else_end.block, store);

                        Ok(else_end)
                    },
                )?;

                let load = ir::InstructionInfo::Load { ty: ty_ir, addr: ir::Value::Slot(result_slot) };
                let load = self.append_instr(end_start.block, load);
                let result_value = ir::Value::Instr(load);

                (end_start, LRValue::Right(TypedValue { ty, ir: result_value }))
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let (after_left, value_left) =
                    self.append_expr_loaded(flow, scope, left)?;
                let (after_right, value_right) =
                    self.append_expr_loaded(after_left, scope, right)?;

                let instr = binary_op_to_instr(*kind, value_left.ir, value_right.ir);
                let instr = self.append_instr(after_right.block, instr);

                let result_ty = self.expr_type(expr);
                (after_right, LRValue::Right(TypedValue { ty: result_ty, ir: ir::Value::Instr(instr) }))
            }
            ast::ExpressionKind::Unary { kind, inner } => {
                match kind {
                    ast::UnaryOp::Ref => {
                        let (flow, inner) =
                            self.append_expr(flow, scope, inner)?;
                        let inner = match inner {
                            //ref turns an lvalue into an rvalue
                            LRValue::Left(inner) => LRValue::Right(inner),
                            //we could create a temporary slot and return a reference to that, but that gets confusing
                            LRValue::Right(_) => return Err(Error::ReferenceOfRValue(expr)),
                        };

                        (flow, inner)
                    }
                    ast::UnaryOp::Deref => {
                        //load to get the value and wrap as lvalue again
                        let (after_value, value) =
                            self.append_expr_loaded(flow, scope, inner)?;
                        (after_value, LRValue::Left(value))
                    }
                    ast::UnaryOp::Neg => {
                        let (after_inner, inner) =
                            self.append_expr_loaded(flow, scope, inner)?;
                        let ty = inner.ty;
                        let ty_ir = self.types.map_type(self.prog, ty);

                        let instr = self.append_instr(after_inner.block, ir::InstructionInfo::Arithmetic {
                            kind: ir::ArithmeticOp::Sub,
                            left: ir::Value::Const(ir::Const::new(ty_ir, 0)),
                            right: inner.ir,
                        });

                        (after_inner, LRValue::Right(TypedValue { ty, ir: ir::Value::Instr(instr) }))
                    }
                }
            }
            ast::ExpressionKind::Call { target, args } => {
                //evaluate target
                let (after_target, target_value) = self.append_expr_loaded(flow, scope, target)?;
                let ret_ty = self.types[target_value.ty].unwrap_func().unwrap().ret;

                // evaluate args
                let mut ir_args = Vec::with_capacity(args.len());
                let after_args = args.iter().try_fold(after_target, |flow, arg| {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, arg)?;
                    ir_args.push(value.ir);
                    Ok(after_value)
                })?;

                //actual call
                let call = ir::InstructionInfo::Call {
                    target: target_value.ir,
                    args: ir_args,
                };
                let call = self.append_instr(after_args.block, call);

                (after_args, LRValue::Right(TypedValue { ty: ret_ty, ir: ir::Value::Instr(call) }))
            }
            ast::ExpressionKind::DotIndex { target, index } => {
                //TODO currently we only allow LValue(&Struct),
                //  but we could add support for RValue(Struct) and RValue(&Struct) as well

                let (after_target, target_value) = self.append_expr_lvalue(flow, scope, target)?;
                let target_inner_ty = self.types[target_value.ty].unwrap_ptr().unwrap();

                let index = match (&self.types[target_inner_ty], index) {
                    (TypeInfo::Tuple(_), ast::DotIndexIndex::Tuple { index, .. }) => {
                        *index
                    }
                    (TypeInfo::Struct(target_ty_info), ast::DotIndexIndex::Struct(id)) => {
                        target_ty_info.find_field_index(&id.string)
                            .ok_or_else(|| Error::StructFieldNotFound {
                                target,
                                target_type: self.types.format_type(target_value.ty).to_string(),
                                index: id,
                            })?
                    }
                    (TypeInfo::Tuple(_), _) | (TypeInfo::Struct(_), _) => return Err(Error::WrongDotIndexType {
                        target,
                        target_type: self.types.format_type(target_value.ty).to_string(),
                        index,
                    }),
                    (_, _) => return Err(Error::ExpectStructOrTupleType {
                        expression: expr,
                        actual: self.types.format_type(target_value.ty).to_string(),
                    })
                };

                let tuple_ty = self.expr_type(target);
                let tuple_ty_ir = self.types.map_type(self.prog, tuple_ty);

                let result_ty = self.expr_type(expr);
                let result_ty_ptr = self.types.define_type_ptr(result_ty);

                let struct_sub_ptr = ir::InstructionInfo::TupleFieldPtr {
                    tuple_ty: tuple_ty_ir,
                    base: target_value.ir,
                    index,
                };
                let struct_sub_ptr = self.append_instr(after_target.block, struct_sub_ptr);

                (after_target, LRValue::Left(TypedValue { ty: result_ty_ptr, ir: ir::Value::Instr(struct_sub_ptr) }))
            }
            ast::ExpressionKind::ArrayIndex { target, index } => {
                let (after_target, target_value) = self.append_expr_lvalue(flow, scope, target)?;
                let (after_index, index) = self.append_expr_loaded(after_target, scope, index)?;

                let result_ty = self.expr_type(expr);
                let result_ty_ir = self.types.map_type(self.prog, result_ty);
                let result_ty_ptr = self.types.define_type_ptr(result_ty);

                let array_index_ptr = ir::InstructionInfo::PointerOffSet {
                    ty: result_ty_ir,
                    base: target_value.ir,
                    index: index.ir,
                };
                let array_index_ptr = self.append_instr(after_index.block, array_index_ptr);

                (after_index, LRValue::Left(TypedValue { ty: result_ty_ptr, ir: ir::Value::Instr(array_index_ptr) }))
            }
            ast::ExpressionKind::Return { value } => {
                let (after_value, value) = if let Some(value) = value {
                    self.append_expr_loaded(flow, scope, value)?
                } else {
                    //check that function return type is indeed void
                    let ty_void = self.types.type_void();
                    (flow, TypedValue { ty: ty_void, ir: ir::Value::Undef(self.prog.ty_ptr()) })
                };

                let ret = ir::Terminator::Return { value: value.ir };
                self.prog.get_block_mut(after_value.block).terminator = ret;

                //continue writing dead code
                (self.new_flow(false), self.never_value(self.expr_type(expr)))
            }
            ast::ExpressionKind::Continue =>
                self.append_break_or_continue(flow, expr, ContinueOrBreak::Continue)?,
            ast::ExpressionKind::Break =>
                self.append_break_or_continue(flow, expr, ContinueOrBreak::Break)?,
        };

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let expect_ty = self.expr_type(expr);
            let actual_ty = result.1.ty(&self.types);

            assert_eq!(
                expect_ty, actual_ty,
                "bug in lower, inferred type '{}' for expression but generated code returns '{}'",
                self.types.format_type(expect_ty), self.types.format_type(actual_ty)
            );
        }

        Ok(result)
    }

    fn append_break_or_continue(
        &mut self,
        flow: Flow,
        expr: &'ast ast::Expression,
        kind: ContinueOrBreak,
    ) -> Result<'ast, (Flow, LRValue)> {
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

        //continue writing dead code
        Ok((self.new_flow(false), self.never_value(self.expr_type(expr))))
    }

    fn append_expr_loaded(
        &mut self,
        flow: Flow,
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, (Flow, TypedValue)> {
        let (after_value, value) = self.append_expr(flow, scope, expr)?;
        let loaded_value = self.append_load(after_value.block, value);

        Ok((after_value, loaded_value))
    }

    fn append_expr_lvalue(
        &mut self,
        flow: Flow,
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, (Flow, TypedValue)> {
        let (after_value, value) = self.append_expr(flow, scope, expr)?;

        match value {
            LRValue::Left(value) => Ok((after_value, value)),
            LRValue::Right(_) => Err(Error::ExpectedLValue(expr)),
        }
    }

    fn append_loop<
        C: FnOnce(&mut Self, Flow) -> Result<'ast, (Flow, ir::Value)>,
        B: FnOnce(&mut Self, Flow) -> Result<'ast, Flow>
    >(&mut self, flow: Flow, cond: C, body: B) -> Result<'ast, Flow> {
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

    fn append_statement(&mut self, flow: Flow, scope: &mut Scope<ScopedItem>, stmt: &'ast ast::Statement) -> Result<'ast, Flow> {
        match &stmt.kind {
            ast::StatementKind::Declaration(decl) => {
                assert!(!decl.mutable, "everything is mutable for now");

                let (after_value, value) = if let Some(init) = &decl.init {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, &init)?;
                    (after_value, Some(value))
                } else {
                    (flow, None)
                };

                //construct the types
                let ty = self.type_solution[*self.decl_type_map.get(&(decl as *const _)).unwrap()];
                let ty_ptr = self.types.define_type_ptr(ty);
                let ty_ir = self.types.map_type(self.prog, ty);

                //define the slot
                let slot = self.define_slot(ty_ir);
                let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Slot(slot) });
                let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
                scope.maybe_declare(&decl.id, item)?;

                //optionally store the value
                if let Some(value) = value {
                    let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value: value.ir };
                    self.append_instr(after_value.block, store);
                }

                Ok(after_value)
            }
            ast::StatementKind::Assignment(assign) => {
                let (after_addr, addr) = self.append_expr_lvalue(flow, scope, &assign.left)?;
                let (after_value, value) =
                    self.append_expr_loaded(after_addr, scope, &assign.right)?;

                let store = ir::InstructionInfo::Store { addr: addr.ir, value: value.ir };
                self.append_instr(after_value.block, store);

                Ok(after_value)
            }
            ast::StatementKind::If(if_stmt) => {
                let (cond_end, cond) =
                    self.append_expr_loaded(flow, scope, &if_stmt.cond)?;

                self.append_if(
                    cond_end,
                    cond.ir,
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
                        let (flow, cond) =
                            s.append_expr_loaded(cond_start, scope, &while_stmt.cond)?;
                        Ok((flow, cond.ir))
                    },
                    |s: &mut Self, body_start: Flow| {
                        s.append_nested_block(body_start, scope, &while_stmt.body)
                    },
                )
            }
            ast::StatementKind::For(for_stmt) => {
                //figure out the index type
                let index_ty = self.expr_type(&for_stmt.start);
                let index_ty_ptr = self.types.define_type_ptr(index_ty);
                let index_ty_ir = self.types.map_type(self.prog, index_ty);

                //evaluate the range
                let (flow, start_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.start)?;
                let (flow, end_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.end)?;

                //declare slot for index
                let mut index_scope = scope.nest();
                let index_slot = self.define_slot(index_ty_ir);
                let index_slot = ir::Value::Slot(index_slot);

                //TODO this allows the index to be mutated, which is fine for now, but it should be marked immutable when that is implemented
                //TODO maybe consider changing the increment to use the index loaded at the beginning so it can't really be mutated after all
                let index_slot_value = LRValue::Left(TypedValue { ty: index_ty_ptr, ir: index_slot });
                let item = ScopedItem::Value(ScopedValue::Immediate(index_slot_value));
                index_scope.maybe_declare(&for_stmt.index, item)?;

                //index = start
                self.append_instr(flow.block, ir::InstructionInfo::Store { addr: index_slot, value: start_value.ir });

                //index < end
                let cond = |s: &mut Self, cond_start: Flow| {
                    let load = ir::InstructionInfo::Load { ty: index_ty_ir, addr: index_slot };
                    let load = s.append_instr(cond_start.block, load);

                    let cond = ir::InstructionInfo::Comparison {
                        kind: ir::LogicalOp::Lt,
                        left: ir::Value::Instr(load),
                        right: end_value.ir,
                    };
                    let cond = s.append_instr(cond_start.block, cond);

                    Ok((cond_start, ir::Value::Instr(cond)))
                };

                //body; index = index + 1
                let body = |s: &mut Self, body_start: Flow| {
                    let body_end = s.append_nested_block(body_start, &index_scope, &for_stmt.body)?;

                    let load = ir::InstructionInfo::Load { ty: index_ty_ir, addr: index_slot };
                    let load = s.append_instr(body_end.block, load);

                    let inc = ir::InstructionInfo::Arithmetic {
                        kind: ir::ArithmeticOp::Add,
                        left: ir::Value::Instr(load),
                        right: ir::Value::Const(ir::Const { ty: index_ty_ir, value: 1 }),
                    };
                    let inc = s.append_instr(body_end.block, inc);

                    let store = ir::InstructionInfo::Store {
                        addr: index_slot,
                        value: ir::Value::Instr(inc),
                    };
                    s.append_instr(body_end.block, store);

                    Ok(body_end)
                };

                self.append_loop(flow, cond, body)
            }
            ast::StatementKind::Block(block) => {
                self.append_nested_block(flow, scope, block)
            }
            ast::StatementKind::Expression(expr) => {
                let (after_value, _) = self.append_expr(flow, scope, expr)?;
                Ok(after_value)
            }
        }
    }

    fn append_nested_block(&mut self, flow: Flow, scope: &Scope<ScopedItem>, block: &'ast ast::Block) -> Result<'ast, Flow> {
        let mut inner_scope = scope.nest();

        block.statements.iter()
            .try_fold(flow, |flow, stmt| {
                self.append_statement(flow, &mut inner_scope, stmt)
            })
    }

    pub fn lower_func(&mut self, decl: &'cst cst::FunctionDecl<'ast>) -> Result<'ast, ()> {
        let start = self.new_flow(true);
        self.prog.get_func_mut(self.ir_func).entry = ir::Target { block: start.block, phi_values: vec![] };

        let mut scope = self.module_scope.nest();

        for (i, param) in decl.ast.params.iter().enumerate() {
            // get all of the types
            let ty = decl.func_ty.params[i];
            let ty_ir = self.prog.get_func(self.ir_func).func_ty.params[i];
            let ty_ptr = self.types.define_type_ptr(ty);

            //create the param
            let ir_param = self.prog.define_param(ir::ParameterInfo { ty: ty_ir });
            self.prog.get_func_mut(self.ir_func).params.push(ir_param);

            //allocate a slot for the parameter so its address can be taken
            let slot = self.define_slot(ty_ir);

            //immediately copy the param into the slot
            let store = ir::InstructionInfo::Store {
                addr: ir::Value::Slot(slot),
                value: ir::Value::Param(ir_param),
            };
            self.append_instr(start.block, store);

            let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Slot(slot) });
            let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
            scope.maybe_declare(&param.id, item)?;
        }

        let body = decl.ast.body.as_ref().
            expect("can only generate code for functions with a body");
        let end = self.append_nested_block(start, &scope, body)?;

        if end.needs_return {
            if self.ret_ty == self.types.type_void() {
                //automatically insert return
                let ret = ir::Terminator::Return { value: ir::Value::Undef(self.prog.ty_ptr()) };
                self.prog.get_block_mut(end.block).terminator = ret;
            } else {
                return Err(Error::MissingReturn(&decl.ast.id));
            }
        }

        Ok(())
    }
}
