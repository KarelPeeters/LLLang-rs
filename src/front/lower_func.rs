use std::collections::HashMap;
use std::convert::TryInto;

use crate::front::{ast, cst};
use crate::front::ast::MaybeIdentifier;
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

    pub func_debug_name: &'ast String,
}

/// Information about the innermost loop, used for `break` and `continue` statements.
pub struct LoopInfo {
    header: ir::Block,
    end: ir::Block,
    has_reachable_break: bool,
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

fn new_jump(block: ir::Block) -> ir::Terminator {
    ir::Terminator::Jump {
        target: new_target(block)
    }
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
    reachable: bool,
}

impl<'ir, 'ast, 'cst, 'ts, F: Fn(ScopedValue) -> LRValue> LowerFuncState<'ir, 'ast, 'cst, 'ts, F> {
    fn expr_type(&self, expr: &ast::Expression) -> cst::Type {
        self.type_solution[*self.expr_type_map.get(&(expr as *const _)).unwrap()]
    }

    fn maybe_id_debug_name(&self, id: &MaybeIdentifier) -> String {
        match id {
            MaybeIdentifier::Identifier(id) => format!("{}.{}", self.func_debug_name, id.string),
            MaybeIdentifier::Placeholder(_span) => format!("{}._", self.func_debug_name),
        }
    }

    #[must_use]
    fn new_block(&mut self) -> ir::Block {
        self.prog.define_block(ir::BlockInfo::new())
    }

    #[must_use]
    fn new_flow(&mut self, reachable: bool) -> Flow {
        Flow {
            block: self.new_block(),
            reachable,
        }
    }

    #[must_use]
    fn define_slot(&mut self, inner_ty: ir::Type, debug_name: Option<String>) -> ir::StackSlot {
        let slot = ir::StackSlotInfo { inner_ty, debug_name };
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
    fn append_negate(&mut self, block: ir::Block, value: ir::Value) -> ir::Value {
        let ty_ir = self.prog.type_of_value(value);
        let instr = ir::InstructionInfo::Arithmetic {
            kind: ir::ArithmeticOp::Sub,
            left: ir::Value::Const(ir::Const::new(ty_ir, 0)),
            right: value,
        };
        ir::Value::Instr(self.append_instr(block, instr))
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
        let then_start = self.new_flow(flow.reachable);
        let then_start_block = then_start.block;
        let then_end = then_func(self, then_start)?;

        let else_start = self.new_flow(flow.reachable);
        let else_start_block = else_start.block;
        let else_end = else_func(self, else_start)?;

        let end_start = self.new_flow(then_end.reachable || else_end.reachable);

        //connect everything
        let branch = new_branch(cond, then_start_block, else_start_block);
        let jump_end = new_jump(end_start.block);

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

                let result_slot = self.define_slot(ty_ir, None);
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

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), ty: ty_ir, value: then_value.ir };
                        s.append_instr(then_end.block, store);

                        Ok(then_end)
                    },
                    |s: &mut Self, else_start: Flow| {
                        let (else_end, else_value) =
                            s.append_expr_loaded(else_start, scope, else_value)?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), ty: ty_ir, value: else_value.ir };
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

                let result_ty = self.expr_type(expr);
                let result = if let Some(inner_ty) = self.types[result_ty].unwrap_ptr() {
                    //pointer offset
                    let offset_ir = match kind {
                        ast::BinaryOp::Add =>
                            value_right.ir,
                        ast::BinaryOp::Sub =>
                            self.append_negate(after_right.block, value_right.ir),
                        _ => panic!("Unexpected binary op kind for pointer result type, should be add or sub")
                    };

                    let inner_ty_ir = self.types.map_type(self.prog, inner_ty);
                    let instr = ir::InstructionInfo::PointerOffSet { base: value_left.ir, ty: inner_ty_ir, index: offset_ir };
                    ir::Value::Instr(self.append_instr(after_right.block, instr))
                } else {
                    //basic binary operation
                    let instr = binary_op_to_instr(*kind, value_left.ir, value_right.ir);
                    ir::Value::Instr(self.append_instr(after_right.block, instr))
                };

                (after_right, LRValue::Right(TypedValue { ty: result_ty, ir: result }))
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

                        let result = self.append_negate(after_inner.block, inner.ir);
                        (after_inner, LRValue::Right(TypedValue { ty, ir: result }))
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
                            .map(|i| i.try_into().unwrap())
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
            ast::ExpressionKind::Cast { value, ty: _ } => {
                let (after_value, value) = self.append_expr_loaded(flow, scope, value)?;
                let result_ty = self.expr_type(expr);

                // only the type changes, the (untyped) pointer value stays the same
                (after_value, LRValue::Right(TypedValue { ty: result_ty, ir: value.ir }))
            }
            ast::ExpressionKind::Return { value } => {
                let (after_value, value) = if let Some(value) = value {
                    self.append_expr_loaded(flow, scope, value)?
                } else {
                    //check that function return type is indeed void
                    let ty_void = self.types.type_void();
                    (flow, TypedValue { ty: ty_void, ir: ir::Value::Void })
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
            ast::ExpressionKind::StructLiteral { struct_path: _, fields } => {
                let struct_ty = self.expr_type(expr);
                let struct_ty_info = unwrap_match!(&self.types[struct_ty], cst::TypeInfo::Struct(info) => info).clone();
                assert_eq!(fields.len(), struct_ty_info.fields.len());

                let struct_ty_ir = self.types.map_type(self.prog, struct_ty);
                let slot = self.define_slot(struct_ty_ir, None);

                let after_stores = fields.iter().try_fold(flow, |flow, (field_id, field_value)| {
                    let field_index = struct_ty_info.find_field_index(&field_id.string).unwrap();

                    let (after_value, field_value) = self.append_expr_loaded(flow, scope, field_value)?;
                    let field_ty_ir = self.types.map_type(self.prog, field_value.ty);

                    let field_ptr = ir::InstructionInfo::TupleFieldPtr {
                        tuple_ty: struct_ty_ir,
                        base: slot.into(),
                        index: field_index.try_into().unwrap(),
                    };
                    let field_ptr = self.append_instr(after_value.block, field_ptr);

                    let store = ir::InstructionInfo::Store {
                        addr: field_ptr.into(),
                        ty: field_ty_ir,
                        value: field_value.ir,
                    };
                    self.append_instr(after_value.block, store);

                    Ok(after_value)
                })?;

                let load = ir::InstructionInfo::Load { addr: slot.into(), ty: struct_ty_ir };
                let load = self.append_instr(after_stores.block, load);

                (after_stores, LRValue::Right(TypedValue { ty: struct_ty, ir: load.into() }))
            }
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
                loop_info.header
            }
            ContinueOrBreak::Break => {
                loop_info.has_reachable_break |= flow.reachable;
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

    fn append_loop<B: FnOnce(&mut Self, Flow) -> Result<'ast, Flow>>(&mut self, flow: Flow, body: B) -> Result<'ast, Flow> {
        // bookkeeping
        // we don't make an end flow yet since we don't know if it's going to be reachable
        let body_start = self.new_flow(flow.reachable);
        let end_start = self.new_block();

        let loop_info = LoopInfo {
            header: body_start.block,
            end: end_start,
            has_reachable_break: false,
        };
        self.loop_stack.push(loop_info);

        // body
        let body_start_block = body_start.block;
        let body_end = body(self, body_start)?;
        let has_reachable_exit = self.loop_stack.pop().unwrap().has_reachable_break;

        // doesn't matter, the loop stops the flow of reachability
        let _ = body_end.reachable;

        // connect everything
        self.prog.get_block_mut(flow.block).terminator = new_jump(body_start_block);
        self.prog.get_block_mut(body_end.block).terminator = new_jump(body_start_block);

        let end_start = Flow { block: end_start, reachable: has_reachable_exit };
        Ok(end_start)
    }

    fn append_while_loop<
        C: FnOnce(&mut Self, Flow) -> Result<'ast, (Flow, ir::Value)>,
        B: FnOnce(&mut Self, Flow) -> Result<'ast, Flow>
    >(&mut self, flow: Flow, cond: C, body: B) -> Result<'ast, Flow> {
        self.append_loop(flow, |s, flow| {
            let (cond_end, cond) = cond(s, flow)?;

            s.append_if(cond_end, cond, |s, flow| {
                // condition true, run the body (and then automatically loop back)
                body(s, flow)
            }, |s, flow| {
                // condition false, break loop
                let loop_info = s.loop_stack.last_mut().unwrap();

                loop_info.has_reachable_break |= flow.reachable;
                s.prog.get_block_mut(flow.block).terminator = new_jump(loop_info.end);

                // continue writing dead code
                Ok(s.new_flow(false))
            })
        })
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
                let debug_name = self.maybe_id_debug_name(&decl.id);
                let slot = self.define_slot(ty_ir, Some(debug_name));
                let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Slot(slot) });
                let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
                scope.maybe_declare(&decl.id, item)?;

                //optionally store the value
                if let Some(value) = value {
                    let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), ty: ty_ir, value: value.ir };
                    self.append_instr(after_value.block, store);
                }

                Ok(after_value)
            }
            ast::StatementKind::Assignment(assign) => {
                let (after_addr, addr) = self.append_expr_lvalue(flow, scope, &assign.left)?;
                let (after_value, value) =
                    self.append_expr_loaded(after_addr, scope, &assign.right)?;

                let ty_ir = self.types.map_type(self.prog, value.ty);
                let store = ir::InstructionInfo::Store { addr: addr.ir, ty: ty_ir, value: value.ir };
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
            ast::StatementKind::Loop(loop_stmt) => {
                self.append_loop(flow, |s: &mut Self, body_start| {
                    s.append_nested_block(body_start, scope, &loop_stmt.body)
                })
            }
            ast::StatementKind::While(while_stmt) => {
                self.append_while_loop(
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
                let debug_name = self.maybe_id_debug_name(&for_stmt.index);
                let index_slot = self.define_slot(index_ty_ir, Some(debug_name));
                let index_slot = ir::Value::Slot(index_slot);

                //TODO this allows the index to be mutated, which is fine for now, but it should be marked immutable when that is implemented
                //TODO maybe consider changing the increment to use the index loaded at the beginning so it can't really be mutated after all
                let index_slot_value = LRValue::Left(TypedValue { ty: index_ty_ptr, ir: index_slot });
                let item = ScopedItem::Value(ScopedValue::Immediate(index_slot_value));
                index_scope.maybe_declare(&for_stmt.index, item)?;

                //index = start
                self.append_instr(flow.block, ir::InstructionInfo::Store { addr: index_slot, ty: index_ty_ir, value: start_value.ir });

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
                        ty: index_ty_ir,
                        value: ir::Value::Instr(inc),
                    };
                    s.append_instr(body_end.block, store);

                    Ok(body_end)
                };

                self.append_while_loop(flow, cond, body)
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
            let debug_name = self.maybe_id_debug_name(&param.id);
            let slot = self.define_slot(ty_ir, Some(debug_name));

            //immediately copy the param into the slot
            let store = ir::InstructionInfo::Store {
                addr: ir::Value::Slot(slot),
                ty: ty_ir,
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

        if end.reachable {
            if self.ret_ty == self.types.type_void() {
                //automatically insert return
                let ret = ir::Terminator::Return { value: ir::Value::Void };
                self.prog.get_block_mut(end.block).terminator = ret;
            } else {
                return Err(Error::MissingReturn(&decl.ast.id));
            }
        }

        Ok(())
    }
}
