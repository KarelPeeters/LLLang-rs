use crate::front::{ast, cst, error};
use crate::front::ast::DotIndexIndex;
use crate::front::cst::{ItemStore, ScopedItem, ScopedValue, ScopeKind, TypeInfo};
use crate::front::error::{Error, Result};
use crate::front::lower::{LRValue, MappingTypeStore, TypedValue};
use crate::front::scope::Scope;
use crate::mid::ir;
use crate::mid::ir::ParameterInfo;

pub struct LoopInfo {
    cond: ir::Block,
    end: ir::Block,
    end_needs_return: bool,
}

//TODO think about field order
pub struct LowerFuncState<'ir, 'ast, 'cst, F: Fn(ScopedValue) -> LRValue> {
    pub prog: &'ir mut ir::Program,

    pub items: &'cst ItemStore<'ast>,
    pub types: &'cst mut MappingTypeStore<'ast>,

    pub module_scope: &'cst Scope<'static, ScopedItem>,
    pub map_value: F,

    pub ir_func: ir::Function,
    pub ret_ty: cst::Type,

    pub loop_stack: Vec<LoopInfo>,
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

impl<'m, 'a, 'c, F: Fn(ScopedValue) -> LRValue> LowerFuncState<'m, 'a, 'c, F> {
    fn resolve_type(&mut self, ty: &'a ast::Type) -> Result<'a, cst::Type> {
        self.items.resolve_type(ScopeKind::Real, &self.module_scope, &mut self.types.inner, ty)
    }

    fn type_of_lrvalue(&self, value: LRValue) -> cst::Type {
        match value {
            LRValue::Left(value) => self.types[value.ty].unwrap_ptr()
                .unwrap_or_else(|| panic!("Left({:?}) should have pointer type", value)),
            LRValue::Right(value) => value.ty,
        }
    }

    fn check_type_match(&self, expr: &'a ast::Expression, expected: Option<cst::Type>, actual: cst::Type) -> Result<'a, ()> {
        if let Some(expected) = expected {
            if expected != actual {
                return Err(Error::TypeMismatch {
                    expression: expr,
                    expected: self.types.format_type(expected).to_string(),
                    actual: self.types.format_type(actual).to_string(),
                });
            }
        }
        Ok(())
    }

    fn check_integer_type(&self, expr: &'a ast::Expression, actual: cst::Type) -> Result<'a, ()> {
        match self.types[actual] {
            TypeInfo::Byte | TypeInfo::Int => Ok(()),
            _ => Err(Error::ExpectIntegerType {
                expression: expr,
                actual: self.types.format_type(actual).to_string(),
            }),
        }
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
        let slot = ir::StackSlotInfo::new(inner_ty, &mut self.prog);
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
                let load_instr = self.append_instr(block, ir::InstructionInfo::Load { addr: value.ir });
                TypedValue { ty: inner_ty, ir: ir::Value::Instr(load_instr) }
            }
            LRValue::Right(value) =>
                value,
        }
    }

    //Return the "never" value returned by expressions like break, continue and return
    #[must_use]
    fn never_value(&mut self, expect_ty: Option<cst::Type>) -> LRValue {
        //TODO replace this with actual "never" value
        let ty_void = self.types.type_void();
        let ty = expect_ty.unwrap_or_else(|| self.types.define_type_ptr(ty_void));
        let ty_ir = self.types.map_type(&mut self.prog, ty);

        return LRValue::Left(TypedValue { ty, ir: ir::Value::Undef(ty_ir) });
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
        scope: &Scope<ScopedItem>,
        expr: &'a ast::Expression,
        expect_ty: Option<cst::Type>,
    ) -> Result<'a, (Flow, LRValue)> {
        let result: (Flow, LRValue) = match &expr.kind {
            ast::ExpressionKind::Null => {
                // flexible, null can take on any pointer type
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                self.types[ty].unwrap_ptr()
                    .ok_or(Error::ExpectPointerType {
                        expression: expr,
                        actual: self.types.format_type(ty).to_string(),
                    })?;
                let ir_ty = self.types.map_type(&mut self.prog, ty);

                let cst = ir::Value::Const(ir::Const { ty: ir_ty, value: 0 });
                (flow, LRValue::Right(TypedValue { ty, ir: cst }))
            }
            ast::ExpressionKind::BoolLit { value } => {
                let ty_bool = self.types.type_bool();
                let ty_bool_ir = self.prog.type_bool();

                self.check_type_match(expr, expect_ty, ty_bool)?;
                let cst = ir::Value::Const(ir::Const { ty: ty_bool_ir, value: *value as i32 });
                (flow, LRValue::Right(TypedValue { ty: ty_bool, ir: cst }))
            }
            ast::ExpressionKind::IntLit { value } => {
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;

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

                self.check_type_match(expr, expect_ty, ty_byte_ptr)?;

                let data = ir::DataInfo {
                    ty: self.types.map_type(&mut self.prog, ty_byte_ptr),
                    inner_ty: self.types.map_type(&mut self.prog, ty_byte),
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
                    return Err(item.err_unexpected_kind(error::ItemType::Value, path));
                };

                self.check_type_match(expr, expect_ty, self.type_of_lrvalue(value))?;
                (flow, value)
            }
            ast::ExpressionKind::Ternary { condition, then_value, else_value } => {
                //TODO remove this once there is better type inference
                let ty = expect_ty.ok_or(Error::CannotInferType(expr.span))?;
                let ty_ir = self.types.map_type(&mut self.prog, ty);

                let result_slot = self.define_slot(ty_ir);
                let (after_cond, cond) =
                    self.append_expr_loaded(flow, scope, condition, Some(self.types.type_bool()))?;

                //TODO is it possible to do append_expr here instead? is an LValue ternary operator useful?
                //  and how does this interact with LRValue? we need to propagate the LR-ness
                //  eg (c ? a : b)[6] = 3
                let end_start = self.append_if(
                    after_cond,
                    cond.ir,
                    //TODO any way to remove this code duplication?
                    |s: &mut Self, then_start: Flow| {
                        let (then_end, then_value) =
                            s.append_expr_loaded(then_start, scope, then_value, Some(ty))?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: then_value.ir };
                        s.append_instr(then_end.block, store);

                        Ok(then_end)
                    },
                    |s: &mut Self, else_start: Flow| {
                        let (else_end, else_value) =
                            s.append_expr_loaded(else_start, scope, else_value, Some(ty))?;

                        let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(result_slot), value: else_value.ir };
                        s.append_instr(else_end.block, store);

                        Ok(else_end)
                    },
                )?;

                let load = ir::InstructionInfo::Load { addr: ir::Value::Slot(result_slot) };
                let load = self.append_instr(end_start.block, load);
                let result_value = ir::Value::Instr(load);

                (end_start, LRValue::Right(TypedValue { ty, ir: result_value }))
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let (expect_ty, result_bool) = match kind {
                    ast::BinaryOp::Add | ast::BinaryOp::Sub | ast::BinaryOp::Mul |
                    ast::BinaryOp::Div | ast::BinaryOp::Mod => {
                        (expect_ty, false)
                    }
                    ast::BinaryOp::Eq | ast::BinaryOp::Neq |
                    ast::BinaryOp::Gte | ast::BinaryOp::Gt |
                    ast::BinaryOp::Lte | ast::BinaryOp::Lt => {
                        self.check_type_match(expr, expect_ty, self.types.type_bool())?;
                        (None, true)
                    }
                };

                let (after_left, value_left) =
                    self.append_expr_loaded(flow, scope, left, expect_ty)?;
                let operand_ty = value_left.ty;
                self.check_integer_type(left, operand_ty)?;

                let result_ty = if result_bool {
                    self.types.type_bool()
                } else {
                    operand_ty
                };

                //infer the left type for the right type, TODO improve this when there is proper inference
                let (after_right, value_right) =
                    self.append_expr_loaded(after_left, scope, right, Some(operand_ty))?;

                let instr = binary_op_to_instr(*kind, value_left.ir, value_right.ir);
                let instr = self.append_instr(after_right.block, instr);

                (after_right, LRValue::Right(TypedValue { ty: result_ty, ir: ir::Value::Instr(instr) }))
            }
            ast::ExpressionKind::Unary { kind, inner } => {
                match kind {
                    ast::UnaryOp::Ref => {
                        //error if expect_ty is not a pointer, otherwise unwrap it
                        let expect_ty_inner = expect_ty
                            .map(|ty| {
                                self.types[ty]
                                    .unwrap_ptr()
                                    .ok_or_else(|| Error::ExpectPointerType {
                                        expression: expr,
                                        actual: self.types.format_type(ty).to_string(),
                                    })
                            }).transpose()?;

                        let (flow, inner) =
                            self.append_expr(flow, scope, inner, expect_ty_inner)?;
                        let inner = match inner {
                            //ref turns an lvalue into an rvalue
                            LRValue::Left(inner) => LRValue::Right(inner),
                            //TODO maybe this should be changed to create a new temporary variable instead?
                            LRValue::Right(_) => return Err(Error::ReferenceOfLValue(expr)),
                        };

                        (flow, inner)
                    }
                    ast::UnaryOp::Deref => {
                        let expect_ty_inner = expect_ty.map(|ty| self.types.define_type_ptr(ty));

                        //load to get the value and wrap as lvalue again
                        let (after_value, value) =
                            self.append_expr_loaded(flow, scope, inner, expect_ty_inner)?;
                        (after_value, LRValue::Left(value))
                    }
                    ast::UnaryOp::Neg => {
                        let (after_inner, inner) =
                            self.append_expr_loaded(flow, scope, inner, expect_ty)?;
                        let ty = inner.ty;
                        let ty_ir = self.types.map_type(&mut self.prog, ty);

                        self.check_integer_type(expr, ty)?;

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
                let (after_target, target) = self.append_expr_loaded(flow, scope, target, None)?;

                //check that the target is a function
                let target_ty = target.ty;
                let target_ty = self.types[target_ty].unwrap_func()
                    .ok_or_else(|| Error::ExpectFunctionType {
                        expression: expr,
                        actual: self.types.format_type(target_ty).to_string(),
                    })?;
                let ret_ty = target_ty.ret;

                //check return type and arg count
                self.check_type_match(expr, expect_ty, ret_ty)?;
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
                    let (after_value, value) =
                        self.append_expr_loaded(flow, scope, arg, Some(target_param_types[i]))?;
                    ir_args.push(value.ir);
                    Ok(after_value)
                })?;

                let call = ir::InstructionInfo::Call {
                    target: target.ir,
                    args: ir_args,
                };

                let call = self.append_instr(after_args.block, call);
                (after_args, LRValue::Right(TypedValue { ty: ret_ty, ir: ir::Value::Instr(call) }))
            }
            ast::ExpressionKind::DotIndex { target, index } => {
                //TODO allow reference to struct too? again, how to propagate the LR-ness?

                let (after_target, target_value) = self.append_expr(flow, scope, target, None)?;


                match target_value {
                    LRValue::Left(target_value) => {
                        let target_inner_ty = self.types[target_value.ty]
                            .unwrap_ptr()
                            .ok_or_else(|| Error::ExpectPointerType {
                                expression: &*target,
                                actual: self.types.format_type(target_value.ty).to_string(),
                            })?;

                        let (index, result_inner_ty) = match (&self.types[target_inner_ty], index) {
                            (TypeInfo::Tuple(target_ty_info), DotIndexIndex::Tuple { span, index }) => {
                                let index: u32 = index.parse().map_err(|_| {
                                    Error::InvalidLiteral {
                                        span: *span,
                                        lit: index.clone(),
                                        ty: "index".to_string(),
                                    }
                                })?;

                                if index > target_ty_info.fields.len() as u32 {
                                    return Err(Error::TupleIndexOutOfBounds {
                                        target,
                                        target_type: self.types.format_type(target_value.ty).to_string(),
                                        index,
                                    });
                                }

                                (index, target_ty_info.fields[index as usize])
                            }
                            (TypeInfo::Struct(target_ty_info), DotIndexIndex::Struct(id)) => {
                                target_ty_info.fiend_field(&id.string)
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

                        let result_ty = self.types.define_type_ptr(result_inner_ty);
                        let result_ty_ir = self.types.map_type(&mut self.prog, result_ty);

                        let struct_sub_ptr = ir::InstructionInfo::TupleFieldPtr { base: target_value.ir, index, result_ty: result_ty_ir };
                        let struct_sub_ptr = self.append_instr(after_target.block, struct_sub_ptr);

                        (after_target, LRValue::Left(TypedValue { ty: result_ty, ir: ir::Value::Instr(struct_sub_ptr) }))
                    }
                    LRValue::Right(_) => {
                        //TODO really? why? origin().x should work too, right?
                        //  just allow both of them and propagate the LRNess
                        panic!("dot indexing only works for LValues")
                    }
                }
            }
            ast::ExpressionKind::Return { value } => {
                let ret_ty = self.ret_ty;

                let (after_value, value) = if let Some(value) = value {
                    self.append_expr_loaded(flow, scope, value, Some(ret_ty))?
                } else {
                    //check that function return type is indeed void
                    let ty_void = self.types.type_void();
                    self.check_type_match(expr, Some(ret_ty), ty_void)?;
                    (flow, TypedValue { ty: ty_void, ir: ir::Value::Undef(self.prog.type_void()) })
                };

                let ret = ir::Terminator::Return { value: value.ir };
                self.prog.get_block_mut(after_value.block).terminator = ret;

                //continue writing dead code
                (self.new_flow(false), self.never_value(expect_ty))
            }
            ast::ExpressionKind::Continue =>
                self.append_break_or_continue(flow, expr, expect_ty, ContinueOrBreak::Continue)?,
            ast::ExpressionKind::Break =>
                self.append_break_or_continue(flow, expr, expect_ty, ContinueOrBreak::Break)?,
        };

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let ty = self.type_of_lrvalue(result.1);
            self.check_type_match(expr, expect_ty, ty).expect("bug in lower")
        }

        Ok(result)
    }

    fn append_break_or_continue(
        &mut self,
        flow: Flow,
        expr: &'a ast::Expression,
        expect_ty: Option<cst::Type>,
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

        //continue writing dead code
        Ok((self.new_flow(false), self.never_value(expect_ty)))
    }

    fn append_expr_loaded(
        &mut self,
        flow: Flow,
        scope: &Scope<ScopedItem>,
        expr: &'a ast::Expression,
        expect_ty: Option<cst::Type>,
    ) -> Result<'a, (Flow, TypedValue)> {
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

    fn append_statement(&mut self, flow: Flow, scope: &mut Scope<ScopedItem>, stmt: &'a ast::Statement) -> Result<'a, Flow> {
        match &stmt.kind {
            ast::StatementKind::Declaration(decl) => {
                assert!(!decl.mutable, "everything is mutable for now");
                let expect_ty = decl.ty.as_ref()
                    .map(|ty| self.resolve_type(ty))
                    .transpose()?;

                let (after_value, value) = if let Some(init) = &decl.init {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, &init, expect_ty)?;
                    (after_value, Some(value))
                } else {
                    (flow, None)
                };

                //figure out the type
                let value_ty = value.map(|v| v.ty);
                let ty = expect_ty.or(value_ty).ok_or(Error::CannotInferType(decl.span))?;
                let ty_ptr = self.types.define_type_ptr(ty);
                let ty_ir = self.types.map_type(&mut self.prog, ty);

                //define the slot
                let slot = self.define_slot(ty_ir);
                let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Slot(slot) });
                let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
                scope.declare(&decl.id, item)?;

                //optionally store the value
                if let Some(value) = value {
                    let store = ir::InstructionInfo::Store { addr: ir::Value::Slot(slot), value: value.ir };
                    self.append_instr(after_value.block, store);
                }

                Ok(after_value)
            }
            ast::StatementKind::Assignment(assign) => {
                let (after_addr, addr) = self.append_expr(flow, scope, &assign.left, None)?;

                match addr {
                    LRValue::Left(addr) => {
                        let inner_ty = self.types[addr.ty].unwrap_ptr()
                            .expect("Left should have pointer type");

                        let (after_value, value) =
                            self.append_expr_loaded(after_addr, scope, &assign.right, Some(inner_ty))?;

                        let store = ir::InstructionInfo::Store { addr: addr.ir, value: value.ir };
                        self.append_instr(after_value.block, store);

                        Ok(after_value)
                    }
                    LRValue::Right(_) => Err(Error::StoreIntoRValue(&assign.left)),
                }
            }
            ast::StatementKind::If(if_stmt) => {
                let (cond_end, cond) =
                    self.append_expr_loaded(flow, scope, &if_stmt.cond, Some(self.types.type_bool()))?;

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
                let ty_bool = self.types.type_bool();
                self.append_loop(
                    flow,
                    |s: &mut Self, cond_start: Flow| {
                        let (flow, cond) =
                            s.append_expr_loaded(cond_start, scope, &while_stmt.cond, Some(ty_bool))?;
                        Ok((flow, cond.ir))
                    },
                    |s: &mut Self, body_start: Flow| {
                        s.append_nested_block(body_start, scope, &while_stmt.body)
                    },
                )
            }
            ast::StatementKind::For(for_stmt) => {
                //figure out the index type
                let index_ty = for_stmt.index_ty.as_ref()
                    .map(|var_ty| self.resolve_type(var_ty))
                    .transpose()?;
                if let Some(index_ty) = index_ty {
                    self.check_integer_type(&for_stmt.start, index_ty)?;
                }

                //evaluate the range
                let (flow, start_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.start, index_ty)?;
                let index_ty = start_value.ty;
                let index_ty_ptr = self.types.define_type_ptr(index_ty);
                let index_ty_ir = self.types.map_type(&mut self.prog, index_ty);
                self.check_integer_type(&for_stmt.start, index_ty)?;

                let (flow, end_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.end, Some(index_ty))?;

                //declare slot for index
                let mut index_scope = scope.nest();
                let index_slot = self.define_slot(index_ty_ir);
                let index_slot = ir::Value::Slot(index_slot);

                //TODO this allows the index to be mutated, which is fine for now, but it should be marked immutable when that is implemented
                //TODO maybe consider changing the increment to use the index loaded at the beginning so it can't really be mutated after all
                let index_slot_value = LRValue::Left(TypedValue { ty: index_ty_ptr, ir: index_slot });
                let item = ScopedItem::Value(ScopedValue::Immediate(index_slot_value));
                index_scope.declare(&for_stmt.index, item)?;

                //index = start
                self.append_instr(flow.block, ir::InstructionInfo::Store { addr: index_slot, value: start_value.ir });

                //index < end
                let cond = |s: &mut Self, cond_start: Flow| {
                    let load = s.append_instr(cond_start.block, ir::InstructionInfo::Load {
                        addr: index_slot,
                    });
                    let cond = s.append_instr(cond_start.block, ir::InstructionInfo::Comparison {
                        kind: ir::LogicalOp::Lt,
                        left: ir::Value::Instr(load),
                        right: end_value.ir,
                    });

                    Ok((cond_start, ir::Value::Instr(cond)))
                };

                //body; index = index + 1
                let body = |s: &mut Self, body_start: Flow| {
                    let body_end = s.append_nested_block(body_start, &index_scope, &for_stmt.body)?;

                    let load = s.append_instr(body_end.block, ir::InstructionInfo::Load {
                        addr: index_slot,
                    });
                    let inc = s.append_instr(body_end.block, ir::InstructionInfo::Arithmetic {
                        kind: ir::ArithmeticOp::Add,
                        left: ir::Value::Instr(load),
                        right: ir::Value::Const(ir::Const { ty: index_ty_ir, value: 1 }),
                    });
                    s.append_instr(body_end.block, ir::InstructionInfo::Store {
                        addr: index_slot,
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

    fn append_nested_block(&mut self, flow: Flow, scope: &Scope<ScopedItem>, block: &'a ast::Block) -> Result<'a, Flow> {
        let mut inner_scope = scope.nest();

        block.statements.iter()
            .try_fold(flow, |flow, stmt| {
                self.append_statement(flow, &mut inner_scope, stmt)
            })
    }

    pub fn append_func(&mut self, decl: &'c cst::FunctionDecl<'a>) -> Result<'a, ()> {
        let start = self.new_flow(true);
        self.prog.get_func_mut(self.ir_func).entry = start.block;

        let mut scope = self.module_scope.nest();

        for (i, param) in decl.ast.params.iter().enumerate() {
            // get all of the types
            let ty = decl.func_ty.params[i];
            let ty_ir = self.prog.get_func(self.ir_func).func_ty.params[i];
            let ty_ptr = self.types.define_type_ptr(ty);

            //create the param
            let ir_param = self.prog.define_param(ParameterInfo { ty: ty_ir });
            self.prog.get_func_mut(self.ir_func).params.push(ir_param);

            //allocate a slot for the parameter so its address can be taken
            let slot = self.define_slot(ty_ir);

            //immediately copy the param into the slot
            self.append_instr(start.block, ir::InstructionInfo::Store {
                addr: ir::Value::Slot(slot),
                value: ir::Value::Param(ir_param),
            });

            let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::Slot(slot) });
            let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
            scope.declare(&param.id, item)?;
        }

        let body = decl.ast.body.as_ref().
            expect("can only generate code for functions with a body");
        let end = self.append_nested_block(start, &mut scope, body)?;

        if end.needs_return {
            if self.ret_ty == self.types.type_void() {
                //automatically insert return
                let ret = ir::Terminator::Return { value: ir::Value::Undef(self.prog.type_void()) };
                self.prog.get_block_mut(end.block).terminator = ret;
            } else {
                return Err(Error::MissingReturn(&decl.ast.id));
            }
        }

        Ok(())
    }
}
