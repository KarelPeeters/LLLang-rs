use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::TryInto;

use crate::front::{ast, cst, DEFAULT_CALLING_CONVENTION};
use crate::front::ast::{LogicalOp};
use crate::front::cst::{IntTypeInfo, ItemStore, ScopedItem, ScopedValue, ScopeKind, TypeInfo};
use crate::front::error::{Error, Result};
use crate::front::lower::{lower_literal, LRValue, MappingTypeStore, TypedValue};
use crate::front::scope::Scope;
use crate::front::type_solver::{TypeSolution, TypeVar};
use crate::mid::ir;
use crate::mid::ir::{ExpressionInfo, Signed};
use crate::mid::util::bit_int::{BitInt, UStorage};

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

#[derive(Debug)]
enum BinaryArgType {
    Int(Signed),
    Bool,
}

impl BinaryArgType {
    fn unwrap_int(self) -> Signed {
        unwrap_match!(self, BinaryArgType::Int(signed) => signed)
    }
}

fn binary_op_to_expr(ast_kind: ast::BinaryOp, arg_ty: BinaryArgType, arg_ty_ir: ir::Type, left: ir::Value, right: ir::Value) -> ir::ExpressionInfo {
    match ast_kind {
        ast::BinaryOp::Add => {
            arg_ty.unwrap_int();
            ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Add, ty: arg_ty_ir, left, right }
        }
        ast::BinaryOp::Sub => {
            arg_ty.unwrap_int();
            ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Sub, ty: arg_ty_ir, left, right }
        }
        ast::BinaryOp::Mul => {
            arg_ty.unwrap_int();
            ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Mul, ty: arg_ty_ir, left, right }
        }
        ast::BinaryOp::Div => ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Div(arg_ty.unwrap_int()), ty: arg_ty_ir, left, right },
        ast::BinaryOp::Mod => ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Mod(arg_ty.unwrap_int()), ty: arg_ty_ir, left, right },

        ast::BinaryOp::Gte => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Gte(arg_ty.unwrap_int()), left, right },
        ast::BinaryOp::Gt => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Gt(arg_ty.unwrap_int()), left, right },
        ast::BinaryOp::Lte => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Lte(arg_ty.unwrap_int()), left, right },
        ast::BinaryOp::Lt => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Lt(arg_ty.unwrap_int()), left, right },

        ast::BinaryOp::Eq => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Eq, left, right },
        ast::BinaryOp::Neq => ir::ExpressionInfo::Comparison { kind: ir::ComparisonOp::Neq, left, right },

        ast::BinaryOp::And => ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::And, ty: arg_ty_ir, left, right },
        ast::BinaryOp::Or => ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Or, ty: arg_ty_ir, left, right },
        ast::BinaryOp::Xor => ir::ExpressionInfo::Arithmetic { kind: ir::ArithmeticOp::Xor, ty: arg_ty_ir, left, right },
    }
}

fn new_target(block: ir::Block) -> ir::Target {
    ir::Target { block, args: Vec::new() }
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
        self.type_solution[*self.expr_type_map.get(&(expr as *const _)).unwrap_or_else(|| panic!("Missing type for expr {:?}", expr))]
    }

    fn fixed_debug_name(&self, name: &str) -> String {
        // TODO add index to deduplicate debug names
        format!("{}.[{}]", self.func_debug_name, name)
    }

    fn maybe_id_debug_name(&self, id: &ast::MaybeIdentifier) -> String {
        match id {
            ast::MaybeIdentifier::Identifier(id) => format!("{}.{}", self.func_debug_name, id.string),
            ast::MaybeIdentifier::Placeholder(_span) => format!("{}._", self.func_debug_name),
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
    fn define_slot(&mut self, inner_ty: ir::Type, debug_name: String) -> ir::StackSlot {
        let slot = ir::StackSlotInfo { inner_ty, debug_name: Some(debug_name) };
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
    fn append_negate(&mut self, value: ir::Value) -> ir::Value {
        let ty_ir = self.prog.type_of_value(value);
        let bits = self.prog.get_type(ty_ir).unwrap_int().unwrap();

        self.prog.define_expr(ir::ExpressionInfo::Arithmetic {
            kind: ir::ArithmeticOp::Sub,
            ty: ty_ir,
            left: ir::Const { ty: ty_ir, value: BitInt::zero(bits) }.into(),
            right: value,
        }).into()
    }

    #[must_use]
    fn append_not(&mut self, value: ir::Value) -> ir::Value {
        let ty_ir = self.prog.type_of_value(value);

        let bits = self.prog.get_type(ty_ir).unwrap_int().unwrap();
        let ones = BitInt::from_signed(bits, -1).unwrap();

        self.prog.define_expr(ir::ExpressionInfo::Arithmetic {
            kind: ir::ArithmeticOp::Xor,
            ty: ty_ir,
            left: value,
            right: ir::Const::new(ty_ir, ones).into(),
        }).into()
    }

    fn append_store(&mut self, block: ir::Block, addr: ir::Value, value: ir::Value) {
        let ty = self.prog.type_of_value(value);
        self.append_instr(block, ir::InstructionInfo::Store { addr, ty, value });
    }

    #[must_use]
    fn append_load(&mut self, block: ir::Block, addr: ir::Value, ty: ir::Type) -> ir::Value {
        self.append_instr(block, ir::InstructionInfo::Load { addr, ty }).into()
    }

    #[must_use]
    fn append_load_typed(&mut self, block: ir::Block, addr: TypedValue) -> TypedValue {
        let inner_ty = *self.types[addr.ty].unwrap_ptr()
            .expect("Address should have pointer type");
        let inner_ty_ir = self.types.map_type(self.prog, inner_ty);

        let loaded = self.append_load(block, addr.ir, inner_ty_ir);
        TypedValue { ty: inner_ty, ir: loaded }
    }

    #[must_use]
    fn append_load_lr(&mut self, block: ir::Block, value: LRValue) -> TypedValue {
        match value {
            LRValue::Left(value) => self.append_load_typed(block, value),
            LRValue::Right(value) => value,
        }
    }

    //Return the "never" value returned by expressions like break, continue and return
    #[must_use]
    fn never_value(&mut self, ty: cst::Type) -> LRValue {
        //TODO replace this with actual "never" value
        let ty_ptr = self.types.define_type_ptr(ty);
        let ty_ptr_ir = self.types.map_type(self.prog, ty_ptr);

        LRValue::Left(TypedValue { ty: ty_ptr, ir: ir::Value::undef(ty_ptr_ir) })
    }

    fn void_value(&mut self) -> TypedValue {
        let ty_void = self.types.type_void();
        TypedValue { ty: ty_void, ir: ir::Value::void() }
    }

    fn append_int_cast(&mut self, info_before: IntTypeInfo, info_after: IntTypeInfo, value_before: ir::Value) -> ir::Value {
        // Conceptually all int casting follows the following steps:
        // * Infinitely extend the value from its original size and signedness.
        // * Truncate at the new size.
        // * Finally assume the new signedness.
        // This means that we should use the signedness from before the cast to extend.

        let ty_after = self.types.define_type(TypeInfo::Int(info_after));
        let ty_after_ir = self.types.map_type(self.prog, ty_after);

        let cast_kind = match info_after.bits.cmp(&info_before.bits) {
            Ordering::Equal => return value_before,
            Ordering::Less => ir::CastKind::IntTruncate,
            Ordering::Greater => ir::CastKind::IntExtend(info_before.signed),
        };

        self.prog.define_expr(ir::ExpressionInfo::Cast {
            ty: ty_after_ir,
            kind: cast_kind,
            value: value_before,
        }).into()
    }

    fn append_cast(&mut self, expr: &'ast ast::Expression, value_before: TypedValue, ty_after: cst::Type) -> Result<'ast, ir::Value> {
        let info_before = self.types.info_size_as_int(value_before.ty);
        let info_after = self.types.info_size_as_int(ty_after);

        match (info_before.as_ref(), info_after.as_ref()) {
            (TypeInfo::Pointer(_), TypeInfo::Pointer(_)) => {
                // IR pointers are untyped, so this is a no-op
                Ok(value_before.ir)
            }
            (&TypeInfo::Int(info_before), &TypeInfo::Int(info_after)) => {
                Ok(self.append_int_cast(info_before, info_after, value_before.ir))
            }
            (TypeInfo::Bool, &TypeInfo::Int(info_after)) => {
                // We don't also have "int->bool" since that's just "!=".
                // "bool->int" is just an unsigned int cast
                let info_before = IntTypeInfo::new(Signed::Unsigned, 1);
                Ok(self.append_int_cast(info_before, info_after, value_before.ir))
            }
            _ => Err(Error::InvalidCastTypes {
                expression: expr,
                ty_before: self.types.format_type(value_before.ty).to_string(),
                ty_after: self.types.format_type(ty_after).to_string(),
            })
        }
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

    fn append_binary_op(&mut self, kind: ast::BinaryOp, value_left: TypedValue, value_right: TypedValue) -> ir::Value {
        if let Some(&inner_ty) = self.types[value_left.ty].unwrap_ptr() {
            //pointer offset
            let offset_ir = match kind {
                ast::BinaryOp::Add =>
                    value_right.ir,
                ast::BinaryOp::Sub =>
                    self.append_negate(value_left.ir),
                _ => panic!("Unexpected binary op kind for pointer result type, should be add or sub")
            };

            let inner_ty_ir = self.types.map_type(self.prog, inner_ty);
            self.prog.define_expr(ir::ExpressionInfo::PointerOffSet {
                base: value_left.ir,
                ty: inner_ty_ir,
                index: offset_ir,
            }).into()
        } else {
            //basic binary operation
            assert_eq!(value_left.ty, value_right.ty);

            let arg_ty_ir = self.types.map_type(self.prog, value_left.ty);
            let arg_ty_info = &self.types[value_left.ty];

            let arg_ty = match *arg_ty_info {
                TypeInfo::Bool => BinaryArgType::Bool,
                TypeInfo::Int(info) => BinaryArgType::Int(info.signed),
                TypeInfo::IntSize(signed) => BinaryArgType::Int(signed),
                _ => panic!(),
            };

            self.prog.define_expr(binary_op_to_expr(
                kind,
                arg_ty,
                arg_ty_ir,
                value_left.ir,
                value_right.ir,
            )).into()
        }
    }

    fn append_dot_index(&mut self, flow: Flow, scope: &Scope<ScopedItem>, target: &'ast ast::Expression, index: &'ast ast::DotIndexIndex) -> Result<'ast, (Flow, LRValue)> {
        let (after_target, target_value) = self.append_expr(flow, scope, target)?;

        let target_outer_ty = target_value.ty(&self.types);
        let (target_inner_ty, wrapped_in_ptr) = match self.types[target_outer_ty] {
            TypeInfo::Pointer(target_inner_ty) => (target_inner_ty, true),
            _ => (target_outer_ty, false)
        };

        let (index, field_ty) = match (&self.types[target_inner_ty], index) {
            (TypeInfo::Tuple(tuple_ty), &ast::DotIndexIndex::Tuple { index, .. }) => {
                (index, tuple_ty.fields[index as usize])
            }
            (TypeInfo::Struct(struct_ty), ast::DotIndexIndex::Struct(id)) => {
                struct_ty.find_field_index(&id.string)
                    .map(|index| (index.try_into().unwrap(), struct_ty.fields[index].ty))
                    .ok_or_else(|| Error::StructFieldNotFound {
                        target,
                        target_type: self.types.format_type(target_outer_ty).to_string(),
                        index: id,
                    })?
            }
            (TypeInfo::Tuple(_), _) | (TypeInfo::Struct(_), _) => return Err(Error::WrongDotIndexType {
                target,
                target_type: self.types.format_type(target_outer_ty).to_string(),
                index,
            }),
            (_, _) => return Err(Error::ExpectStructOrTupleType {
                expression: target,
                actual: self.types.format_type(target_outer_ty).to_string(),
            })
        };

        let tuple_ty_ir = self.types.map_type(self.prog, target_inner_ty);
        let field_ty_ir = self.types.map_type(self.prog, field_ty);
        let field_ptr_ty = self.types.define_type(TypeInfo::Pointer(field_ty));

        let result = match (target_value, wrapped_in_ptr) {
            // LValue(Struct) -> LValue(Field)
            (LRValue::Left(target_value), false) => {
                let field_ptr = self.prog.define_expr(ExpressionInfo::TupleFieldPtr {
                    base: target_value.ir,
                    index,
                    tuple_ty: tuple_ty_ir,
                });
                LRValue::Left(TypedValue {
                    ty: field_ptr_ty,
                    ir: field_ptr.into(),
                })
            }
            // RValue(Struct) -> RValue(Field)
            (LRValue::Right(target_value), false) => {
                // store into temp slot, offset, load
                let slot = self.define_slot(tuple_ty_ir, self.fixed_debug_name("dot_index"));
                self.append_store(after_target.block, slot.into(), target_value.ir);
                let field_ptr = self.prog.define_expr(ExpressionInfo::TupleFieldPtr {
                    base: slot.into(),
                    index,
                    tuple_ty: tuple_ty_ir,
                });
                let load = self.append_load(after_target.block, field_ptr.into(), field_ty_ir);
                LRValue::Right(TypedValue {
                    ty: field_ty,
                    ir: load,
                })
            }
            // LRValue(&Struct) -> RValue(&Field)
            (target_value, true) => {
                let target_value = self.append_load_lr(after_target.block, target_value);

                let field_ptr = self.prog.define_expr(ExpressionInfo::TupleFieldPtr {
                    base: target_value.ir,
                    index,
                    tuple_ty: tuple_ty_ir,
                });

                LRValue::Right(TypedValue {
                    ty: field_ptr_ty,
                    ir: field_ptr.into(),
                })
            }
        };

        Ok((after_target, result))
    }

    fn append_expr(
        &mut self,
        flow: Flow,
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, (Flow, LRValue)> {
        let result: (Flow, LRValue) = match &expr.kind {
            ast::ExpressionKind::Wrapped { inner } => {
                self.append_expr(flow, scope, inner)?
            }
            ast::ExpressionKind::Null | ast::ExpressionKind::BoolLit { .. } | ast::ExpressionKind::IntLit { .. } | ast::ExpressionKind::StringLit { .. } => {
                let value = self.lower_literal(expr)?;
                (flow, value)
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

                let result_slot = self.define_slot(ty_ir, self.fixed_debug_name("ternary"));
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
                        s.append_store(then_end.block, result_slot.into(), then_value.ir);
                        Ok(then_end)
                    },
                    |s: &mut Self, else_start: Flow| {
                        let (else_end, else_value) =
                            s.append_expr_loaded(else_start, scope, else_value)?;
                        s.append_store(else_end.block, result_slot.into(), else_value.ir);
                        Ok(else_end)
                    },
                )?;

                let result_value = self.append_load(end_start.block, result_slot.into(), ty_ir);
                (end_start, LRValue::Right(TypedValue { ty, ir: result_value }))
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let (after_left, value_left) =
                    self.append_expr_loaded(flow, scope, left)?;
                let (after_right, value_right) =
                    self.append_expr_loaded(after_left, scope, right)?;

                let result_ty = self.expr_type(expr);
                let result = self.append_binary_op(*kind, value_left, value_right);

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

                        let result = self.append_negate(inner.ir);
                        (after_inner, LRValue::Right(TypedValue { ty, ir: result }))
                    }
                    ast::UnaryOp::Not => {
                        let (after_inner, inner) =
                            self.append_expr_loaded(flow, scope, inner)?;
                        let ty = inner.ty;

                        let result = self.append_not(inner.ir);
                        (after_inner, LRValue::Right(TypedValue { ty, ir: result }))
                    }
                }
            }
            ast::ExpressionKind::Logical { kind, left, right } => {
                let ty_bool_ir = self.prog.ty_bool();
                let ty_bool = self.types.type_bool();

                let slot = self.define_slot(ty_bool_ir, self.fixed_debug_name("logical"));

                let (after_left, left_value) = self.append_expr_loaded(flow, scope, left)?;
                assert_eq!(left_value.ty, ty_bool);

                let cond = match kind {
                    LogicalOp::And => left_value.ir,
                    LogicalOp::Or => self.append_not(left_value.ir),
                };

                let after_both = self.append_if(after_left, cond, |s, flow| {
                    let (after_right, right_value) = s.append_expr_loaded(flow, scope, right)?;
                    s.append_store(after_right.block, slot.into(), right_value.ir);
                    Ok(after_right)
                }, |s, flow| {
                    s.append_store(flow.block, slot.into(), left_value.ir);
                    Ok(flow)
                })?;

                let result_value = self.append_load(after_both.block, slot.into(), ty_bool_ir);
                (after_both, LRValue::Right(TypedValue { ty: ty_bool, ir: result_value }))
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
                    conv: DEFAULT_CALLING_CONVENTION,
                };
                let call = self.append_instr(after_args.block, call);

                (after_args, LRValue::Right(TypedValue { ty: ret_ty, ir: call.into() }))
            }
            ast::ExpressionKind::DotIndex { target, index } => {
                self.append_dot_index(flow, scope, target, index)?
            }
            ast::ExpressionKind::ArrayIndex { target, index } => {
                let (after_target, target_value) = self.append_expr_lvalue(flow, scope, target)?;
                let (after_index, index) = self.append_expr_loaded(after_target, scope, index)?;

                let result_ty = self.expr_type(expr);
                let result_ty_ir = self.types.map_type(self.prog, result_ty);
                let result_ty_ptr = self.types.define_type_ptr(result_ty);

                let array_index_ptr = self.prog.define_expr(ir::ExpressionInfo::PointerOffSet {
                    ty: result_ty_ir,
                    base: target_value.ir,
                    index: index.ir,
                }).into();

                (after_index, LRValue::Left(TypedValue { ty: result_ty_ptr, ir: array_index_ptr }))
            }
            ast::ExpressionKind::Cast { value, ty: _ } => {
                let (after_value, value_before) = self.append_expr_loaded(flow, scope, value)?;

                let ty_after = self.expr_type(expr);
                let value_after_ir = self.append_cast(expr, value_before, ty_after)?;

                (after_value, LRValue::Right(TypedValue { ty: ty_after, ir: value_after_ir }))
            }
            ast::ExpressionKind::Return { value } => {
                let (after_value, value) = if let Some(value) = value {
                    self.append_expr_loaded(flow, scope, value)?
                } else {
                    (flow, self.void_value())
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
                let slot = self.define_slot(struct_ty_ir, self.fixed_debug_name("struct_lit"));

                let after_stores = fields.iter().try_fold(flow, |flow, (field_id, field_value)| {
                    let field_index = struct_ty_info.find_field_index(&field_id.string).unwrap();

                    let (after_value, field_value) = self.append_expr_loaded(flow, scope, field_value)?;

                    let field_ptr = self.prog.define_expr(ir::ExpressionInfo::TupleFieldPtr {
                        tuple_ty: struct_ty_ir,
                        base: slot.into(),
                        index: field_index.try_into().unwrap(),
                    }).into();

                    self.append_store(after_value.block, field_ptr, field_value.ir);

                    Ok(after_value)
                })?;

                let result_value = self.append_load(after_stores.block, slot.into(), struct_ty_ir);
                (after_stores, LRValue::Right(TypedValue { ty: struct_ty, ir: result_value }))
            }
            ast::ExpressionKind::ArrayLiteral { values } => {
                let array_ty = self.expr_type(expr);
                let array_ty_ir = self.types.map_type(self.prog, array_ty);

                let slot = self.define_slot(array_ty_ir, self.fixed_debug_name("array_lit"));

                let after_stores = values.iter().enumerate().try_fold(flow, |flow, (i, value)| {
                    let (after_value, value) = self.append_expr_loaded(flow, scope, value)?;

                    let i_ustorage: UStorage = i.try_into().unwrap();
                    let i_bit_int = BitInt::from_unsigned(self.prog.ptr_size_bits(), i_ustorage).unwrap();
                    let i_const = ir::Const::new(self.prog.ty_isize(), i_bit_int);

                    let value_ptr = self.prog.define_expr(ir::ExpressionInfo::PointerOffSet {
                        ty: array_ty_ir,
                        base: slot.into(),
                        index: i_const.into(),
                    }).into();

                    self.append_store(after_value.block, value_ptr, value.ir);

                    Ok(after_value)
                })?;

                // we could return an lvalue here, but that doesn't make sense from the language POV
                let load = self.append_load(after_stores.block, slot.into(), array_ty_ir);
                (after_stores, LRValue::Right(TypedValue { ty: array_ty, ir: load.into() }))
            }
            ast::ExpressionKind::Obscure { value } => {
                let (flow_after, value) = self.append_expr_loaded(flow, scope, value)?;

                let ty_ir = self.types.map_type(self.prog, value.ty);
                let obscure = self.prog.define_expr(ir::ExpressionInfo::Obscure { ty: ty_ir, value: value.ir });

                (flow_after, LRValue::Right(TypedValue { ty: value.ty, ir: obscure.into() }))
            }
            ast::ExpressionKind::BlackHole { value } => {
                let (flow_after, value) = self.append_expr_loaded(flow, scope, value)?;
                self.append_instr(flow_after.block, ir::InstructionInfo::BlackHole { value: value.ir });
                (flow_after, LRValue::Right(self.void_value()))
            }
            ast::ExpressionKind::MemBarrier => {
                self.append_instr(flow.block, ir::InstructionInfo::MemBarrier);
                (flow, LRValue::Right(self.void_value()))
            }
            ast::ExpressionKind::Unreachable => {
                self.prog.get_block_mut(flow.block).terminator = ir::Terminator::Unreachable;
                //continue writing dead code
                (self.new_flow(false), self.never_value(self.expr_type(expr)))
            }
        };

        //check that the returned value's type is indeed expect_ty
        if cfg!(debug_assertions) {
            let (_, result_value) = result;

            let expect_ty = self.expr_type(expr);
            let actual_ty = result_value.ty(self.types);

            assert_eq!(
                expect_ty, actual_ty,
                "bug in lower, inferred type '{}' for expression but generated code returns '{}'",
                self.types.format_type(expect_ty), self.types.format_type(actual_ty)
            );

            if let Some(actual_ty_ir) = result_value.ty_ir(self.prog) {
                let expect_ty_ir = self.types.map_type(self.prog, expect_ty);

                assert_eq!(
                    expect_ty_ir, actual_ty_ir,
                    "bug in lower, inferred type '{}' for expression but generated code returns '{}'",
                    self.prog.format_type(expect_ty_ir), self.prog.format_type(actual_ty_ir)
                );
            };
        }

        Ok(result)
    }

    fn lower_literal(&mut self, expr: &'ast ast::Expression) -> Result<'ast, LRValue> {
        let ty = self.expr_type(expr);
        let result = lower_literal(self.types, self.prog, expr, ty);

        // TODO this is pretty ugly but will go away when we get real type checking for constants
        if let Err(Error::TypeMismatch { .. } | Error::ExpectIntegerType { .. } | Error::ExpectPointerType { .. }) = result {
            panic!("We should not be getting any type errors from literal lowering, type checking has already been done, but got {:?}", result);
        }

        if let Err(Error::ExpectedLiteral(_)) = result {
            unreachable!();
        }

        result.map(LRValue::Right)
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
        let loaded_value = self.append_load_lr(after_value.block, value);
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
                    let (after_value, value) = self.append_expr_loaded(flow, scope, init)?;
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
                let slot = self.define_slot(ty_ir, debug_name);
                let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: slot.into() });
                let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
                scope.maybe_declare(&decl.id, item)?;

                //optionally store the value
                if let Some(value) = value {
                    self.append_store(after_value.block, slot.into(), value.ir);
                }

                Ok(after_value)
            }
            ast::StatementKind::Assignment(assign) => {
                let (after_addr, addr) = self.append_expr_lvalue(flow, scope, &assign.left)?;
                let (after_right, right) =
                    self.append_expr_loaded(after_addr, scope, &assign.right)?;

                self.append_store(after_right.block, addr.ir, right.ir);
                Ok(after_right)
            }
            ast::StatementKind::BinaryAssignment(assign) => {
                let (after_left, addr) = self.append_expr_lvalue(flow, scope, &assign.left)?;
                let (after_right, right) =
                    self.append_expr_loaded(after_left, scope, &assign.right)?;

                let left = self.append_load_typed(after_right.block, addr);
                let result = self.append_binary_op(assign.op, left, right);

                self.append_store(after_right.block, addr.ir, result);
                Ok(after_right)
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

                let index_info = self.types.info_size_as_int(index_ty).unwrap_int().unwrap();
                let const_one = ir::Const { ty: index_ty_ir, value: BitInt::from_unsigned(index_info.bits, 1).unwrap() };

                //evaluate the range
                let (flow, start_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.start)?;
                let (flow, end_value) =
                    self.append_expr_loaded(flow, scope, &for_stmt.end)?;

                //declare slot for index
                let mut index_scope = scope.nest();
                let debug_name = self.maybe_id_debug_name(&for_stmt.index);
                let index_slot: ir::Value = self.define_slot(index_ty_ir, debug_name).into();

                //TODO this allows the index to be mutated, which is fine for now, but it should be marked immutable when that is implemented
                //TODO maybe consider changing the increment to use the index loaded at the beginning so it can't really be mutated after all
                let index_slot_value = LRValue::Left(TypedValue { ty: index_ty_ptr, ir: index_slot });
                let item = ScopedItem::Value(ScopedValue::Immediate(index_slot_value));
                index_scope.maybe_declare(&for_stmt.index, item)?;

                //index = start
                self.append_store(flow.block, index_slot, start_value.ir);

                //index < end
                let cond = |s: &mut Self, cond_start: Flow| {
                    let load = s.append_load(cond_start.block, index_slot, index_ty_ir);

                    let cond = s.prog.define_expr(ir::ExpressionInfo::Comparison {
                        kind: ir::ComparisonOp::Lt(index_info.signed),
                        left: load,
                        right: end_value.ir,
                    }).into();

                    Ok((cond_start, cond))
                };

                //body; index = index + 1
                let body = |s: &mut Self, body_start: Flow| {
                    let body_end = s.append_nested_block(body_start, &index_scope, &for_stmt.body)?;

                    let load = s.append_load(body_end.block, index_slot, index_ty_ir);

                    let inc = s.prog.define_expr(ir::ExpressionInfo::Arithmetic {
                        kind: ir::ArithmeticOp::Add,
                        ty: index_ty_ir,
                        left: load,
                        right: const_one.into(),
                    }).into();

                    s.append_store(body_end.block, index_slot, inc);

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
        // TODO actually collect which lines of code are part of this block, for each block separately
        let debug_name = &mut self.prog.get_block_mut(flow.block).debug_name;
        if debug_name.is_none() {
            *debug_name = Some(format!("{}_{:?}", self.func_debug_name, block.span));
        }

        let mut inner_scope = scope.nest();

        block.statements.iter()
            .try_fold(flow, |flow, stmt| {
                self.append_statement(flow, &mut inner_scope, stmt)
            })
    }

    pub fn lower_func(&mut self, decl: &'cst cst::FunctionDecl<'ast>) -> Result<'ast, ()> {
        let mut scope = self.module_scope.nest();
        let func_entry = self.prog.get_func(self.ir_func).entry;

        for (i, param) in decl.ast.params.iter().enumerate() {
            // get all of the types
            let ty = decl.func_ty.params[i];
            let ty_ir = self.prog.get_func(self.ir_func).func_ty.params[i];
            let ty_ptr = self.types.define_type_ptr(ty);

            //get the corresponding param (which is the param of the entry block)
            let ir_param = self.prog.get_block(func_entry).params.clone()[i];

            //allocate a slot for the parameter so its address can be taken
            let debug_name = self.maybe_id_debug_name(&param.id);
            let slot = self.define_slot(ty_ir, debug_name);

            //immediately copy the param into the slot
            self.append_store(func_entry, slot.into(), ir_param.into());

            let slot_value = LRValue::Left(TypedValue { ty: ty_ptr, ir: slot.into() });
            let item = ScopedItem::Value(ScopedValue::Immediate(slot_value));
            scope.maybe_declare(&param.id, item)?;
        }

        // jump from entry to start
        let start = self.new_flow(true);
        let entry_term = ir::Terminator::Jump { target: ir::Target { block: start.block, args: vec![] } };
        self.prog.get_block_mut(func_entry).terminator = entry_term;

        // append the block
        let body = decl.ast.body.as_ref().
            expect("can only generate code for functions with a body");
        let end = self.append_nested_block(start, &scope, body)?;

        // check/insert the final return
        if end.reachable {
            if self.ret_ty == self.types.type_void() {
                //automatically insert return
                let ret = ir::Terminator::Return { value: ir::Value::void() };
                self.prog.get_block_mut(end.block).terminator = ret;
            } else {
                return Err(Error::MissingReturn(&decl.ast.id));
            }
        } else {
            // TODO insert proper return for non-reachable end?
        }

        Ok(())
    }
}
