use std::collections::HashMap;

use itertools::Itertools;

use crate::front::{ast, cst, error};
use crate::front::ast::{BinaryOp, DotIndexIndex};
use crate::front::cst::{FunctionTypeInfo, ItemStore, ScopedItem, ScopedValue, ScopeKind, TypeInfo};
use crate::front::error::Result;
use crate::front::lower::{LRValue, MappingTypeStore};
use crate::front::scope::Scope;
use crate::front::type_solver::{TypeProblem, TypeVar};
use crate::mid::ir;

/// The state necessary to lower a single function.
pub struct TypeFuncState<'ast, 'cst, F: Fn(ScopedValue) -> LRValue> {
    //TODO remove dead fields
    pub items: &'cst ItemStore<'ast>,
    pub types: &'cst mut MappingTypeStore<'ast>,
    pub map_value: F,

    pub module_scope: &'cst Scope<'static, ScopedItem>,

    pub ir_func: ir::Function,
    pub ret_ty: cst::Type,

    pub expr_type_map: HashMap<*const ast::Expression, TypeVar>,
    pub decl_type_map: HashMap<*const ast::Declaration, TypeVar>,

    pub problem: TypeProblem<'ast>,
}

impl<'ast, 'cst, F: Fn(ScopedValue) -> LRValue> TypeFuncState<'ast, 'cst, F> {
    fn resolve_type(&mut self, scope: &Scope<ScopedItem>, ty: &'ast ast::Type) -> Result<'ast, cst::Type> {
        self.items.resolve_type(ScopeKind::Real, scope, &mut self.types.inner, ty)
    }

    fn type_of_scoped_value(&mut self, value: ScopedValue) -> TypeVar {
        match value {
            ScopedValue::TypeVar(var) => var,
            ScopedValue::Function(_) | ScopedValue::Const(_) | ScopedValue::Immediate(_) => {
                let ty = (self.map_value)(value).ty(&self.types);
                self.problem.fully_known(&self.types, ty)
            }
        }
    }

    fn visit_expr(
        &mut self,
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, TypeVar> {
        let result: TypeVar = match &expr.kind {
            ast::ExpressionKind::Null => {
                // null can take on any pointer type
                let inner_ty = self.problem.unknown();
                self.problem.known(TypeInfo::Pointer(inner_ty))
            }
            ast::ExpressionKind::BoolLit { .. } => {
                self.problem.ty_bool()
            }
            ast::ExpressionKind::IntLit { .. } => {
                let ty = self.problem.unknown();
                self.problem.require_int(ty);
                ty
            }
            ast::ExpressionKind::StringLit { .. } => {
                self.problem.known(TypeInfo::Pointer(self.problem.ty_byte()))
            }
            ast::ExpressionKind::Path(path) => {
                let item = self.items.resolve_path(ScopeKind::Real, scope, path)?;

                if let ScopedItem::Value(value) = item {
                    //TODO maybe inline this function into the single use location?
                    self.type_of_scoped_value(value)
                } else {
                    return Err(item.err_unexpected_kind(error::ItemType::Value, path));
                }
            }
            ast::ExpressionKind::Ternary { condition, then_value, else_value } => {
                let cond_ty = self.visit_expr(&scope, &*condition)?;
                self.problem.equal(cond_ty, self.problem.ty_bool());

                let value_ty = self.problem.unknown();
                let then_ty = self.visit_expr(&scope, then_value)?;
                let else_ty = self.visit_expr(&scope, else_value)?;
                self.problem.equal(value_ty, then_ty);
                self.problem.equal(value_ty, else_ty);

                value_ty
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let value_ty = self.problem.unknown();
                let left_ty = self.visit_expr(&scope, left)?;
                let right_ty = self.visit_expr(&scope, right)?;
                self.problem.equal(value_ty, left_ty);
                self.problem.equal(value_ty, right_ty);

                match kind {
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod =>
                        value_ty,
                    BinaryOp::Eq | BinaryOp::Neq | BinaryOp::Gte | BinaryOp::Gt | BinaryOp::Lte | BinaryOp::Lt =>
                        self.problem.ty_bool()
                }
            }
            ast::ExpressionKind::Unary { kind, inner } => {
                match kind {
                    ast::UnaryOp::Ref => {
                        let inner_ty = self.visit_expr(scope, inner)?;
                        self.problem.known(TypeInfo::Pointer(inner_ty))
                    }
                    ast::UnaryOp::Deref => {
                        let inner_ty = self.visit_expr(scope, inner)?;

                        let deref_ty = self.problem.unknown();
                        let ref_ty = self.problem.known(TypeInfo::Pointer(deref_ty));
                        self.problem.equal(inner_ty, ref_ty);

                        deref_ty
                    }
                    ast::UnaryOp::Neg => {
                        let inner_ty = self.visit_expr(scope, inner)?;
                        self.problem.require_int(inner_ty);
                        inner_ty
                    }
                }
            }
            ast::ExpressionKind::Call { target, args } => {
                let target_ty = self.visit_expr(scope, target)?;

                let arg_tys = args.iter().map(|arg| {
                    self.visit_expr(scope, arg)
                }).try_collect()?;
                let ret_ty = self.problem.unknown();
                let template = self.problem.known(TypeInfo::Function(FunctionTypeInfo {
                    params: arg_tys,
                    ret: ret_ty,
                }));

                self.problem.equal(target_ty, template);
                ret_ty
            }
            ast::ExpressionKind::DotIndex { target, index } => {
                //TODO allow reference to struct too? again, how to propagate the LR-ness?

                let target_ty = self.visit_expr(scope, target)?;

                match index {
                    DotIndexIndex::Tuple { span: _, index } => {
                        self.problem.tuple_index(target_ty, *index)
                    }
                    DotIndexIndex::Struct(id) => {
                        self.problem.struct_index(target_ty, &id.string)
                    }
                }
            }
            ast::ExpressionKind::Return { value } => {
                let value_ty = if let Some(value) = value {
                    self.visit_expr(scope, value)?
                } else {
                    self.problem.known(TypeInfo::Void)
                };

                let ret_ty = self.problem.fully_known(&self.types, self.ret_ty);
                self.problem.equal(ret_ty, value_ty);

                self.problem.unknown_with_default_void()
            }
            ast::ExpressionKind::Continue => self.problem.unknown_with_default_void(),
            ast::ExpressionKind::Break => self.problem.unknown_with_default_void(),
        };

        let prev = self.expr_type_map.insert(expr as *const _, result);
        assert!(prev.is_none());

        Ok(result)
    }

    fn visit_statement(&mut self, scope: &mut Scope<ScopedItem>, stmt: &'ast ast::Statement) -> Result<'ast, ()> {
        match &stmt.kind {
            ast::StatementKind::Declaration(decl) => {
                assert!(!decl.mutable, "everything is mutable for now");

                let expect_ty = decl.ty.as_ref()
                    .map(|ty| self.resolve_type(scope, ty))
                    .transpose()?;
                let expect_ty = match expect_ty {
                    Some(expect_ty) => self.problem.fully_known(&self.types, expect_ty),
                    None => self.problem.unknown(),
                };

                let value_ty = decl.init.as_ref()
                    .map(|init| { self.visit_expr(scope, init) })
                    .transpose()?
                    .unwrap_or_else(|| self.problem.unknown());

                self.problem.equal(expect_ty, value_ty);
                self.decl_type_map.insert(decl as *const _, expect_ty);

                scope.declare(&decl.id, ScopedItem::Value(ScopedValue::TypeVar(expect_ty)))?;

                Ok(())
            }
            ast::StatementKind::Assignment(assign) => {
                let addr_ty = self.visit_expr(scope, &assign.left)?;
                let value_ty = self.visit_expr(scope, &assign.right)?;
                self.problem.equal(addr_ty, value_ty);
                Ok(())
            }
            ast::StatementKind::If(if_stmt) => {
                let cond_ty = self.visit_expr(scope, &if_stmt.cond)?;
                self.problem.equal(cond_ty, self.problem.ty_bool());

                self.visit_nested_block(scope, &if_stmt.then_block)?;
                if let Some(else_block) = &if_stmt.else_block {
                    self.visit_nested_block(scope, else_block)?;
                }

                Ok(())
            }
            ast::StatementKind::While(while_stmt) => {
                let cond_ty = self.visit_expr(scope, &while_stmt.cond)?;
                self.problem.equal(cond_ty, self.problem.ty_bool());

                self.visit_nested_block(scope, &while_stmt.body)?;
                Ok(())
            }
            ast::StatementKind::For(for_stmt) => {
                let index_ty = for_stmt.index_ty.as_ref()
                    .map(|ty| self.resolve_type(scope, ty))
                    .transpose()?;
                let index_ty = match index_ty {
                    Some(index_ty) => self.problem.fully_known(&self.types, index_ty),
                    None => self.problem.unknown(),
                };

                let start_ty = self.visit_expr(scope, &for_stmt.start)?;
                let end_ty = self.visit_expr(scope, &for_stmt.end)?;
                self.problem.equal(index_ty, start_ty);
                self.problem.equal(index_ty, end_ty);

                let mut index_scope = scope.nest();
                index_scope.declare(&for_stmt.index, ScopedItem::Value(ScopedValue::TypeVar(index_ty)))?;

                self.visit_nested_block(&index_scope, &for_stmt.body)?;

                Ok(())
            }
            ast::StatementKind::Block(block) => {
                self.visit_nested_block(scope, block)
            }
            ast::StatementKind::Expression(expr) => {
                self.visit_expr(scope, expr)?;
                Ok(())
            }
        }
    }

    fn visit_nested_block(&mut self, scope: &Scope<ScopedItem>, block: &'ast ast::Block) -> Result<'ast, ()> {
        let mut inner_scope = scope.nest();

        block.statements.iter()
            .try_for_each(|stmt| self.visit_statement(&mut inner_scope, stmt))
    }

    pub fn visit_func(&mut self, decl: &'cst cst::FunctionDecl<'ast>) -> Result<'ast, ()> {
        let mut scope = self.module_scope.nest();

        for (i, param) in decl.ast.params.iter().enumerate() {
            let ty = decl.func_ty.params[i];
            let ty_var = self.problem.fully_known(&self.types, ty);

            scope.declare(&param.id, ScopedItem::Value(ScopedValue::TypeVar(ty_var)))?;
        }

        let body = decl.ast.body.as_ref().
            expect("can only generate code for functions with a body");
        self.visit_nested_block(&mut scope, body)?;

        Ok(())
    }
}
