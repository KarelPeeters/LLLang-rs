use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::front::{ast, cst, error};
use crate::front::ast::{BinaryOp, DotIndexIndex, LogicalOp};
use crate::front::cst::{FunctionTypeInfo, ItemStore, ScopedItem, ScopedValue, ScopeKind, TypeInfo};
use crate::front::error::{Error, Result};
use crate::front::lower::{LRValue, MappingTypeStore};
use crate::front::scope::Scope;
use crate::front::type_solver::{Origin, TypeProblem, TypeVar};
use crate::mid::ir::Signed;

/// The state necessary to lower a single function.
pub struct TypeFuncState<'ast, 'cst, F: Fn(ScopedValue) -> LRValue> {
    pub items: &'cst ItemStore<'ast>,
    pub types: &'cst mut MappingTypeStore<'ast>,
    pub map_value: F,

    pub module_scope: &'cst Scope<'static, ScopedItem>,

    pub ret_ty: cst::Type,

    pub expr_type_map: HashMap<*const ast::Expression, TypeVar>,
    pub decl_type_map: HashMap<*const ast::Declaration, TypeVar>,

    pub problem: TypeProblem<'ast>,
}

impl<'ast, 'cst, F: Fn(ScopedValue) -> LRValue> TypeFuncState<'ast, 'cst, F> {
    fn resolve_type(&mut self, scope: &Scope<ScopedItem>, ty: &'ast ast::Type) -> Result<'ast, cst::Type> {
        self.items.resolve_type(ScopeKind::Real, scope, &mut self.types.inner, ty)
    }

    fn resolve_path_type(&mut self, scope: &Scope<ScopedItem>, path: &'ast ast::Path) -> Result<'ast, cst::Type> {
        self.items.resolve_path_type(ScopeKind::Real, scope, path)
    }

    fn visit_expr(
        &mut self,
        scope: &Scope<ScopedItem>,
        expr: &'ast ast::Expression,
    ) -> Result<'ast, TypeVar> {
        let expr_origin = Origin::Expression(expr);

        let result: TypeVar = match &expr.kind {
            ast::ExpressionKind::Null => {
                // null can take on any pointer type
                let inner_ty = self.problem.unknown(expr_origin);
                self.problem.known(expr_origin, TypeInfo::Pointer(inner_ty))
            }
            ast::ExpressionKind::BoolLit { .. } => {
                self.problem.ty_bool()
            }
            ast::ExpressionKind::IntLit { value, ty: ty_lit } => {
                // TODO should we prefer this style which always defines an unknown var,
                //   or just immediately return the type decl like we sometimes do elsewhere (eg. declaration)?
                let ty_expr = self.problem.unknown_int(expr_origin, None);

                if let Some(ty_lit) = ty_lit {
                    // require type specification to match
                    let ty_lit = self.resolve_type(scope, ty_lit)?;
                    let ty_lit = self.problem.fully_known(&self.types, ty_lit);
                    self.problem.equal(ty_expr, ty_lit);
                }

                if value.starts_with("0x") {
                    // require hex literals to be unsigned
                    let ty_unsigned = self.problem.unknown_int(expr_origin, Some(Signed::Unsigned));
                    self.problem.equal(ty_expr, ty_unsigned);
                }

                ty_expr
            }
            ast::ExpressionKind::StringLit { .. } => {
                self.problem.known(expr_origin, TypeInfo::Pointer(self.problem.ty_u8()))
            }
            ast::ExpressionKind::Path(path) => {
                let item = self.items.resolve_path(ScopeKind::Real, scope, path)?;

                if let ScopedItem::Value(value) = item {
                    match value {
                        ScopedValue::TypeVar(var) => var,
                        ScopedValue::Function(_) | ScopedValue::Const(_) | ScopedValue::Immediate(_) => {
                            let ty = (self.map_value)(value).ty(&self.types);
                            self.problem.fully_known(&self.types, ty)
                        }
                    }
                } else {
                    return Err(item.err_unexpected_kind(error::ItemType::Value, path));
                }
            }
            ast::ExpressionKind::Ternary { condition, then_value, else_value } => {
                let cond_ty = self.visit_expr(&scope, &*condition)?;
                self.problem.equal(cond_ty, self.problem.ty_bool());

                let value_ty = self.problem.unknown(expr_origin);
                let then_ty = self.visit_expr(&scope, then_value)?;
                let else_ty = self.visit_expr(&scope, else_value)?;
                self.problem.equal(value_ty, then_ty);
                self.problem.equal(value_ty, else_ty);

                value_ty
            }
            ast::ExpressionKind::Binary { kind, left, right } => {
                let left_ty = self.visit_expr(&scope, left)?;
                let right_ty = self.visit_expr(&scope, right)?;

                let (result_ty, arg_ty) = match kind {
                    // special case for pointer math
                    BinaryOp::Add | BinaryOp::Sub => {
                        self.problem.add_sub_constraint(left_ty, right_ty);
                        (left_ty, None)
                    }
                    // any int -> same int
                    BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                        let ty = self.problem.unknown_int(expr_origin, None);
                        (ty, Some(ty))
                    }
                    // any int -> bool
                    BinaryOp::Gte | BinaryOp::Gt | BinaryOp::Lte | BinaryOp::Lt => {
                        let ty = self.problem.unknown_int(expr_origin, None);
                        (self.problem.ty_bool(), Some(ty))
                    }
                    // any int or bool -> bool
                    // TODO maybe this should also accept structs and tuples?
                    BinaryOp::Eq | BinaryOp::Neq => {
                        let ty = self.problem.unknown_int_or_bool(expr_origin, None);
                        (ty, Some(ty))
                    }
                    // unsigned int or bool -> same type
                    BinaryOp::And | BinaryOp::Or | BinaryOp::Xor => {
                        let ty = self.problem.unknown_int_or_bool(expr_origin, Some(Signed::Unsigned));
                        (ty, Some(ty))
                    }
                };

                if let Some(arg_ty) = arg_ty {
                    self.problem.equal(arg_ty, left_ty);
                    self.problem.equal(arg_ty, right_ty);
                }

                result_ty
            }
            ast::ExpressionKind::Unary { kind, inner } => {
                match kind {
                    ast::UnaryOp::Ref => {
                        let inner_ty = self.visit_expr(scope, inner)?;
                        self.problem.known(expr_origin, TypeInfo::Pointer(inner_ty))
                    }
                    ast::UnaryOp::Deref => {
                        let inner_ty = self.visit_expr(scope, inner)?;

                        let deref_ty = self.problem.unknown(expr_origin);
                        let ref_ty = self.problem.known(expr_origin, TypeInfo::Pointer(deref_ty));
                        self.problem.equal(inner_ty, ref_ty);

                        deref_ty
                    }
                    ast::UnaryOp::Neg => {
                        let value_ty = self.problem.unknown_int(expr_origin, Some(Signed::Signed));
                        let inner_ty = self.visit_expr(scope, inner)?;
                        self.problem.equal(value_ty, inner_ty);
                        value_ty
                    }
                }
            }
            ast::ExpressionKind::Logical { kind, left, right } => {
                let (LogicalOp::And | LogicalOp::Or) = kind;
                
                let left_ty = self.visit_expr(&scope, left)?;
                let right_ty = self.visit_expr(&scope, right)?;
                
                let ty_bool = self.problem.ty_bool();
                self.problem.equal(ty_bool, left_ty);
                self.problem.equal(ty_bool, right_ty);
                ty_bool
            }
            ast::ExpressionKind::Call { target, args } => {
                let target_ty = self.visit_expr(scope, target)?;

                let arg_tys = args.iter().map(|arg| {
                    self.visit_expr(scope, arg)
                }).try_collect()?;
                let ret_ty = self.problem.unknown(expr_origin);
                let template = self.problem.known(expr_origin, TypeInfo::Function(FunctionTypeInfo {
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
                        self.problem.tuple_index(expr_origin, target_ty, *index)
                    }
                    DotIndexIndex::Struct(id) => {
                        self.problem.struct_index(expr_origin, target_ty, &id.string)
                    }
                }
            }
            ast::ExpressionKind::ArrayIndex { target, index } => {
                let target_ty = self.visit_expr(scope, target)?;
                let index_ty = self.visit_expr(scope, index)?;

                self.problem.equal(self.problem.ty_usize(), index_ty);
                // TODO allow array indexing on pointers
                self.problem.array_index(expr_origin, target_ty)
            }
            ast::ExpressionKind::Cast { value, ty } => {
                // don't put in any type constraints, they're pretty complex and casting will destroy most of it anyway
                // TODO revisit this when we redesign the type solver (and implement separate signed and bits for int)
                let _before_ty = self.visit_expr(scope, value)?;
                let after_ty = self.resolve_type(scope, ty)?;
                self.problem.fully_known(self.types, after_ty)
            }
            ast::ExpressionKind::Return { value } => {
                let value_ty = if let Some(value) = value {
                    self.visit_expr(scope, value)?
                } else {
                    self.problem.ty_void()
                };

                let ret_ty = self.problem.fully_known(&self.types, self.ret_ty);
                self.problem.equal(ret_ty, value_ty);

                //TODO use "never" type once that exists instead, also for break and continue
                self.problem.unknown_default_void(expr_origin)
            }
            ast::ExpressionKind::Continue => self.problem.unknown_default_void(expr_origin),
            ast::ExpressionKind::Break => self.problem.unknown_default_void(expr_origin),
            ast::ExpressionKind::StructLiteral { struct_path, fields } => {
                let struct_ty = self.resolve_path_type(scope, struct_path)?;
                let struct_ty_info = if let TypeInfo::Struct(struct_ty_info) = &self.types[struct_ty] {
                    struct_ty_info.clone()
                } else {
                    return Err(Error::StructLiteralForNonStructType {
                        expr,
                        ty: self.types.format_type(struct_ty).to_string(),
                        fields: fields.iter().map(|(id, _)| id).collect(),
                    });
                };

                let fields_set: HashSet<_> = fields.iter().map(|(id, _)| &*id.string).collect();
                let expected_set: HashSet<_> = struct_ty_info.fields.iter().map(|info| info.id).collect();
                assert_eq!(expected_set.len(), struct_ty_info.fields.len());

                if fields.len() != struct_ty_info.fields.len() || fields_set != expected_set {
                    return Err(Error::StructLiteralInvalidFields {
                        expected: struct_ty_info.fields.iter().map(|info| info.id.to_owned()).collect(),
                        actual: fields.iter().map(|(id, _)| id.string.clone()).collect(),
                        expr,
                    })
                }

                // require that field types match
                for (field_id, field_value) in fields {
                    let field_value_ty = self.visit_expr(scope, field_value)?;

                    let field_index = struct_ty_info.find_field_index(&field_id.string).unwrap();
                    let field_info = &struct_ty_info.fields[field_index];

                    let field_ty = self.problem.fully_known(&self.types, field_info.ty);
                    self.problem.equal(field_ty, field_value_ty);
                }

                self.problem.fully_known(&self.types, struct_ty)
            }
            ast::ExpressionKind::BlackBox { value } => {
                self.visit_expr(scope, value)?
            }
        };

        let prev = self.expr_type_map.insert(expr as *const _, result);
        assert!(prev.is_none());

        Ok(result)
    }

    fn visit_statement(&mut self, scope: &mut Scope<ScopedItem>, stmt: &'ast ast::Statement) -> Result<'ast, ()> {
        match &stmt.kind {
            ast::StatementKind::Declaration(decl) => {
                assert!(!decl.mutable, "everything is mutable for now");
                let decl_origin = Origin::Declaration(decl);

                let expect_ty = match &decl.ty {
                    None => self.problem.unknown(decl_origin),
                    Some(ty) => {
                        let ty = self.resolve_type(scope, ty);
                        self.problem.fully_known(&self.types, ty?)
                    }
                };

                let value_ty = match &decl.init {
                    None => self.problem.unknown(decl_origin),
                    Some(init) => self.visit_expr(scope, init)?
                };

                self.problem.equal(expect_ty, value_ty);
                self.decl_type_map.insert(decl as *const _, expect_ty);

                scope.maybe_declare(&decl.id, ScopedItem::Value(ScopedValue::TypeVar(expect_ty)))?;

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
            ast::StatementKind::Loop(loop_stmt) => {
                self.visit_nested_block(scope, &loop_stmt.body)?;
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
                    None => self.problem.unknown(Origin::ForIndex(for_stmt)),
                };

                let start_ty = self.visit_expr(scope, &for_stmt.start)?;
                let end_ty = self.visit_expr(scope, &for_stmt.end)?;

                let unknown_int = self.problem.unknown_int(Origin::ForIndex(for_stmt), None);
                self.problem.equal(index_ty, unknown_int);
                self.problem.equal(index_ty, start_ty);
                self.problem.equal(index_ty, end_ty);

                let mut index_scope = scope.nest();
                index_scope.maybe_declare(&for_stmt.index, ScopedItem::Value(ScopedValue::TypeVar(index_ty)))?;

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

            scope.maybe_declare(&param.id, ScopedItem::Value(ScopedValue::TypeVar(ty_var)))?;
        }

        let body = decl.ast.body.as_ref().
            expect("can only generate code for functions with a body");
        self.visit_nested_block(&scope, body)?;

        Ok(())
    }
}
