// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type inference helpers for the interpreter.
//!
//! Static (associated) functions on `Interpreter` that infer types from
//! expression structure without requiring interpreter state.

use crate::expr::{EvalResult, Expr, MatchArm, Stmt};
use crate::types::{ConstGenericArg, Mutability, RustType, TypeParamDef};
use crate::values::Value;
use std::collections::HashMap;

use super::Interpreter;

pub(super) fn contains_type_param(ty: &RustType) -> bool {
    match ty {
        RustType::TypeParam(_) => true,
        RustType::Reference { inner, .. }
        | RustType::RawPtr { inner, .. }
        | RustType::Slice { elem: inner }
        | RustType::Box { inner }
        | RustType::Cell { inner }
        | RustType::RefCell { inner }
        | RustType::UnsafeCell { inner }
        | RustType::Atomic { inner }
        | RustType::Pin { inner }
        | RustType::Option { inner } => contains_type_param(inner),
        RustType::Array { element, .. } | RustType::Vec { element } => contains_type_param(element),
        RustType::Tuple(elems) => elems.iter().any(contains_type_param),
        RustType::Function { params, ret } | RustType::Closure { params, ret, .. } => {
            params.iter().any(contains_type_param) || contains_type_param(ret)
        }
        RustType::Named { type_args, .. } => type_args.iter().any(contains_type_param),
        RustType::Result { ok, err } => contains_type_param(ok) || contains_type_param(err),
        RustType::TypeProjection {
            self_ty,
            assoc_type_args,
            ..
        } => contains_type_param(self_ty) || assoc_type_args.iter().any(contains_type_param),
        RustType::Unit
        | RustType::Never
        | RustType::Bool
        | RustType::Char
        | RustType::Uint(_)
        | RustType::Int(_)
        | RustType::Float(_)
        | RustType::Str
        | RustType::DynTrait { .. }
        | RustType::ImplTrait { .. }
        | RustType::Infer => false,
    }
}

impl Interpreter {
    pub(super) fn normalized_runtime_type(&self, ty: &RustType) -> RustType {
        self.ctx.normalize_type(ty).erase_anonymous_lifetimes()
    }

    pub(super) fn infer_type_param_subst(
        &self,
        expected: &RustType,
        actual: &RustType,
        subst: &mut HashMap<u32, RustType>,
    ) -> bool {
        match expected {
            RustType::TypeParam(crate::types::TypeVar { id, .. }) => {
                if let Some(existing) = subst.get(id) {
                    existing == actual
                } else {
                    subst.insert(*id, actual.clone());
                    true
                }
            }
            RustType::Reference {
                mutability, inner, ..
            } => match actual {
                RustType::Reference {
                    mutability: actual_mutability,
                    inner: actual_inner,
                    ..
                } if actual_mutability == mutability
                    || (*mutability == Mutability::Shared
                        && *actual_mutability == Mutability::Mutable) =>
                {
                    self.infer_type_param_subst(inner, actual_inner, subst)
                }
                _ => false,
            },
            RustType::RawPtr { mutability, inner } => match actual {
                RustType::RawPtr {
                    mutability: actual_mutability,
                    inner: actual_inner,
                } if actual_mutability == mutability => {
                    self.infer_type_param_subst(inner, actual_inner, subst)
                }
                _ => false,
            },
            RustType::Array { element, len } => match actual {
                RustType::Array {
                    element: actual_element,
                    len: actual_len,
                } if actual_len == len => {
                    self.infer_type_param_subst(element, actual_element, subst)
                }
                _ => false,
            },
            RustType::Slice { elem } => match actual {
                RustType::Slice {
                    elem: actual_element,
                } => self.infer_type_param_subst(elem, actual_element, subst),
                RustType::Array {
                    element: actual_element,
                    ..
                } => self.infer_type_param_subst(elem, actual_element, subst),
                _ => false,
            },
            RustType::Tuple(expected_elems) => match actual {
                RustType::Tuple(actual_elems) if expected_elems.len() == actual_elems.len() => {
                    expected_elems.iter().zip(actual_elems.iter()).all(
                        |(expected_elem, actual_elem)| {
                            self.infer_type_param_subst(expected_elem, actual_elem, subst)
                        },
                    )
                }
                _ => false,
            },
            RustType::Function {
                params: expected_params,
                ret: expected_ret,
            } => match actual {
                RustType::Function {
                    params: actual_params,
                    ret: actual_ret,
                } if expected_params.len() == actual_params.len() => {
                    expected_params.iter().zip(actual_params.iter()).all(
                        |(expected_param, actual_param)| {
                            self.infer_type_param_subst(expected_param, actual_param, subst)
                        },
                    ) && self.infer_type_param_subst(expected_ret, actual_ret, subst)
                }
                _ => false,
            },
            RustType::Named {
                name, type_args, ..
            } => match actual {
                RustType::Named {
                    name: actual_name,
                    type_args: actual_type_args,
                    ..
                } if actual_name == name && actual_type_args.len() == type_args.len() => type_args
                    .iter()
                    .zip(actual_type_args.iter())
                    .all(|(expected_arg, actual_arg)| {
                        self.infer_type_param_subst(expected_arg, actual_arg, subst)
                    }),
                _ => false,
            },
            RustType::Box { inner } => match actual {
                RustType::Box {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::Cell { inner } => match actual {
                RustType::Cell {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::RefCell { inner } => match actual {
                RustType::RefCell {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::UnsafeCell { inner } => match actual {
                RustType::UnsafeCell {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::Pin { inner } => match actual {
                RustType::Pin {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::Option { inner } => match actual {
                RustType::Option {
                    inner: actual_inner,
                } => self.infer_type_param_subst(inner, actual_inner, subst),
                _ => false,
            },
            RustType::Result { ok, err } => match actual {
                RustType::Result {
                    ok: actual_ok,
                    err: actual_err,
                } => {
                    self.infer_type_param_subst(ok, actual_ok, subst)
                        && self.infer_type_param_subst(err, actual_err, subst)
                }
                _ => false,
            },
            RustType::Vec { element } => match actual {
                RustType::Vec {
                    element: actual_element,
                } => self.infer_type_param_subst(element, actual_element, subst),
                _ => false,
            },
            RustType::Closure {
                params: expected_params,
                ret: expected_ret,
                ..
            } => match actual {
                RustType::Closure {
                    params: actual_params,
                    ret: actual_ret,
                    ..
                } if expected_params.len() == actual_params.len() => {
                    expected_params.iter().zip(actual_params.iter()).all(
                        |(expected_param, actual_param)| {
                            self.infer_type_param_subst(expected_param, actual_param, subst)
                        },
                    ) && self.infer_type_param_subst(expected_ret, actual_ret, subst)
                }
                _ => false,
            },
            RustType::Infer => true,
            _ => expected == actual,
        }
    }

    pub(super) fn infer_call_type_param_subst(
        &self,
        params: &[(String, RustType)],
        args: &[Value],
    ) -> HashMap<u32, RustType> {
        let actual_arg_types: Vec<_> = args.iter().map(Value::get_type).collect();
        self.infer_call_type_param_subst_from_types(params, &actual_arg_types)
    }

    pub(super) fn infer_call_type_param_subst_from_types(
        &self,
        params: &[(String, RustType)],
        actual_arg_types: &[RustType],
    ) -> HashMap<u32, RustType> {
        let mut subst = HashMap::new();
        for ((_, expected_ty), actual_ty) in params.iter().zip(actual_arg_types.iter()) {
            let expected_ty = self.normalized_runtime_type(expected_ty);
            let actual_ty = self.normalized_runtime_type(actual_ty);
            if !self.infer_type_param_subst(&expected_ty, &actual_ty, &mut subst) {
                subst.clear();
                break;
            }
        }
        subst
    }

    pub(super) fn merge_type_param_subst(
        &self,
        name: &str,
        subst: &mut HashMap<u32, RustType>,
        inferred: HashMap<u32, RustType>,
    ) -> Option<EvalResult> {
        for (id, ty) in inferred {
            if let Some(existing) = subst.get(&id) {
                if existing != &ty {
                    return Some(EvalResult::Error(format!(
                        "function {name} inferred conflicting type substitutions for param {id}"
                    )));
                }
            } else {
                subst.insert(id, ty);
            }
        }
        None
    }

    pub(super) fn validate_type_param_bounds(
        &self,
        name: &str,
        type_params: &[TypeParamDef],
        subst: &HashMap<u32, RustType>,
    ) -> Option<EvalResult> {
        for type_param in type_params {
            let Some(concrete_ty) = subst.get(&type_param.id) else {
                continue;
            };
            let concrete_ty = self
                .ctx
                .normalize_type(concrete_ty)
                .erase_anonymous_lifetimes();
            for bound in &type_param.bounds {
                if !self.type_satisfies_bound(&concrete_ty, bound) {
                    return Some(EvalResult::Error(format!(
                        "function {name} requires type parameter `{}` to implement `{bound}`, got {:?}",
                        type_param.name, concrete_ty
                    )));
                }
            }
        }
        None
    }

    pub(super) fn type_satisfies_bound(&self, ty: &RustType, bound: &str) -> bool {
        match ty {
            RustType::DynTrait {
                trait_name,
                auto_traits,
            } => trait_name == bound || auto_traits.iter().any(|auto_trait| auto_trait == bound),
            RustType::ImplTrait { traits } => traits.iter().any(|trait_name| trait_name == bound),
            _ => ty
                .name()
                .is_some_and(|type_name| self.ctx.implements_trait(&type_name, bound)),
        }
    }

    /// Infer the return type of a closure body expression.
    ///
    /// This performs a simple analysis to determine the return type:
    /// 1. If the body is a Return expression, use its value type
    /// 2. If the body is a Block, analyze the final expression
    /// 3. For other expressions, use their result type
    ///
    /// Note: This is a simplified inference. Full HM inference would be needed
    /// for complex cases with generic closures.
    pub(super) fn infer_closure_return_type(body: &Expr) -> RustType {
        match body {
            // Explicit return - the value type is the return type
            Expr::Return(Some(e)) => Self::infer_expr_type(e),
            Expr::Return(None) => RustType::Unit,

            // Block - check the final expression
            Expr::Block { stmts, expr } => {
                if let Some(final_expr) = expr {
                    Self::infer_closure_return_type(final_expr)
                } else if let Some(Stmt::Expr(e)) = stmts.last() {
                    Self::infer_expr_type(e)
                } else {
                    RustType::Unit
                }
            }

            // If expression - check both branches (should be same type)
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_ty = Self::infer_closure_return_type(then_branch);
                // Use then_branch type (assuming type checking ensures else matches)
                if else_branch.is_some() {
                    then_ty
                } else {
                    // if without else returns unit
                    RustType::Unit
                }
            }

            // Match - use first arm's body type
            Expr::Match { arms, .. } => {
                if let Some(MatchArm { body, .. }) = arms.first() {
                    Self::infer_closure_return_type(body)
                } else {
                    RustType::Unit
                }
            }

            // Loop with break value
            Expr::Loop { body, .. } => Self::find_break_type(body),

            // Default: infer from expression type
            _ => Self::infer_expr_type(body),
        }
    }

    /// Infer the type of an expression from its structure.
    pub(super) fn infer_expr_type(expr: &Expr) -> RustType {
        match expr {
            Expr::Literal(v) => v.get_type(),
            Expr::BinOp { op, left, .. } => {
                use crate::values::BinOp;
                match op {
                    // Comparison operators return bool
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        RustType::Bool
                    }
                    // Arithmetic and bitwise operators preserve operand type
                    _ => Self::infer_expr_type(left),
                }
            }
            Expr::UnOp { op, expr: operand } => {
                use crate::values::UnOp;
                match op {
                    UnOp::Not => {
                        let inner_ty = Self::infer_expr_type(operand);
                        if matches!(inner_ty, RustType::Bool) {
                            RustType::Bool
                        } else {
                            inner_ty // Bitwise not preserves type
                        }
                    }
                    UnOp::Neg => Self::infer_expr_type(operand),
                }
            }
            Expr::Deref(inner) => {
                let inner_ty = Self::infer_expr_type(inner);
                match inner_ty {
                    RustType::Reference { inner, .. }
                    | RustType::RawPtr { inner, .. }
                    | RustType::Box { inner }
                    | RustType::Pin { inner } => *inner,
                    _ => inner_ty,
                }
            }
            Expr::AddrOf { mutability, expr } => {
                let inner_ty = Self::infer_expr_type(expr);
                RustType::Reference {
                    lifetime: crate::types::Lifetime::Anonymous(0),
                    mutability: *mutability,
                    inner: Box::new(inner_ty),
                }
            }
            Expr::Tuple(elems) => {
                RustType::Tuple(elems.iter().map(Self::infer_expr_type).collect())
            }
            Expr::Array(elements) => {
                let elem_ty = elements
                    .first()
                    .map(Self::infer_expr_type)
                    .unwrap_or(RustType::Unit);
                RustType::Array {
                    element: Box::new(elem_ty),
                    len: ConstGenericArg::usize(elements.len()),
                }
            }
            Expr::ArrayRepeat { value, count } => RustType::Array {
                element: Box::new(Self::infer_expr_type(value)),
                len: ConstGenericArg::usize(*count),
            },
            Expr::Struct {
                name,
                type_args,
                const_args,
                ..
            } => RustType::Named {
                name: name.clone(),
                type_args: type_args.clone(),
                lifetime_args: vec![],
                const_args: const_args.clone(),
            },
            Expr::EnumVariant {
                enum_name,
                type_args,
                const_args,
                ..
            } => RustType::Named {
                name: enum_name.clone(),
                type_args: type_args.clone(),
                lifetime_args: vec![],
                const_args: const_args.clone(),
            },
            Expr::UnionInit { name, .. } => RustType::Named {
                name: name.clone(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
            Expr::Cast { target, .. } => target.clone(),
            Expr::AssignOp { .. } => RustType::Unit,
            // For other expressions, default to Unit (conservative)
            _ => RustType::Unit,
        }
    }

    /// Find the type of a break expression in a loop body.
    pub(super) fn find_break_type(body: &Expr) -> RustType {
        match body {
            Expr::Break { value: Some(e), .. } => Self::infer_expr_type(e),
            Expr::Break { value: None, .. } => RustType::Unit,
            Expr::Block { stmts, expr } => {
                // Check statements for break
                for stmt in stmts {
                    if let Stmt::Expr(e) = stmt {
                        let ty = Self::find_break_type(e);
                        if !matches!(ty, RustType::Unit) {
                            return ty;
                        }
                    }
                }
                // Check final expression
                if let Some(e) = expr {
                    Self::find_break_type(e)
                } else {
                    RustType::Unit
                }
            }
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                let ty = Self::find_break_type(then_branch);
                if !matches!(ty, RustType::Unit) {
                    return ty;
                }
                if let Some(else_br) = else_branch {
                    Self::find_break_type(else_br)
                } else {
                    RustType::Unit
                }
            }
            _ => RustType::Unit,
        }
    }
}
