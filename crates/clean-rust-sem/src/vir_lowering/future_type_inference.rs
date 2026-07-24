// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Future-output inference helpers for async/await lowering.

use super::context::FunctionLoweringContext;
use super::type_helpers::nominal_type_name;
use crate::expr::Expr;
use crate::types::RustType;

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn callable_future_output_type_of_expr(&self, expr: &Expr) -> Option<RustType> {
        match expr {
            Expr::Var { name, .. } => match self.lookup_local(name) {
                Ok(local) => self.callable_future_output_tys.get(&local).cloned(),
                Err(_) => self.fn_future_output_type(name).cloned(),
            },
            Expr::Closure {
                params,
                body,
                captures,
                ..
            } => self.future_output_type_of_closure(params, captures, body),
            Expr::If {
                then_branch,
                else_branch: Some(else_branch),
                ..
            } => self.merge_output_types(
                [then_branch.as_ref(), else_branch.as_ref()],
                Self::callable_future_output_type_of_expr,
            ),
            Expr::Match { arms, .. } => self.merge_output_types(
                arms.iter().map(|arm| &arm.body),
                Self::callable_future_output_type_of_expr,
            ),
            Expr::Block {
                expr: Some(tail), ..
            } => self.callable_future_output_type_of_expr(tail),
            Expr::Unsafe { block } => self.callable_future_output_type_of_expr(block),
            _ => None,
        }
    }

    pub(super) fn future_output_type_of_expr(&self, expr: &Expr) -> Option<RustType> {
        match expr {
            Expr::Async { body, .. } => self.infer_expr_type(body).ok(),
            Expr::Var { name, .. } => self
                .lookup_local(name)
                .ok()
                .and_then(|local| self.future_output_tys.get(&local).cloned()),
            Expr::Call { func, .. } => self.callable_future_output_type_of_expr(func),
            Expr::MethodCall {
                receiver, method, ..
            } => {
                let receiver_ty = self.infer_expr_type(receiver).ok()?;
                let type_name = nominal_type_name(&receiver_ty)?;
                let qualified_name = self.resolve_method_name(&type_name, method);
                self.fn_future_output_type(&qualified_name).cloned()
            }
            Expr::If {
                then_branch,
                else_branch: Some(else_branch),
                ..
            } => self.merge_output_types(
                [then_branch.as_ref(), else_branch.as_ref()],
                Self::future_output_type_of_expr,
            ),
            Expr::Match { arms, .. } => self.merge_output_types(
                arms.iter().map(|arm| &arm.body),
                Self::future_output_type_of_expr,
            ),
            Expr::Block {
                expr: Some(tail), ..
            } => self.future_output_type_of_expr(tail),
            Expr::Unsafe { block } => self.future_output_type_of_expr(block),
            _ => None,
        }
    }

    fn merge_output_types<'b>(
        &self,
        exprs: impl IntoIterator<Item = &'b Expr>,
        extract: impl Fn(&Self, &Expr) -> Option<RustType>,
    ) -> Option<RustType> {
        let mut merged: Option<RustType> = None;
        for expr in exprs {
            match extract(self, expr) {
                Some(output_ty) => match &merged {
                    Some(existing) if !existing.is_compatible(&output_ty) => return None,
                    Some(_) => {}
                    None => merged = Some(output_ty),
                },
                None if self.infer_expr_type(expr).ok() == Some(RustType::Never) => {}
                None => return None,
            }
        }
        merged
    }
}
