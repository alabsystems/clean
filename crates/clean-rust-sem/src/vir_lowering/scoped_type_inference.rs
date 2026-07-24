// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scope-aware type inference helpers for VIR lowering.

use super::context::FunctionLoweringContext;
use super::type_helpers::{nominal_type_name, pattern_is_irrefutable};
use super::VirLoweringError;
use crate::expr::{Expr, MatchArm, Pattern, Stmt as SemStmt};
use crate::types::{Mutability, RustType};

/// Companion to `builtin_try_pattern_can_match` in `match_lowering.rs`:
/// keep the type-inference walk consistent with the lowering walk by
/// skipping arms whose `EnumVariant` enum-name does not match the
/// scrutinee's enum (Option / Result). The `?` operator desugar emits
/// arms for both — the lowering already filters them away; this mirrors
/// that filter so type inference does not try to bind an `Option::Some`
/// pattern against a `Result` scrutinee.
fn builtin_try_pattern_compatible(scrutinee_ty: &RustType, pattern: &Pattern) -> bool {
    match pattern {
        Pattern::EnumVariant { enum_name, .. } => {
            let actual_enum = nominal_type_name(scrutinee_ty);
            !matches!(
                (actual_enum.as_deref(), enum_name.as_str()),
                (Some("Option"), "Result") | (Some("Result"), "Option")
            )
        }
        Pattern::Or(alternatives) => alternatives
            .iter()
            .any(|alt| builtin_try_pattern_compatible(scrutinee_ty, alt)),
        _ => true,
    }
}

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn future_output_type_of_closure(
        &self,
        params: &[(String, RustType)],
        captures: &[(String, Mutability)],
        body: &Expr,
    ) -> Option<RustType> {
        let capture_params: Vec<(String, RustType)> = captures
            .iter()
            .filter_map(|(name, _)| {
                let local = self.lookup_local(name).ok()?;
                let ty = self.local_ty(local).ok()?;
                Some((name.clone(), ty))
            })
            .collect();
        let mut full_params = capture_params;
        full_params.extend_from_slice(params);

        let visible_symbols = self.visible_symbols();
        let temp_ctx: FunctionLoweringContext<'_> = FunctionLoweringContext::new(
            self.function_name,
            &full_params,
            RustType::Unit,
            &visible_symbols,
        );
        temp_ctx.future_output_type_of_expr(body)
    }

    pub(super) fn infer_closure_body_type(
        &self,
        params: &[(String, RustType)],
        body: &Expr,
    ) -> Result<RustType, VirLoweringError> {
        let visible_symbols = self.visible_symbols();
        let temp_ctx: FunctionLoweringContext<'_> = FunctionLoweringContext::new(
            self.function_name,
            params,
            RustType::Unit,
            &visible_symbols,
        );
        temp_ctx.infer_expr_type(body)
    }

    pub(super) fn infer_block_expr_type(
        &self,
        stmts: &[SemStmt],
        expr: Option<&Expr>,
    ) -> Result<RustType, VirLoweringError> {
        let mut temp_ctx = self.fork_for_type_inference();
        temp_ctx.push_scope();
        for stmt in stmts {
            temp_ctx.observe_stmt_for_type_inference(stmt)?;
        }
        let ty = match expr {
            Some(expr) => temp_ctx.infer_expr_type(expr)?,
            None => RustType::Unit,
        };
        temp_ctx.pop_scope();
        Ok(ty)
    }

    pub(super) fn infer_match_expr_type(
        &self,
        scrutinee: &Expr,
        arms: &[MatchArm],
    ) -> Result<RustType, VirLoweringError> {
        let Some(first_arm) = arms.first() else {
            return Ok(RustType::Unit);
        };

        let scrutinee_ty = self.infer_expr_type(scrutinee)?;
        // `desugar_try_operator` emits BOTH Result-shaped and Option-shaped
        // arms because the desugar has no type information; the lowering
        // pass already filters mismatched arms via
        // `builtin_try_pattern_can_match`. Mirror that filter here so type
        // inference doesn't try to bind an `Option::Some` pattern against
        // a `Result` scrutinee. (Wave 108.)
        let arms_iter: Vec<&MatchArm> = arms
            .iter()
            .filter(|arm| builtin_try_pattern_compatible(&scrutinee_ty, &arm.pattern))
            .collect();
        let Some(&first_arm) = arms_iter.first() else {
            return Ok(RustType::Unit);
        };
        let first_ty = self.infer_match_arm_body_type(scrutinee, &scrutinee_ty, first_arm)?;
        // Track the joined type as we walk arms. `Never` (the bottom type)
        // unifies with any other type: an arm that diverges (e.g. an early
        // `return` desugaring or a `panic!`) does not constrain the
        // surrounding match's result type. This is required for the `?`
        // operator on `Option`/`Result`, whose early-return arm is
        // `Never`-typed. Wave 108.
        let mut joined_ty = first_ty;
        for arm in arms_iter.iter().skip(1) {
            let arm_ty = self.infer_match_arm_body_type(scrutinee, &scrutinee_ty, arm)?;
            joined_ty = match (&joined_ty, &arm_ty) {
                // Never-arms never widen the joined type.
                (_, RustType::Never) => joined_ty,
                // First-arm-was-Never: adopt the non-Never sibling.
                (RustType::Never, _) => arm_ty,
                _ if arm_ty.is_compatible(&joined_ty) => joined_ty,
                _ => {
                    return Err(VirLoweringError::Unsupported {
                        context: "match expression",
                        detail: format!(
                            "match arms must share a type, got `{joined_ty:?}` and `{arm_ty:?}`"
                        ),
                    });
                }
            };
        }
        Ok(joined_ty)
    }

    fn infer_match_arm_body_type(
        &self,
        scrutinee_expr: &Expr,
        scrutinee_ty: &RustType,
        arm: &MatchArm,
    ) -> Result<RustType, VirLoweringError> {
        let mut temp_ctx = self.fork_for_type_inference();
        temp_ctx.push_scope();
        let scrutinee_local = temp_ctx.alloc_local(None, scrutinee_ty.clone(), Mutability::Mutable);
        // Propagate async metadata so pattern bindings in the arm can discover
        // callable/future output types carried by the scrutinee expression.
        if let Some(output_ty) = temp_ctx.callable_future_output_type_of_expr(scrutinee_expr) {
            temp_ctx.remember_callable_future_output(scrutinee_local, output_ty);
        }
        if let Some(output_ty) = temp_ctx.future_output_type_of_expr(scrutinee_expr) {
            temp_ctx.remember_future_output(scrutinee_local, output_ty);
        }
        temp_ctx.bind_pattern(
            crate::ownership::Place::Local(scrutinee_local),
            &arm.pattern,
        )?;
        if let Some(guard) = &arm.guard {
            let guard_ty = temp_ctx.infer_expr_type(guard)?;
            if guard_ty != RustType::Bool {
                return Err(VirLoweringError::Unsupported {
                    context: "match guard",
                    detail: format!("guard must be boolean, got `{guard_ty:?}`"),
                });
            }
        }
        let body_ty = temp_ctx.infer_expr_type(&arm.body)?;
        temp_ctx.pop_scope();
        Ok(body_ty)
    }

    fn observe_stmt_for_type_inference(&mut self, stmt: &SemStmt) -> Result<(), VirLoweringError> {
        match stmt {
            SemStmt::Let {
                pattern,
                ty,
                init,
                else_block,
            } => self.observe_let_for_type_inference(
                pattern,
                ty.as_ref(),
                init.as_deref(),
                else_block.as_deref(),
            ),
            SemStmt::Expr(expr) => {
                let _ = self.infer_expr_type(expr)?;
                Ok(())
            }
            SemStmt::Item(item) => self.register_scoped_item(item),
        }
    }

    fn observe_let_for_type_inference(
        &mut self,
        pattern: &Pattern,
        ty: Option<&RustType>,
        init: Option<&Expr>,
        else_block: Option<&Expr>,
    ) -> Result<(), VirLoweringError> {
        let future_output_ty = init.and_then(|expr| self.future_output_type_of_expr(expr));
        let callable_future_output_ty =
            init.and_then(|expr| self.callable_future_output_type_of_expr(expr));
        let init_ty = match ty {
            Some(ty) => ty.clone(),
            None => match init {
                Some(expr) => self.infer_expr_type(expr)?,
                None => {
                    return Err(VirLoweringError::MissingType {
                        context: format!(
                            "binding pattern in `{}` without annotation or initializer",
                            self.function_name
                        ),
                    });
                }
            },
        };

        if else_block.is_none() && !pattern_is_irrefutable(pattern) {
            return Err(VirLoweringError::Unsupported {
                context: "let binding",
                detail: format!("refutable pattern `{pattern:?}` requires let-else lowering"),
            });
        }

        if let Some(else_expr) = else_block {
            let _ = self.infer_expr_type(else_expr)?;
        }

        if let Pattern::Binding {
            name,
            mutable,
            subpattern: None,
        } = pattern
        {
            let local = self.declare_binding(
                name,
                init_ty,
                if *mutable {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                },
            )?;
            if let Some(output_ty) = future_output_ty {
                self.remember_future_output(local, output_ty);
            }
            if let Some(output_ty) = callable_future_output_ty {
                self.remember_callable_future_output(local, output_ty);
            }
            return Ok(());
        }

        let init_local = self.alloc_local(None, init_ty, Mutability::Mutable);
        if let Some(output_ty) = future_output_ty {
            self.remember_future_output(init_local, output_ty);
        }
        if let Some(output_ty) = callable_future_output_ty {
            self.remember_callable_future_output(init_local, output_ty);
        }
        self.bind_pattern(crate::ownership::Place::Local(init_local), pattern)?;
        Ok(())
    }
}
