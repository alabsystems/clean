// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern elaboration with metavariables and static matching.
//!
//! Handles elaboration of q-patterns into kernel expressions and
//! static matching at elaboration time using unification.

use super::super::{ElabCtx, ElabError};
use super::{extract::QPatternMatchResult, q_match_pattern_expr};
use crate::stack_safe;
use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::{Expr, ExprKind, FVarId, Name};
use clean_parser::{QAntiquotContent, SurfaceExpr, SurfacePattern};
use std::collections::HashMap;

impl<'a> ElabCtx<'a> {
    /// Elaborate a q-pattern, replacing pattern variables with fresh metavariables
    ///
    /// Returns (elaborated_pattern, mvar_map) where mvar_map maps pattern variable
    /// names to their corresponding metavariable FVarIds.
    pub(in crate::infer) fn elaborate_q_pattern_with_mvars(
        &mut self,
        pattern: &SurfaceExpr,
    ) -> Result<(Expr, HashMap<String, FVarId>), ElabError> {
        let mut mvar_map = HashMap::new();
        let expr = self.elaborate_q_pattern_inner(pattern, &mut mvar_map)?;
        Ok((expr, mvar_map))
    }

    /// Inner helper for elaborating q-patterns with metavariable tracking
    fn elaborate_q_pattern_inner(
        &mut self,
        pattern: &SurfaceExpr,
        mvar_map: &mut HashMap<String, FVarId>,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| match pattern {
            SurfaceExpr::QAntiquot { content, .. } => {
                match content {
                    QAntiquotContent::Simple(name) => {
                        // Reuse existing metavariable if name already bound (#317)
                        // This enforces equality when the same $x appears multiple times
                        if let Some(fvar_id) = mvar_map.get(name) {
                            return Ok(Expr::fvar(*fvar_id));
                        }

                        // Create fresh metavariable for this pattern variable
                        // Use fresh universe parameter for type flexibility (#318)
                        let u = self.fresh_universe_param();
                        let mvar_ty = self.fresh_meta(Expr::sort(u));
                        let mvar = self.fresh_meta(mvar_ty);

                        // Get the FVarId from the metavariable
                        if let ExprKind::FVar(fvar_id) = mvar.kind() {
                            mvar_map.insert(name.clone(), *fvar_id);
                        }
                        Ok(mvar)
                    }

                    QAntiquotContent::Typed { name, ty } => {
                        // Reuse existing metavariable if name already bound (#317)
                        // Note: If name was first bound as Simple, the type annotation here
                        // is effectively ignored. This matches quote4 behavior where the
                        // first occurrence determines the binding.
                        if let Some(fvar_id) = mvar_map.get(name) {
                            return Ok(Expr::fvar(*fvar_id));
                        }

                        // Pattern variable with explicit type
                        let ty_expr = self.elaborate(ty)?;
                        let mvar = self.fresh_meta(ty_expr);

                        if let ExprKind::FVar(fvar_id) = mvar.kind() {
                            mvar_map.insert(name.clone(), *fvar_id);
                        }
                        Ok(mvar)
                    }

                    QAntiquotContent::Expr(inner) => {
                        // $(expr) - elaborate and match exactly
                        self.elaborate(inner)
                    }

                    QAntiquotContent::Splice { name, .. } => {
                        // $[xs]* - splice pattern: binds to a list of expressions
                        // For now, treat as a simple variable binding; the match logic
                        // will handle iterating over sequences
                        if let Some(fvar_id) = mvar_map.get(name) {
                            return Ok(Expr::fvar(*fvar_id));
                        }

                        let u = self.fresh_universe_param();
                        let mvar_ty = self.fresh_meta(Expr::sort(u));
                        let mvar = self.fresh_meta(mvar_ty);

                        if let ExprKind::FVar(fvar_id) = mvar.kind() {
                            mvar_map.insert(name.clone(), *fvar_id);
                        }
                        Ok(mvar)
                    }
                }
            }

            SurfaceExpr::App(_, func, args) => {
                let func_expr = self.elaborate_q_pattern_inner(func, mvar_map)?;
                let mut result = func_expr;
                for arg in args {
                    let arg_expr = self.elaborate_q_pattern_inner(&arg.expr, mvar_map)?;
                    result = Expr::app(result, arg_expr);
                }
                Ok(result)
            }

            SurfaceExpr::Paren(_, inner) => self.elaborate_q_pattern_inner(inner, mvar_map),

            // For non-antiquotation expressions, delegate to normal elaboration
            _ => self.elaborate(pattern),
        })
    }

    /// Match a scrutinee against a q-pattern, returning bindings if successful
    ///
    /// Uses definitional equality (isDefEq/unification) to match, following
    /// quote4 semantics where patterns match by definitional equality.
    pub(in crate::infer) fn match_q_pattern(
        &mut self,
        scrutinee: &Expr,
        pattern_expr: &SurfaceExpr,
    ) -> Result<Option<QPatternMatchResult>, ElabError> {
        // 1. Extract pattern variables for result binding
        let pat_vars = self.extract_q_pattern_vars(pattern_expr);

        // 2. Push scope for potential rollback
        self.metas.push_scope();

        // 3. Elaborate pattern with fresh metavariables
        let (pattern, mvar_map) = match self.elaborate_q_pattern_with_mvars(pattern_expr) {
            Ok(result) => result,
            Err(e) => {
                // Elaboration failed - rollback scope before propagating error
                self.metas.pop_scope();
                return Err(e);
            }
        };

        // 4. Try unification (isDefEq) with reducible transparency
        let ctx = self.build_local_ctx();
        let unify_result = {
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            unifier.unify(scrutinee, &pattern)
        };
        match unify_result {
            UnifyResult::Success => {}
            UnifyResult::Failure(_) | UnifyResult::Stuck => {
                // Pattern doesn't match - restore metavariable state
                self.metas.pop_scope();
                return Ok(None);
            }
        }

        // 5. Extract bindings from metavariable assignments
        let mut bindings = Vec::new();
        for (var_name, _type_annot) in pat_vars {
            if let Some(fvar_id) = mvar_map.get(&var_name) {
                // Get the metavariable's assigned value
                if let Some(meta_id) = MetaState::from_fvar(*fvar_id) {
                    if let Some(val) = self.metas.get_assignment(meta_id) {
                        let val = val.clone();
                        let ty = match self.infer_type(&val) {
                            Ok(ty) => ty,
                            Err(e) => {
                                // Type inference failed - rollback scope before propagating error
                                self.metas.pop_scope();
                                return Err(e);
                            }
                        };
                        bindings.push((var_name, val, ty));
                    } else {
                        // Metavariable not assigned - pattern not fully determined
                        self.metas.pop_scope();
                        return Ok(None);
                    }
                }
            }
        }

        // Commit scope - pattern match succeeded
        self.metas.commit();
        Ok(Some(QPatternMatchResult { bindings }))
    }

    /// Check if a match has any q-patterns
    pub(in crate::infer) fn has_q_patterns(&self, arms: &[clean_parser::SurfaceMatchArm]) -> bool {
        arms.iter().any(|arm| {
            let mut aliases = Vec::new();
            q_match_pattern_expr(&arm.pattern, &mut aliases).is_some()
        })
    }

    /// Determine if a q-match scrutinee requires runtime evaluation
    ///
    /// Part of #23: Qq Phase 4 - Runtime pattern matching
    ///
    /// Static matching (Phase 3) works when the scrutinee can be fully evaluated
    /// at elaboration time. Runtime matching (Phase 4) is needed when:
    /// - Scrutinee is a free variable (function parameter)
    /// - Scrutinee is a metavariable that hasn't been assigned
    /// - Scrutinee is an application of a free variable
    pub(in crate::infer) fn needs_runtime_q_match(&self, scrutinee: &Expr) -> bool {
        stack_safe(|| match scrutinee.kind() {
            // Free variable - might be a function parameter
            ExprKind::FVar(fvar_id) => {
                // Check if it's a metavariable (internal) or a real local
                // Metavariables might still be solvable statically
                if let Some(meta_id) = MetaState::from_fvar(*fvar_id) {
                    // It's a metavariable - check if it's assigned
                    if self.metas.get_assignment(meta_id).is_some() {
                        // Assigned metavariable - can be evaluated statically
                        return false;
                    }
                    // Unassigned metavariable - needs runtime
                    true
                } else {
                    // Real local variable - definitely needs runtime
                    true
                }
            }

            // Application - check if head is a free variable
            ExprKind::App(func, _) => self.needs_runtime_q_match(func),

            // Let binding - check the body after substitution would need runtime
            ExprKind::Let(_, _, val, body, _) => {
                // If value needs runtime, the whole let needs runtime
                // This is conservative - we could be smarter here
                self.needs_runtime_q_match(val) || {
                    // Check if body would need runtime if we substituted
                    // For now, be conservative and check the body as-is
                    self.needs_runtime_q_match(body)
                }
            }

            // All other expressions can be evaluated statically
            _ => false,
        })
    }

    /// Elaborate a match expression with q-patterns
    ///
    /// Q-patterns compile to runtime pattern matching using expression comparison,
    /// unlike casesOn which uses constructor-based dispatch.
    ///
    /// Part of #23: Qq Phase 4 - Runtime pattern matching
    ///
    /// This function dispatches between:
    /// - Static matching (Phase 3): scrutinee can be evaluated at elaboration time
    /// - Runtime matching (Phase 4): scrutinee is dynamic (e.g., function parameter)
    pub(in crate::infer) fn elaborate_q_match(
        &mut self,
        scrutinee: &Expr,
        scrutinee_ty: &Expr,
        arms: &[clean_parser::SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        // Phase 4: Check if scrutinee requires runtime matching
        if self.needs_runtime_q_match(scrutinee) {
            return self.elaborate_runtime_q_match(scrutinee, scrutinee_ty, arms);
        }

        // Phase 3: Static matching at elaboration time
        // For q-matches, we elaborate each arm and use the first one that matches
        // at elaboration time.

        let mut tried_patterns: Vec<String> = Vec::new();

        for arm in arms {
            let mut aliases = Vec::new();
            if let Some(pat_expr) = q_match_pattern_expr(&arm.pattern, &mut aliases) {
                // Try to match the pattern.
                let match_result = self.match_q_pattern(scrutinee, pat_expr)?;

                if let Some(result) = match_result {
                    let mut alias_fvars = Vec::new();
                    for alias in &aliases {
                        alias_fvars
                            .push(self.push_local((*alias).to_string(), scrutinee_ty.clone()));
                    }

                    for (name, _val, ty) in &result.bindings {
                        self.push_local(name.clone(), ty.clone());
                    }

                    let body = self.elaborate(&arm.body)?;

                    // Pop locals in reverse order.
                    for _ in &result.bindings {
                        self.pop_local();
                    }
                    for _ in &alias_fvars {
                        self.pop_local();
                    }

                    // Build let bindings for q-pattern variables, then wrap any
                    // `name @ q(...)` aliases around the matched scrutinee.
                    let mut result_expr = body;
                    for (binding_name, val, ty) in result.bindings.into_iter().rev() {
                        result_expr = Expr::let_named(
                            Name::from_string(&binding_name),
                            ty,
                            val,
                            result_expr,
                            false,
                        );
                    }
                    for alias_fvar in alias_fvars.iter().rev() {
                        result_expr = Expr::let_named(
                            Name::anon(),
                            scrutinee_ty.clone(),
                            scrutinee.clone(),
                            result_expr.abstract_fvar(*alias_fvar),
                            false,
                        );
                    }

                    return Ok(result_expr);
                }
                // Pattern doesn't match - record it for error message.
                tried_patterns.push(format!("{:?}", arm.pattern));
                continue;
            }

            match &arm.pattern {
                SurfacePattern::Wildcard => {
                    // Wildcard catches all
                    return self.elaborate(&arm.body);
                }

                SurfacePattern::Var(name) => {
                    // Variable pattern - bind scrutinee to name
                    let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let body = self.elaborate(&arm.body)?;
                    self.pop_local();
                    let body_abs = body.abstract_fvar(fvar);
                    return Ok(Expr::let_named(
                        Name::from_string(name),
                        scrutinee_ty.clone(),
                        scrutinee.clone(),
                        body_abs,
                        false,
                    ));
                }

                _ => {
                    return Err(ElabError::NotImplemented(format!(
                        "q-match with non-q pattern: {:?}",
                        arm.pattern
                    )));
                }
            }
        }

        // No arm matched - provide helpful error message
        if tried_patterns.is_empty() {
            Err(ElabError::NotImplemented(
                "q-match: no patterns provided".to_string(),
            ))
        } else {
            Err(ElabError::TypeMismatch {
                expected: format!("scrutinee to match one of: {}", tried_patterns.join(", ")),
                actual: format!(
                    "scrutinee {:?} of type {:?} did not match any q-pattern. \
                    Consider adding a wildcard pattern `| _ => ...`",
                    scrutinee, scrutinee_ty
                ),
            })
        }
    }
}
