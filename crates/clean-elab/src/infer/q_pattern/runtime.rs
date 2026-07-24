// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime q-pattern matching and let-pattern desugaring.
//!
//! Handles patterns that cannot be resolved statically at elaboration time,
//! generating runtime isDefEq checks and let-pattern desugaring.

use super::super::{ElabCtx, ElabError};
use super::q_match_pattern_expr;
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};
use clean_parser::{Span, SurfaceExpr, SurfaceMatchArm, SurfacePattern};
use std::collections::HashMap;

impl<'a> ElabCtx<'a> {
    /// Elaborate a q-match with runtime pattern matching
    ///
    /// Part of #23: Qq Phase 4 - Runtime pattern matching
    ///
    /// This generates code that performs pattern matching at runtime using
    /// `isDefEq` checks. The generated code has the form:
    ///
    /// ```text
    /// if isDefEq(scrutinee, pattern1) then
    ///   let a := getMVar(mvar_a) in
    ///   let b := getMVar(mvar_b) in
    ///   body1
    /// else if isDefEq(scrutinee, pattern2) then
    ///   ...
    /// else
    ///   fallback
    /// ```
    ///
    /// In Lean 4/quote4, this requires MetaM context. We generate a simplified
    /// representation that can be interpreted by our runtime or compiled to
    /// actual MetaM calls.
    pub(in crate::infer) fn elaborate_runtime_q_match(
        &mut self,
        scrutinee: &Expr,
        scrutinee_ty: &Expr,
        arms: &[SurfaceMatchArm],
    ) -> Result<Expr, ElabError> {
        // Build the match from back to front (innermost else first)
        let mut result: Option<Expr> = None;

        for arm in arms.iter().rev() {
            let mut aliases = Vec::new();
            if let Some(pat_expr) = q_match_pattern_expr(&arm.pattern, &mut aliases) {
                // Q-pattern needs runtime isDefEq check.
                let (check_expr, bindings_info) =
                    self.gen_runtime_q_check(scrutinee, scrutinee_ty, pat_expr)?;

                let mut alias_fvars = Vec::new();
                for alias in &aliases {
                    alias_fvars.push(self.push_local((*alias).to_string(), scrutinee_ty.clone()));
                }

                // Elaborate the body with pattern variables in scope.
                for (name, ty) in &bindings_info {
                    self.push_local(name.clone(), ty.clone());
                }
                let body = self.elaborate(&arm.body)?;

                // Pop locals in reverse order.
                for _ in &bindings_info {
                    self.pop_local();
                }
                for _ in &alias_fvars {
                    self.pop_local();
                }

                // Wrap body with runtime q bindings, then any `name @ q(...)`
                // aliases that bind the whole scrutinee.
                let mut arm_expr = self.wrap_with_runtime_bindings(body, &bindings_info);
                for alias_fvar in alias_fvars.iter().rev() {
                    arm_expr = Expr::let_named(
                        Name::anon(),
                        scrutinee_ty.clone(),
                        scrutinee.clone(),
                        arm_expr.abstract_fvar(*alias_fvar),
                        false,
                    );
                }

                let alt = result.unwrap_or_else(|| {
                    // No fallback - runtime error
                    // In practice, users should always have a wildcard pattern
                    self.mk_runtime_match_failure(scrutinee, scrutinee_ty)
                });

                result = Some(self.mk_runtime_if(check_expr, arm_expr, alt));
                continue;
            }

            match &arm.pattern {
                SurfacePattern::Wildcard => {
                    // Wildcard is the fallback - just elaborate the body
                    let body = self.elaborate(&arm.body)?;
                    result = Some(body);
                }

                SurfacePattern::Var(name) => {
                    // Variable pattern binds the scrutinee
                    let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let body = self.elaborate(&arm.body)?;
                    self.pop_local();
                    let body_abs = body.abstract_fvar(fvar);
                    let arm_expr = Expr::let_named(
                        Name::from_string(name),
                        scrutinee_ty.clone(),
                        scrutinee.clone(),
                        body_abs,
                        false,
                    );
                    result = Some(arm_expr);
                }

                _ => {
                    return Err(ElabError::NotImplemented(format!(
                        "runtime q-match with pattern: {:?}",
                        arm.pattern
                    )));
                }
            }
        }

        result.ok_or_else(|| {
            ElabError::NotImplemented("runtime q-match: no arms provided".to_string())
        })
    }

    /// Generate a runtime isDefEq check for a q-pattern
    ///
    /// Returns (check_expression, pattern_variable_bindings)
    /// where check_expression evaluates to Bool at runtime.
    fn gen_runtime_q_check(
        &mut self,
        scrutinee: &Expr,
        _scrutinee_ty: &Expr,
        pattern_expr: &SurfaceExpr,
    ) -> Result<(Expr, Vec<(String, Expr)>), ElabError> {
        // Extract pattern variables
        let pat_vars = self.extract_q_pattern_vars(pattern_expr);

        // Elaborate pattern with fresh metavariables
        let (pattern, mvar_map) = self.elaborate_q_pattern_with_mvars(pattern_expr)?;

        // Build bindings info: pattern variable name -> type
        let mut bindings_info = Vec::new();
        for (var_name, _type_annot) in &pat_vars {
            if let Some(fvar_id) = mvar_map.get(var_name) {
                // Get the metavariable's type
                if let Some(meta_id) = MetaState::from_fvar(*fvar_id) {
                    if let Some(meta) = self.metas.get(meta_id) {
                        bindings_info.push((var_name.clone(), meta.ty.clone()));
                    }
                }
            }
        }

        // Generate the isDefEq check expression
        // This is a special expression that represents: isDefEq(scrutinee, pattern)
        //
        // We use an MData wrapper to tag this as a runtime pattern check.
        // The runtime or codegen can interpret this appropriately.
        let check_expr = self.mk_is_def_eq_check(scrutinee.clone(), pattern, mvar_map);

        Ok((check_expr, bindings_info))
    }

    /// Create an isDefEq check expression
    ///
    /// This generates a representation of `isDefEq(scrutinee, pattern)` that
    /// can be evaluated at runtime. The `mvar_map` provides the mapping from
    /// pattern variable names to their metavariable FVarIds, which the runtime
    /// needs to extract binding values after successful unification.
    fn mk_is_def_eq_check(
        &mut self,
        scrutinee: Expr,
        pattern: Expr,
        mvar_map: HashMap<String, FVarId>,
    ) -> Expr {
        use clean_kernel::MDataValue;

        // Create a special marker expression for runtime pattern matching
        // Using MData with a "qq_runtime_check" tag
        //
        // The structure is: MData("qq_runtime_check", App(App(scrutinee), pattern))
        // This can be interpreted by the runtime system.

        // Build the check as a pair: (scrutinee, pattern)
        // The runtime will call isDefEq on these
        // Prod.mk.{u, v} is universe-polymorphic
        let prod_mk = self.mk_const_str("Prod.mk");
        let pair = Expr::app(Expr::app(prod_mk, scrutinee), pattern);

        // Build metadata with:
        // 1. Main tag: qq_runtime_check = true
        // 2. Binding entries: qq_binding_<varname> = fvar_id (as Nat)
        //
        // The runtime uses these binding entries to map variable names to
        // metavariable FVarIds for extracting assignments after isDefEq succeeds.
        let mut metadata = vec![(
            Name::from_string("qq_runtime_check"),
            MDataValue::Bool(true),
        )];

        // Add binding metadata for each pattern variable
        for (var_name, fvar_id) in &mvar_map {
            metadata.push((
                Name::from_string(&format!("qq_binding_{}", var_name)),
                MDataValue::Nat(fvar_id.as_u64()),
            ));
        }

        Expr::mdata(metadata, pair)
    }

    /// Wrap a body expression with runtime pattern variable bindings
    fn wrap_with_runtime_bindings(&self, body: Expr, bindings_info: &[(String, Expr)]) -> Expr {
        use clean_kernel::MDataValue;
        use std::sync::Arc;

        // For now, we create let bindings that will be filled in by the runtime
        // The runtime extracts metavariable values after successful isDefEq
        let mut result = body;

        for (name, ty) in bindings_info.iter().rev() {
            // Create a placeholder that the runtime will replace
            // Using MData to tag the binding extraction
            let metadata = vec![(
                Name::from_string("qq_runtime_binding"),
                MDataValue::String(Arc::from(name.as_str())),
            )];
            let placeholder = Expr::mdata(
                metadata,
                Expr::const_(Name::from_string("Lean.Expr.hole"), vec![]),
            );

            result = Expr::let_named(
                Name::from_string(name),
                ty.clone(),
                placeholder,
                result,
                false,
            );
        }

        result
    }

    /// Create a runtime if-then-else expression
    fn mk_runtime_if(&mut self, cond: Expr, then_branch: Expr, else_branch: Expr) -> Expr {
        // Standard if-then-else using ite or if
        // We use a special form that the runtime can interpret
        // ite.{u} is universe-polymorphic
        let ite = self.mk_const_str("ite");
        Expr::app(Expr::app(Expr::app(ite, cond), then_branch), else_branch)
    }

    /// Create a runtime match failure expression
    fn mk_runtime_match_failure(&self, scrutinee: &Expr, scrutinee_ty: &Expr) -> Expr {
        use clean_kernel::MDataValue;

        // Generate a panic/unreachable for match failure
        // In practice, users should add wildcard patterns
        let metadata = vec![(
            Name::from_string("qq_match_failure"),
            MDataValue::Bool(true),
        )];
        // Store debug info as a separate key if needed (for now we just use a flag)
        let _ = (scrutinee, scrutinee_ty); // suppress unused warnings
        Expr::mdata(
            metadata,
            Expr::const_(Name::from_string("Lean.Expr.panic"), vec![]),
        )
    }

    /// Elaborate a let-pattern expression
    ///
    /// Syntax: `let <pattern> := scrutinee | fallback in body`
    ///
    /// Supported patterns:
    /// - `q($pat)` - Q-pattern matching on quoted expressions (Phase 4)
    /// - `x` - Variable binding (always matches, fallback ignored)
    /// - `_` - Wildcard (always matches, fallback ignored, evaluates for effects)
    /// - Complex patterns (Ctor, Lit, As, Or, NumeralAdd) - Desugared to match expression
    ///
    /// Part of #23: Qq Phase 4 - let-pattern support
    /// Part of #751: Non-q-pattern let-pattern elaboration
    pub(in crate::infer) fn elaborate_let_q_pattern(
        &mut self,
        pattern: &SurfacePattern,
        scrutinee: &SurfaceExpr,
        fallback: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Elaborate scrutinee
        let scrutinee_expr = self.elaborate(scrutinee)?;
        let scrutinee_ty = self.infer_type(&scrutinee_expr)?;

        // Check if this is a q-pattern
        match pattern {
            SurfacePattern::QPattern(pat_expr) => {
                // Check if we need runtime matching
                if self.needs_runtime_q_match(&scrutinee_expr) {
                    // Generate runtime check and bindings
                    let (check_expr, bindings_info) =
                        self.gen_runtime_q_check(&scrutinee_expr, &scrutinee_ty, pat_expr)?;

                    // Elaborate the body with pattern variables in scope
                    for (name, ty) in &bindings_info {
                        self.push_local(name.clone(), ty.clone());
                    }
                    let body_expr = self.elaborate(body)?;

                    // Pop locals in reverse order
                    for _ in &bindings_info {
                        self.pop_local();
                    }

                    // Wrap body with let bindings for pattern variables
                    let body_with_bindings =
                        self.wrap_with_runtime_bindings(body_expr, &bindings_info);

                    // Elaborate fallback
                    let fallback_expr = self.elaborate(fallback)?;

                    // Build if-then-else
                    Ok(self.mk_runtime_if(check_expr, body_with_bindings, fallback_expr))
                } else {
                    // Static matching - try to match at elaboration time
                    let match_result = self.match_q_pattern(&scrutinee_expr, pat_expr)?;

                    if let Some(result) = match_result {
                        // Pattern matches - bind variables and elaborate body
                        for (name, _val, ty) in &result.bindings {
                            self.push_local(name.clone(), ty.clone());
                        }

                        let body_expr = self.elaborate(body)?;

                        // Pop locals in reverse order
                        for _ in &result.bindings {
                            self.pop_local();
                        }

                        // Build let bindings for pattern variables
                        let mut result_expr = body_expr;
                        for (binding_name, val, ty) in result.bindings.into_iter().rev() {
                            result_expr = Expr::let_named(
                                Name::from_string(&binding_name),
                                ty,
                                val,
                                result_expr,
                                false,
                            );
                        }

                        Ok(result_expr)
                    } else {
                        // Pattern doesn't match - use fallback
                        self.elaborate(fallback)
                    }
                }
            }
            SurfacePattern::Var(name) => {
                // Simple variable binding: let x := scrutinee | fallback in body
                // Fallback is ignored for variable patterns (always matches)
                // Part of #751: Non-q-pattern let-pattern elaboration
                let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                let body_expr = self.elaborate(body)?;
                self.pop_local();
                let body_abs = body_expr.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    Name::from_string(name),
                    scrutinee_ty,
                    scrutinee_expr,
                    body_abs,
                    false,
                ))
            }
            SurfacePattern::Wildcard => {
                // Wildcard pattern: let _ := scrutinee | fallback in body
                // Fallback is ignored (always matches), scrutinee is evaluated for effects
                // Part of #751: Non-q-pattern let-pattern elaboration
                let body_expr = self.elaborate(body)?;
                Ok(Expr::let_named(
                    Name::from_string("_"),
                    scrutinee_ty,
                    scrutinee_expr,
                    body_expr,
                    true,
                ))
            }
            _ => {
                // Complex patterns (Ctor, Lit, NumeralAdd, As, Or) require match expression
                // Desugar: let pat := scrutinee | fallback in body
                //       => let __letpat_scrutinee := scrutinee in
                //          match __letpat_scrutinee with | pat => body | _ => fallback
                // Part of #751: Non-q-pattern let-pattern elaboration
                //
                // We bind the elaborated scrutinee to a synthetic variable, then build
                // a match on that variable. This avoids re-elaborating the scrutinee.
                let match_arms = vec![
                    SurfaceMatchArm {
                        span: Span::dummy(),
                        pattern: pattern.clone(),
                        body: body.clone(),
                    },
                    SurfaceMatchArm {
                        span: Span::dummy(),
                        pattern: SurfacePattern::Wildcard,
                        body: fallback.clone(),
                    },
                ];

                // Create synthetic variable for the scrutinee
                let synth_var_name = "__letpat_scrutinee".to_string();
                let synth_var_expr = SurfaceExpr::Ident(Span::dummy(), synth_var_name.clone());

                // Build match expression using the synthetic variable
                let match_expr =
                    SurfaceExpr::Match(Span::dummy(), None, Box::new(synth_var_expr), match_arms);

                // Push the synthetic local with the scrutinee value and type
                let fvar = self.push_local(synth_var_name.clone(), scrutinee_ty.clone());

                // Elaborate the match expression with the synthetic variable in scope
                let match_result = self.elaborate(&match_expr)?;

                self.pop_local();

                // Abstract over the synthetic variable and wrap with let
                let match_abs = match_result.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    Name::from_string(&synth_var_name),
                    scrutinee_ty,
                    scrutinee_expr,
                    match_abs,
                    false,
                ))
            }
        }
    }
}
