// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Q-pattern support for do-notation matches.
//!
//! Split out of `elab_do_match.rs` to keep the main casesOn path under the
//! file-size limit while sharing the existing q-pattern matcher/runtime helpers.

use super::*;
use crate::infer::q_pattern::q_match_pattern_expr;

impl<'a> ElabCtx<'a> {
    pub(super) fn do_match_has_q_patterns(arms: &[DoMatchArm]) -> bool {
        arms.iter().any(|arm| {
            arm.patterns.iter().any(|pattern| {
                let mut aliases = Vec::new();
                q_match_pattern_expr(pattern, &mut aliases).is_some()
            })
        })
    }

    pub(super) fn elaborate_do_q_match(
        &mut self,
        scrutinee: &Expr,
        scrutinee_ty: &Expr,
        arms: &[DoMatchArm],
    ) -> Result<Expr, ElabError> {
        if self.needs_runtime_q_match(scrutinee) {
            let _ = (scrutinee_ty, arms);
            return Err(ElabError::NotImplemented(
                "runtime q-pattern do-match is not yet supported".to_string(),
            ));
        }

        let mut tried_patterns = Vec::new();

        for arm in arms {
            let pattern = match arm.patterns.as_slice() {
                [pattern] => pattern,
                _ => {
                    return Err(ElabError::NotImplemented(
                        "multi-discriminant q-pattern do-match".to_string(),
                    ));
                }
            };

            let mut aliases = Vec::new();
            if let Some(pat_expr) = q_match_pattern_expr(pattern, &mut aliases) {
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

                    let body = self.elab_do_body_with_outer_continuation(&arm.body)?;

                    for _ in &result.bindings {
                        self.pop_local();
                    }
                    for _ in &alias_fvars {
                        self.pop_local();
                    }

                    // Fix #3419: Instantiate metas before abstracting FVars.
                    let mut result_expr = self.metas.instantiate(&body);
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

                tried_patterns.push(format!("{pattern:?}"));
                continue;
            }

            match pattern {
                SurfacePattern::Wildcard => {
                    return self.elab_do_body_with_outer_continuation(&arm.body);
                }
                SurfacePattern::Var(name) => {
                    let fvar = self.push_local(name.clone(), scrutinee_ty.clone());
                    let body = self.elab_do_body_with_outer_continuation(&arm.body)?;
                    self.pop_local();
                    // Fix #3419: Instantiate metas before abstracting FVars.
                    let body_inst = self.metas.instantiate(&body);
                    let body_abs = body_inst.abstract_fvar(fvar);
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
                        "q-do-match with non-q pattern: {pattern:?}"
                    )));
                }
            }
        }

        if tried_patterns.is_empty() {
            Err(ElabError::NotImplemented(
                "q-do-match: no patterns provided".to_string(),
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
