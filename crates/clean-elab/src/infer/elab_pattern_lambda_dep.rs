// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ledger class (88), brick B4, on the generic pass-2 path: a curried
//! pattern lambda (`fun | .Tuple a0, h => …`, the body of an equation-form
//! member of a `mutual` block) whose trailing columns are hypotheses typed by
//! the matched column.
//!
//! `elab_curried_dependent_match` matches one column and refused a pattern
//! variable in any later column ("curried dependent match: pattern variable
//! `h` … is not bound by this lowering"): trust-ir
//! `Proofs/TemplateProps.lean` `substTy_total` / `substTys_total`, whose
//! `h : refsOk σ η t = true` follows `t`. As on the single-declaration path
//! (`super::equation_dep_columns`), the trailing run of such columns is
//! generalized into the match's result type and bound per alternative with
//! `fun`, which is Lean's motive over all the discriminants: the match on
//! `t` has type `∀ h : refsOk σ η t = true, …`, specialized per constructor,
//! and is applied to the lambda's own `h`.
//!
//! Scope: exactly ONE matched column (the trust-ir shape). Several matched
//! columns would pack into a non-dependent tuple whose components the
//! generalized type cannot name; they keep the refusal.

use clean_kernel::{BinderData, Expr, FVarId};
use clean_parser::{SurfaceBinder, SurfaceExpr, SurfaceMatchArm, SurfacePattern};

use super::{ElabCtx, ElabError};

impl ElabCtx<'_> {
    /// The generalized lowering, or `None` when the shape is not one column
    /// followed by plain hypothesis columns that name it.
    pub(super) fn try_elab_curried_generalized_match(
        &mut self,
        arms: &[SurfaceMatchArm],
        peeled_arms: &[Vec<SurfacePattern>],
        eta_locals: &[(FVarId, Expr, BinderData, bool)],
    ) -> Result<Option<Expr>, ElabError> {
        let arity = eta_locals.len();
        if arity < 2 || peeled_arms.iter().any(|pats| pats.len() != arity) {
            return Ok(None);
        }
        // Every later column is bound by a plain variable or `_` in every
        // alternative; a name ordinary resolution makes a constructor is not.
        for pats in peeled_arms {
            for pat in &pats[1..] {
                match pat {
                    SurfacePattern::Wildcard => {}
                    SurfacePattern::Var(name) => {
                        if self.bare_pattern_name_is_constructor(name) != Some(false) {
                            return Ok(None);
                        }
                    }
                    _ => return Ok(None),
                }
            }
        }
        // A later column must name the matched one.
        let (matched_fvar, ref matched_ty, _, _) = eta_locals[0];
        let names_matched = eta_locals[1..].iter().any(|(_, ty, _, _)| {
            crate::tactic::hypothesis::collect_fvars(ty).contains(&matched_fvar)
        });
        if !names_matched {
            return Ok(None);
        }
        let Some(result_ty) = self.current_expected_type.clone() else {
            return Ok(None);
        };
        // `∀ (later columns), result`: the match's own type.
        let mut generalized = self.metas.instantiate(&result_ty);
        for (fvar, ty, info, _) in eta_locals[1..].iter().rev() {
            generalized = Expr::pi(*info, ty.clone(), generalized.abstract_fvar(*fvar));
        }
        let inner_arms: Vec<SurfaceMatchArm> = arms
            .iter()
            .zip(peeled_arms)
            .map(|(arm, pats)| {
                let binders = pats[1..]
                    .iter()
                    .zip(&eta_locals[1..])
                    .map(|(pat, (_, _, info, _))| {
                        let name = match pat {
                            SurfacePattern::Var(name) => name.clone(),
                            _ => clean_parser::SurfaceName::component("_", false),
                        };
                        SurfaceBinder::new_typed(name, None, surface_info(info))
                    })
                    .collect();
                SurfaceMatchArm {
                    span: arm.span,
                    pattern: pats[0].clone(),
                    body: SurfaceExpr::Lambda(arm.span, binders, Box::new(arm.body.clone())),
                }
            })
            .collect();
        let saved = self.current_expected_type.replace(generalized);
        let matched = self.elab_match_with_scrutinee(
            Expr::fvar(matched_fvar),
            matched_ty.clone(),
            None,
            &inner_arms,
        );
        self.current_expected_type = saved;
        let mut result = matched?;
        for (fvar, _, _, _) in &eta_locals[1..] {
            result = Expr::app(result, Expr::fvar(*fvar));
        }
        Ok(Some(result))
    }
}

fn surface_info(info: &BinderData) -> clean_parser::SurfaceBinderInfo {
    match info.info {
        clean_kernel::BinderInfo::Default => clean_parser::SurfaceBinderInfo::Explicit,
        clean_kernel::BinderInfo::Implicit => clean_parser::SurfaceBinderInfo::Implicit,
        clean_kernel::BinderInfo::StrictImplicit => clean_parser::SurfaceBinderInfo::StrictImplicit,
        clean_kernel::BinderInfo::InstImplicit => clean_parser::SurfaceBinderInfo::Instance,
    }
}
