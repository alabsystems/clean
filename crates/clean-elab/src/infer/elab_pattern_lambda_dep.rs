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
//! A nonrecursive two-column match may instead select a nullary constructor
//! first and destructure its dependent argument inside that branch. Distinct
//! constructors are disjoint; repeated rows for one constructor keep their
//! original order. The checked expected type supplies each inner binder.

use clean_kernel::{BinderData, Expr, FVarId};
use clean_parser::{SurfaceBinder, SurfaceExpr, SurfaceMatchArm, SurfaceName, SurfacePattern};
use hashbrown::HashMap;

use super::{ElabCtx, ElabError};

impl ElabCtx<'_> {
    /// Generalize dependent columns over the matched argument. Plain hypotheses
    /// become lambda binders; patterned hypotheses use a constructor split.
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
        let all_plain = peeled_arms.iter().all(|pats| {
            pats[1..].iter().all(|pat| match pat {
                SurfacePattern::Wildcard => true,
                SurfacePattern::Var(name) => {
                    self.bare_pattern_name_is_constructor(name) == Some(false)
                }
                _ => false,
            })
        });
        let inner_arms: Vec<SurfaceMatchArm> = if all_plain {
            arms.iter()
                .zip(peeled_arms)
                .map(|(arm, pats)| {
                    let binders = pats[1..]
                        .iter()
                        .zip(&eta_locals[1..])
                        .map(|(pat, (_, _, info, _))| {
                            let name = match pat {
                                SurfacePattern::Var(name) => name.clone(),
                                _ => SurfaceName::component("_", false),
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
                .collect()
        } else {
            if arity != 2 || self.recursive_def_ctx.is_some() {
                return Ok(None);
            }
            let Some(arms) =
                self.specialize_enum_rows(arms, peeled_arms, matched_ty, &eta_locals[1].2)?
            else {
                return Ok(None);
            };
            arms
        };
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
    /// For a non-indexed enumeration, group rows by the authenticated first
    /// constructor and match the second pattern only at its specialized type.
    fn specialize_enum_rows(
        &mut self,
        arms: &[SurfaceMatchArm],
        patterns: &[Vec<SurfacePattern>],
        first_type: &Expr,
        second_info: &BinderData,
    ) -> Result<Option<Vec<SurfaceMatchArm>>, ElabError> {
        let Ok(first_name) = self.get_type_identity(first_type) else {
            return Ok(None);
        };
        let Some(constructors) =
            super::equation_dep_family::enum_constructors(self.env, &first_name)
        else {
            return Ok(None);
        };
        let mut positions = HashMap::new();
        let mut groups: Vec<(SurfaceName, Vec<SurfaceMatchArm>)> = Vec::new();
        for (arm, row) in arms.iter().zip(patterns) {
            let normalized = self.normalize_match_pattern_names(&row[0], first_type)?;
            let SurfacePattern::Ctor(name, fields) = normalized else {
                return Ok(None);
            };
            if !fields.is_empty() {
                return Ok(None);
            }
            let index = *positions.entry(name.name().clone()).or_insert_with(|| {
                let index = groups.len();
                groups.push((name, Vec::new()));
                index
            });
            groups[index].1.push(SurfaceMatchArm {
                span: arm.span,
                pattern: row[1].clone(),
                body: arm.body.clone(),
            });
        }
        // Each outer row names a constructor; none can cover an omitted one.
        if let Some(missing) = constructors
            .iter()
            .find(|name| !positions.contains_key(*name))
        {
            return Err(ElabError::NotImplemented(format!(
                "non-exhaustive dependent match on `{first_name}`: missing constructor `{missing}`"
            )));
        }
        let result = groups
            .into_iter()
            .map(|(name, rows)| {
                let span = rows[0].span;
                let binder = SurfaceName::unspellable("_dependent_column", 0);
                let inner = SurfaceExpr::Match(
                    span,
                    None,
                    Box::new(SurfaceExpr::Ident(span, binder.clone())),
                    rows,
                );
                SurfaceMatchArm {
                    span,
                    pattern: SurfacePattern::Ctor(name, Vec::new()),
                    body: SurfaceExpr::Lambda(
                        span,
                        vec![SurfaceBinder::new_typed(
                            binder,
                            None,
                            surface_info(second_info),
                        )],
                        Box::new(inner),
                    ),
                }
            })
            .collect();
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
