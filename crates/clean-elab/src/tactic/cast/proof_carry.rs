// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cast proof-carry target rewrite pipeline.
//!
//! Replaces the trusted-fallback pattern in cast-normalization tactics
//! (`push_cast`, `norm_cast`, `zify`, `qify`) with theorem-backed rewrites
//! routed through the simp engine.
//!
//! Part of #2516: eliminate trusted fallback from cast-normalization tactics.

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};

use crate::tactic::core::{Goal, ProofState, TacticError};
use crate::tactic::simp::{collect_named_eq_lemmas, simp_expr, SimpConfig, SimpLemmaSet};

/// Flavor of cast rewrite, determining which lemma bundle to use.
#[derive(Debug, Clone, Copy)]
pub(crate) enum CastRewriteFlavor {
    /// Push casts toward leaves: `Int.ofNat_add`, `Int.ofNat_mul`,
    /// `Rat.ofInt_add`, `Rat.ofInt_mul`.
    PushCast,
    /// Normalize casts: arithmetic lemmas + proposition transfer.
    NormCast,
    /// Nat -> Int: proposition transfer + Nat arithmetic cast lemmas.
    Zify,
    /// Int -> Rat: proposition transfer + Rat arithmetic cast lemmas.
    Qify,
}

impl CastRewriteFlavor {
    /// Return the named lemma bundle for this flavor.
    fn lemma_names(&self) -> &'static [&'static str] {
        match self {
            CastRewriteFlavor::PushCast => &[
                "Int.ofNat_add",
                "Int.ofNat_mul",
                "Rat.ofInt_add",
                "Rat.ofInt_mul",
            ],
            CastRewriteFlavor::NormCast => &[
                "Int.ofNat_add",
                "Int.ofNat_mul",
                "Rat.ofInt_add",
                "Rat.ofInt_mul",
                // `norm_cast` should normalize Nat-side propositions into Int,
                // not escalate existing Int goals again into Rat.
                "Nat.cast_eq_prop",
            ],
            // Order `*_lt_prop` before `*_le_prop`: the unifier WHNFs reducible
            // `<` relations (`Int.lt`, `Rat.lt`) into `≤`-based definitions, so
            // the direct `<` transfer lemma must win before the broader `≤` one.
            CastRewriteFlavor::Zify => &[
                "Nat.cast_eq_prop",
                "Nat.cast_lt_prop",
                "Nat.cast_le_prop",
                "Int.ofNat_add",
                "Int.ofNat_mul",
            ],
            CastRewriteFlavor::Qify => &[
                "Int.cast_eq_prop",
                "Int.cast_lt_prop",
                "Int.cast_le_prop",
                "Rat.ofInt_add",
                "Rat.ofInt_mul",
            ],
        }
    }
}

fn has_unsupported_cast_source(expr: &Expr, flavor: CastRewriteFlavor) -> bool {
    let blocked_head = match (flavor, expr.get_app_fn().kind()) {
        (CastRewriteFlavor::Zify, ExprKind::Const(name, _)) => name.to_string() == "Nat.sub",
        (CastRewriteFlavor::Qify, ExprKind::Const(name, _)) => name.to_string() == "Int.div",
        _ => false,
    };
    if blocked_head {
        return true;
    }

    match expr.kind() {
        ExprKind::App(f, arg) => {
            has_unsupported_cast_source(f, flavor) || has_unsupported_cast_source(arg, flavor)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            has_unsupported_cast_source(ty, flavor) || has_unsupported_cast_source(body, flavor)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            has_unsupported_cast_source(ty, flavor)
                || has_unsupported_cast_source(val, flavor)
                || has_unsupported_cast_source(body, flavor)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            has_unsupported_cast_source(inner, flavor)
        }
        _ => false,
    }
}

/// Rewrite the current goal's target using cast-specific simp lemmas.
///
/// This is the shared proof-carry pipeline for all cast-normalization tactics.
/// It replaces the previous pattern of heuristic AST surgery followed by
/// `replace_target_with_trusted_fallback`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(true)`, the target has been rewritten via
///   `replace_target_eq` (with proof) or `replace_target_def_eq` (definitional).
/// ENSURES: On `Ok(false)`, the target was unchanged (no applicable lemmas fired).
/// ENSURES: Never falls through to `replace_target_with_trusted_fallback`.
/// ENSURES: Returns `Err(EnvironmentMissing)` if the cast lemma overlay is not
///   initialized or any named lemma is absent.
pub(crate) fn rewrite_target_with_cast_lemmas(
    state: &mut ProofState,
    _tactic_name: &'static str,
    flavor: CastRewriteFlavor,
) -> Result<bool, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Ensure the cast lemma overlay is initialized.
    state
        .env_mut()
        .init_cast_simp_lemmas()
        .map_err(|e| TacticError::EnvironmentMissing {
            constant: format!("cast lemma init failed: {e}"),
        })?;

    // Collect the flavor-specific lemma bundle.
    let lemmas = collect_named_eq_lemmas(state, flavor.lemma_names(), 200)?;

    // Run simp on the current target with only the cast lemmas.
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // `zify`/`qify` must fail closed on side-condition-sensitive rewrites such
    // as `Nat.sub` and `Int.div`; proposition transfer alone is incomplete.
    if has_unsupported_cast_source(&target, flavor) {
        return Ok(false);
    }

    let config = SimpConfig {
        only_simplify: true,
        ..SimpConfig::new()
    };
    let lemmas = SimpLemmaSet::with_goal(state, &goal, lemmas);
    let result = simp_expr(state, &goal, &target, &lemmas, &config);

    // No change — nothing to do.
    if result.expr == target {
        return Ok(false);
    }

    // Apply the rewrite.
    if let Some(eq_proof) = result.proof {
        state.replace_target_eq(result.expr, eq_proof)?;
    } else {
        // Definitional change (beta/eta/iota/zeta only).
        state.replace_target_def_eq(result.expr)?;
    }

    Ok(true)
}

/// Rewrite local hypothesis types using the same proof-carrying cast lemma
/// bundle as `rewrite_target_with_cast_lemmas`.
///
/// This is intentionally hypothesis-only: let-bound locals are skipped because
/// replacing their type would also require rewriting the stored value.
pub(crate) fn rewrite_local_decls_with_cast_lemmas(
    state: &mut ProofState,
    tactic_name: &'static str,
    flavor: CastRewriteFlavor,
) -> Result<usize, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    state
        .env_mut()
        .init_cast_simp_lemmas()
        .map_err(|e| TacticError::EnvironmentMissing {
            constant: format!("cast lemma init failed: {e}"),
        })?;

    let lemmas = collect_named_eq_lemmas(state, flavor.lemma_names(), 200)?;
    let config = SimpConfig {
        only_simplify: true,
        ..SimpConfig::new()
    };
    let locals = state
        .current_goal()
        .ok_or(TacticError::NoGoals)?
        .local_ctx
        .iter()
        .filter(|decl| decl.value.is_none())
        .map(|decl| (decl.fvar, decl.name.clone()))
        .collect::<Vec<_>>();

    let mut rewrites = 0;
    for (hyp_fvar, hyp_name) in locals {
        let Some((goal, old_ty)) = current_hypothesis_type(state, hyp_fvar) else {
            continue;
        };
        if has_unsupported_cast_source(&old_ty, flavor) {
            continue;
        }

        let lemma_set = SimpLemmaSet::with_goal(state, &goal, lemmas.clone());
        let result = simp_expr(state, &goal, &old_ty, &lemma_set, &config);
        if result.expr == old_ty {
            continue;
        }

        let cast_expr = build_local_cast_expr(
            state,
            &goal,
            hyp_fvar,
            &hyp_name,
            &old_ty,
            &result.expr,
            result.proof,
            tactic_name,
        )?;
        state.replace_local_decl_with_cast(hyp_fvar, result.expr, cast_expr)?;
        rewrites += 1;
    }

    Ok(rewrites)
}

fn current_hypothesis_type(state: &ProofState, hyp_fvar: FVarId) -> Option<(Goal, Expr)> {
    let goal = state.current_goal()?.clone();
    let ty = goal
        .local_ctx
        .iter()
        .find(|decl| decl.fvar == hyp_fvar)?
        .ty
        .clone();
    Some((goal, ty))
}

fn build_local_cast_expr(
    state: &mut ProofState,
    goal: &Goal,
    hyp_fvar: FVarId,
    hyp_name: &str,
    old_ty: &Expr,
    new_ty: &Expr,
    eq_proof: Option<Expr>,
    tactic_name: &'static str,
) -> Result<Expr, TacticError> {
    if let Some(eq_proof) = eq_proof {
        let alpha = state
            .infer_type(goal, old_ty)
            .unwrap_or(Expr::sort(Level::zero()));
        let motive = Expr::lam(BinderInfo::Default, alpha.clone(), Expr::bvar(0));
        let eq_subst_level = match alpha.kind() {
            ExprKind::Sort(level) => Level::succ(level.clone()),
            _ => Level::succ(Level::zero()),
        };
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![eq_subst_level]);
        return Ok(Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(eq_subst, alpha), motive),
                        old_ty.clone(),
                    ),
                    new_ty.clone(),
                ),
                eq_proof,
            ),
            Expr::fvar(hyp_fvar),
        ));
    }

    if state.is_def_eq(goal, old_ty, new_ty) {
        Ok(Expr::fvar(hyp_fvar))
    } else {
        Err(TacticError::TypeCheckFailed(format!(
            "{tactic_name} at {hyp_name}: congruence proof construction failed; \
             simplified type is not definitionally equal to the original"
        )))
    }
}
