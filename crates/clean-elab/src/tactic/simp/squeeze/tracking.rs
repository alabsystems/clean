// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `simp?` traversal: one `simp` step that also records WHICH lemma fired.
//!
//! Split out of `squeeze.rs` so that file stays under the 500-line limit; the
//! traversal is self-contained (it reads the parent module's `TrackedSimpStep`
//! and nothing else of it) and is the half that carries the per-traversal
//! budget checks, so it reads better on its own.

use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;
use crate::tactic::core::{Goal, ProofState};

use super::super::budget::SimpBudget;
use super::super::expr::try_apply_simp_lemma_with_proof;
use super::super::match_target::MatchTarget;
use super::super::proof::{
    mk_congr, mk_congr_arg, mk_congr_fun, mk_eq_trans, mk_forall_congr, mk_funext,
};
use super::super::reduce::{beta_reduce, eta_reduce};
use super::super::types::{SimpConfig, SimpLemmaSet, SimpResult};
use super::{extend_unique_lemmas, TrackedSimpStep};

/// Helper: simplify expression while tracking which lemma was applied
///
/// # Contract
///
/// REQUIRES: `expr` is a well-typed expression in the current environment
/// ENSURES: `result.expr` is the rewritten expression for this step
/// ENSURES: `result.proof` stays aligned with the rewrite when the change is propositional
/// ENSURES: `applied_named_lemmas` reports every named simp lemma used while
/// rewriting recursive child nodes in left-to-right order
/// ENSURES: `applied_reduction` reports beta/eta only when no named simp lemma
/// was used in this step
pub(super) fn simp_expr_tracking(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> TrackedSimpStep {
    // Same three budget checks as `expr::simp_expr_budgeted`, for the same
    // reason: a trip must unwind this frame to its own INPUT so no partial
    // rewrite (and no lemma attribution for one) survives.
    if !budget.tick() {
        return tracked_refl(expr);
    }
    let step = simp_expr_tracking_inner(state, goal, expr, lemmas, config, budget);
    if budget.is_tripped() {
        return tracked_refl(expr);
    }
    if step.result.expr != *expr && !budget.admit(&step.result.expr) {
        return tracked_refl(expr);
    }
    step
}

/// The unchanged step: `expr` with no rewrite, no lemma, no reduction.
fn tracked_refl(expr: &Expr) -> TrackedSimpStep {
    TrackedSimpStep {
        result: SimpResult::refl(expr.clone()),
        applied_named_lemmas: Vec::new(),
        applied_reduction: None,
    }
}

/// The body of one tracked traversal frame. Call [`simp_expr_tracking`].
fn simp_expr_tracking_inner(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> TrackedSimpStep {
    stack_safe(|| {
        let mut result = SimpResult::refl(expr.clone());
        let mut applied_reduction: Option<String> = None;
        let preserve_outer_let = matches!(expr.kind(), ExprKind::Let(..));

        if config.beta && !preserve_outer_let {
            let reduced = beta_reduce(&result.expr);
            if reduced != result.expr {
                result = SimpResult {
                    expr: reduced,
                    proof: None,
                };
                applied_reduction = Some("beta".to_string());
            }
        }

        if config.eta {
            let reduced = eta_reduce(&result.expr);
            if reduced != result.expr {
                result = SimpResult {
                    expr: reduced,
                    proof: None,
                };
                if applied_reduction.is_none() {
                    applied_reduction = Some("eta".to_string());
                }
            }
        }

        // Whole-expression lemma matching uses WHNF unification, which would
        // collapse outer let-bindings before recursive child tracking can
        // record value/body lemma provenance.
        if !preserve_outer_let {
            let match_target = MatchTarget::new(state, goal, &result.expr);
            for lemma in lemmas.candidates(state, goal, &result.expr) {
                if let Some((new_expr, proof)) = try_apply_simp_lemma_with_proof(
                    state,
                    goal,
                    &match_target,
                    lemma,
                    lemmas,
                    config,
                    budget,
                ) {
                    if new_expr != result.expr {
                        let step = SimpResult {
                            expr: new_expr,
                            proof: Some(proof),
                        };
                        return TrackedSimpStep {
                            result: mk_eq_trans(result, step, state, goal),
                            applied_named_lemmas: vec![lemma.name.to_string()],
                            applied_reduction: None,
                        };
                    }
                }
            }
        }

        // Recurse into subexpressions
        match result.expr.kind() {
            ExprKind::App(f, a) => {
                let f_step =
                    stack_safe(|| simp_expr_tracking(state, goal, f, lemmas, config, budget));
                let a_step =
                    stack_safe(|| simp_expr_tracking(state, goal, a, lemmas, config, budget));
                let f_changed = f_step.result.expr != **f;
                let a_changed = a_step.result.expr != **a;

                if f_changed || a_changed {
                    let app_expr =
                        Expr::app(f_step.result.expr.clone(), a_step.result.expr.clone());
                    let app_proof = match (&f_step.result.proof, &a_step.result.proof) {
                        (Some(h_f), Some(h_a)) => mk_congr(
                            state,
                            goal,
                            f,
                            &f_step.result.expr,
                            a,
                            &a_step.result.expr,
                            h_f,
                            h_a,
                        ),
                        (Some(h_f), None) => {
                            mk_congr_fun(state, goal, f, &f_step.result.expr, a, h_f)
                        }
                        (None, Some(h_a)) => {
                            mk_congr_arg(state, goal, f, a, &a_step.result.expr, h_a)
                        }
                        (None, None) => None,
                    };
                    let app_result = SimpResult {
                        expr: app_expr,
                        proof: app_proof,
                    };
                    let mut applied_named_lemmas = Vec::new();
                    extend_unique_lemmas(&mut applied_named_lemmas, f_step.applied_named_lemmas);
                    extend_unique_lemmas(&mut applied_named_lemmas, a_step.applied_named_lemmas);
                    return TrackedSimpStep {
                        result: mk_eq_trans(result, app_result, state, goal),
                        applied_reduction: if applied_named_lemmas.is_empty() {
                            f_step
                                .applied_reduction
                                .or(a_step.applied_reduction)
                                .or(applied_reduction)
                        } else {
                            None
                        },
                        applied_named_lemmas,
                    };
                }
            }
            ExprKind::Lam(bi, ty, body) => {
                let body_step =
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config, budget));
                if body_step.result.expr != **body {
                    let lam_proof = body_step.result.proof.as_ref().and_then(|bp| {
                        mk_funext(state, goal, ty, body, &body_step.result.expr, bp)
                    });
                    let lam_result = SimpResult {
                        expr: Expr::lam(*bi, ty.as_ref().clone(), body_step.result.expr),
                        proof: lam_proof,
                    };
                    let applied_reduction = if body_step.applied_named_lemmas.is_empty() {
                        body_step.applied_reduction.or(applied_reduction)
                    } else {
                        None
                    };
                    return TrackedSimpStep {
                        result: mk_eq_trans(result, lam_result, state, goal),
                        applied_named_lemmas: body_step.applied_named_lemmas,
                        applied_reduction,
                    };
                }
            }
            ExprKind::Pi(bi, ty, body) => {
                let body_step =
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config, budget));
                if body_step.result.expr != **body {
                    let pi_proof = body_step.result.proof.as_ref().and_then(|bp| {
                        mk_forall_congr(state, goal, ty, body, &body_step.result.expr, bp)
                    });
                    let pi_result = SimpResult {
                        expr: Expr::pi(*bi, ty.as_ref().clone(), body_step.result.expr),
                        proof: pi_proof,
                    };
                    let applied_reduction = if body_step.applied_named_lemmas.is_empty() {
                        body_step.applied_reduction.or(applied_reduction)
                    } else {
                        None
                    };
                    return TrackedSimpStep {
                        result: mk_eq_trans(result, pi_result, state, goal),
                        applied_named_lemmas: body_step.applied_named_lemmas,
                        applied_reduction,
                    };
                }
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let val_step =
                    stack_safe(|| simp_expr_tracking(state, goal, val, lemmas, config, budget));
                let body_step =
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config, budget));
                if val_step.result.expr != **val || body_step.result.expr != **body {
                    let mut let_expr = Expr::let_named(
                        name.clone(),
                        ty.as_ref().clone(),
                        val_step.result.expr,
                        body_step.result.expr,
                        *non_dep,
                    );
                    let let_reduction = if config.beta {
                        let reduced = beta_reduce(&let_expr);
                        if reduced != let_expr {
                            let_expr = reduced;
                            Some("beta".to_string())
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let let_result = SimpResult {
                        expr: let_expr,
                        proof: None,
                    };
                    let mut applied_named_lemmas = Vec::new();
                    extend_unique_lemmas(&mut applied_named_lemmas, val_step.applied_named_lemmas);
                    extend_unique_lemmas(&mut applied_named_lemmas, body_step.applied_named_lemmas);
                    return TrackedSimpStep {
                        result: mk_eq_trans(result, let_result, state, goal),
                        applied_reduction: if applied_named_lemmas.is_empty() {
                            val_step
                                .applied_reduction
                                .or(body_step.applied_reduction)
                                .or(let_reduction)
                                .or(applied_reduction)
                        } else {
                            None
                        },
                        applied_named_lemmas,
                    };
                }
            }
            ExprKind::Proj(name, idx, inner) => {
                let inner_step =
                    stack_safe(|| simp_expr_tracking(state, goal, inner, lemmas, config, budget));
                if inner_step.result.expr != **inner {
                    let proj_proof = inner_step.result.proof.as_ref().and_then(|h| {
                        let inner_ty = state.infer_type(goal, inner).ok()?;
                        let f = Expr::lam(
                            clean_kernel::BinderInfo::Default,
                            inner_ty,
                            Expr::proj(name.clone(), *idx, Expr::bvar(0)),
                        );
                        mk_congr_arg(state, goal, &f, inner, &inner_step.result.expr, h)
                    });
                    let proj_result = SimpResult {
                        expr: Expr::proj(name.clone(), *idx, inner_step.result.expr),
                        proof: proj_proof,
                    };
                    let applied_reduction = if inner_step.applied_named_lemmas.is_empty() {
                        inner_step.applied_reduction.or(applied_reduction)
                    } else {
                        None
                    };
                    return TrackedSimpStep {
                        result: mk_eq_trans(result, proj_result, state, goal),
                        applied_named_lemmas: inner_step.applied_named_lemmas,
                        applied_reduction,
                    };
                }
            }
            ExprKind::MData(_mdata, inner) => {
                // MData is semantically transparent (def-eq to inner via WHNF).
                let inner_step =
                    stack_safe(|| simp_expr_tracking(state, goal, inner, lemmas, config, budget));
                let strip_result = SimpResult {
                    expr: inner_step.result.expr,
                    proof: inner_step.result.proof,
                };
                let applied_reduction = if inner_step.applied_named_lemmas.is_empty() {
                    inner_step.applied_reduction.or(applied_reduction)
                } else {
                    None
                };
                return TrackedSimpStep {
                    result: mk_eq_trans(result, strip_result, state, goal),
                    applied_named_lemmas: inner_step.applied_named_lemmas,
                    applied_reduction,
                };
            }
            _ => {}
        }

        if preserve_outer_let && config.beta {
            let reduced = beta_reduce(&result.expr);
            if reduced != result.expr {
                return TrackedSimpStep {
                    result: SimpResult {
                        expr: reduced,
                        proof: None,
                    },
                    applied_named_lemmas: Vec::new(),
                    applied_reduction: Some("beta".to_string()),
                };
            }
        }

        TrackedSimpStep {
            result,
            applied_named_lemmas: Vec::new(),
            applied_reduction,
        }
    })
}
