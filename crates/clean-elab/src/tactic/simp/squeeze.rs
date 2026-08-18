// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Squeeze simp tactic — tracks which lemmas are actually used during
//! simplification and suggests a minimal `simp only [...]` call.

use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;
use crate::tactic::core::{Goal, ProofState, TacticError, TacticResult};
use crate::tactic::{assumption, rfl};

use super::cache::collect_simp_lemmas_cached;
use super::expr::try_apply_simp_lemma_with_proof;
use super::proof::{mk_congr, mk_congr_arg, mk_congr_fun, mk_eq_trans, mk_forall_congr, mk_funext};
use super::reduce::{beta_reduce, eta_reduce};
use super::types::{SimpConfig, SimpLemmaSet, SimpResult};

/// Configuration for squeeze_simp
#[derive(Debug, Clone, Default)]
pub struct SqueezeSimpConfig {
    /// Base simp configuration
    pub simp_config: SimpConfig,
    /// Whether to print verbose output about all attempted lemmas
    pub verbose: bool,
}

impl SqueezeSimpConfig {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Result of squeeze_simp showing which lemmas were used
#[derive(Debug, Clone)]
pub struct SqueezeSimpResult {
    /// The lemmas that were actually used during simplification
    pub used_lemmas: Vec<String>,
    /// Suggested replacement: "simp only [lemma1, lemma2, ...]"
    pub suggested_tactic: String,
    /// Whether the goal was closed
    pub closed: bool,
}

#[derive(Debug, Clone)]
struct TrackedSimpStep {
    result: SimpResult,
    applied_named_lemmas: Vec<String>,
    applied_reduction: Option<String>,
}

fn push_unique_lemma(target: &mut Vec<String>, lemma: String) {
    if !target.contains(&lemma) {
        target.push(lemma);
    }
}

fn extend_unique_lemmas(target: &mut Vec<String>, lemmas: impl IntoIterator<Item = String>) {
    for lemma in lemmas {
        push_unique_lemma(target, lemma);
    }
}

/// Tactic: squeeze_simp
///
/// Like `simp`, but tracks which lemmas were actually used during simplification.
/// Returns a `SqueezeSimpResult` with the suggested `simp only [...]` call.
///
/// This is useful for:
/// - Speeding up proofs by replacing `simp` with `simp only [...]`
/// - Making proofs more robust by explicitly listing dependencies
/// - Debugging which lemmas are being applied
///
/// # Example
/// ```text
/// -- Goal: a + 0 + 0 = a
/// squeeze_simp
/// -- Output: "Try: simp only [Nat.add_zero]"
/// -- Goal closed
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
pub fn squeeze_simp(state: &mut ProofState) -> Result<SqueezeSimpResult, TacticError> {
    squeeze_simp_with_config(state, SqueezeSimpConfig::new())
}

/// squeeze_simp with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: `used_lemmas` contains each applied lemma name exactly once, in application order
/// ENSURES: If `closed == true`, the goal was closed via rfl or assumption after simplification
/// ENSURES: If no progress, `used_lemmas` is empty and goal target is unchanged
/// ENSURES: On Err(NoGoals), no goals exist; state unchanged
pub fn squeeze_simp_with_config(
    state: &mut ProofState,
    config: SqueezeSimpConfig,
) -> Result<SqueezeSimpResult, TacticError> {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut current_target = goal.target.clone();
    let mut steps = 0;
    let mut used_lemmas: Vec<String> = Vec::new();
    let mut accumulated_proof: Option<Expr> = None;

    // Collect simp lemmas from environment
    let simp_lemmas = collect_simp_lemmas_cached(state, &config.simp_config);

    // Main simplification loop - track which lemmas are actually applied
    while steps < config.simp_config.max_steps {
        let step = simp_expr_tracking(
            state,
            &goal,
            &current_target,
            &simp_lemmas,
            &config.simp_config,
        );

        if step.result.expr != current_target {
            accumulated_proof = match (accumulated_proof.take(), step.result.proof) {
                (None, proof) => proof,
                (proof, None) => proof,
                (Some(p1), Some(p2)) => {
                    Some(super::mk_eq_trans_expr(state, &goal, &p1, &p2).unwrap_or(p2))
                }
            };

            let applied_lemmas = if step.applied_named_lemmas.is_empty() {
                step.applied_reduction.into_iter().collect()
            } else {
                step.applied_named_lemmas
            };
            extend_unique_lemmas(&mut used_lemmas, applied_lemmas);
            current_target = step.result.expr;
            steps += 1;
        } else {
            break;
        }
    }

    let made_progress = current_target != goal.target;

    // Part of #2503: preserve proof-carry target rewrites instead of falling
    // back to trustedArith on successful simplification.
    if made_progress {
        if let Some(proof) = accumulated_proof {
            state.replace_target_eq(current_target.clone(), proof)?;
        } else {
            state.replace_target_def_eq(current_target.clone())?;
        }
    }

    // Try to close with reflexivity
    let closed = if config.simp_config.only_simplify {
        false
    } else {
        rfl(state).is_ok() || assumption(state).is_ok()
    };

    // Generate suggested tactic
    let suggested_tactic = if used_lemmas.is_empty() {
        "simp only []".to_string()
    } else {
        format!("simp only [{}]", used_lemmas.join(", "))
    };

    Ok(SqueezeSimpResult {
        used_lemmas,
        suggested_tactic,
        closed,
    })
}

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
fn simp_expr_tracking(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
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
            for lemma in lemmas.candidates(state, goal, &result.expr) {
                if let Some((new_expr, proof)) = try_apply_simp_lemma_with_proof(
                    state,
                    goal,
                    &result.expr,
                    lemma,
                    lemmas,
                    config,
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
                let f_step = stack_safe(|| simp_expr_tracking(state, goal, f, lemmas, config));
                let a_step = stack_safe(|| simp_expr_tracking(state, goal, a, lemmas, config));
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
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config));
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
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config));
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
                let val_step = stack_safe(|| simp_expr_tracking(state, goal, val, lemmas, config));
                let body_step =
                    stack_safe(|| simp_expr_tracking(state, goal, body, lemmas, config));
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
                    stack_safe(|| simp_expr_tracking(state, goal, inner, lemmas, config));
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
                    stack_safe(|| simp_expr_tracking(state, goal, inner, lemmas, config));
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

/// squeeze_simp and apply the result
pub fn squeeze_simp_and_apply(state: &mut ProofState) -> TacticResult {
    let result = squeeze_simp(state)?;
    if result.closed {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "squeeze_simp".into(),
        })
    }
}

#[cfg(test)]
mod tests;
