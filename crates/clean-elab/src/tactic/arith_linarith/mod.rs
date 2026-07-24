// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear arithmetic (linarith) tactic
//!
//! Fourier-Motzkin elimination for linear arithmetic reasoning.
//!
//! Split into sub-modules for maintainability (#307):
//! - `trusted_arith`: Trusted arithmetic proof tracking and counters
//! - `certificate`: Proof certificate types for Fourier-Motzkin
//! - `fourier_motzkin`: Variable elimination algorithms
//! - `parse`: Constraint extraction and expression parsing

mod arena;
mod certificate;
mod fourier_motzkin;
mod fourier_motzkin_wide;
mod parse;
mod trusted_arith;

// Re-export public items
pub use certificate::{CertifiedConstraint, FMCertifiedResult, FMResult, LinarithCertificate};
#[cfg(test)]
pub use trusted_arith::arith_lifetime_count;
pub use trusted_arith::{arith_proof_count, reset_arith_counter};

// Re-export pub(crate) items
pub(crate) use fourier_motzkin::{fourier_motzkin_check, fourier_motzkin_check_certified};
pub(crate) use parse::{extract_certified_linear_constraints, extract_linear_constraints};
#[cfg(test)]
pub(crate) use trusted_arith::close_with_trusted_arith;
#[cfg(test)]
pub(crate) use trusted_arith::create_trusted_arith_term;
#[cfg(test)]
pub(crate) use trusted_arith::make_trusted_arith_term_untracked;
#[cfg(test)]
pub(crate) use trusted_arith::record_target_rewrite_trusted_arith_fallback;
#[cfg(test)]
pub(crate) use trusted_arith::{arith_locations, enable_arith_location_tracking};

// Re-export proof reconstruction functions for tests and other modules
pub(crate) use super::arith_linarith_proof::build_linarith_proof;

use super::smt::AyConfig;
use super::{decide, ProofState, TacticError, TacticResult};

fn certified_unsat_without_kernel_proof(reason: impl Into<String>) -> TacticResult {
    Err(TacticError::ArithmeticFailed {
        tactic: "linarith".to_string(),
        reason: format!(
            "certified FM found contradiction but replay produced no kernel proof ({})",
            reason.into()
        ),
    })
}

#[cfg(test)]
pub(crate) fn test_only_certified_unsat_without_kernel_proof(reason: &str) -> TacticResult {
    certified_unsat_without_kernel_proof(reason)
}

/// Attempt to close the current goal via the Ay QF_LRA solver.
///
/// This is the SMT-backed fallback for `linarith`. When Fourier-Motzkin
/// elimination finds a contradiction but native proof reconstruction fails,
/// the Ay solver can often produce a kernel-verified proof term via the
/// SMT proof reconstruction bridge.
///
/// REQUIRES: `state` has at least one open goal with linear arithmetic hypotheses
/// ENSURES: On `Ok(())`, the current goal is closed with a kernel-verified proof
/// ENSURES: On `Err(_)`, the Ay solver could not prove the goal
fn try_ay_lra(state: &mut ProofState) -> TacticResult {
    super::smt::ay_lra(state, AyConfig::from_env())
}

/// Try certified FM path: extract constraints, eliminate, build proof.
///
/// Returns `Some(Ok(()))` if the goal was closed, `Some(Err(_))` if FM
/// determined the result definitively (SAT or UNSAT without proof), or
/// `None` if certified FM was inconclusive and the caller should continue.
fn try_certified_fm(state: &mut ProofState, goal: &super::Goal) -> Option<TacticResult> {
    let (certified, _var_map, hyp_fvars) = extract_certified_linear_constraints(state, goal)?;
    match fourier_motzkin_check_certified(&certified) {
        FMCertifiedResult::Unsat(certificate) => {
            // Try kernel proof from certificate
            if let Some(proof) = build_linarith_proof(state, goal, &certificate, &hyp_fvars) {
                match state.close_goal(goal, proof) {
                    Ok(()) => return Some(Ok(())),
                    Err(e) => tracing::debug!(
                        "linarith: build_linarith_proof succeeded but close_goal rejected: {e:?}"
                    ),
                }
            } else {
                tracing::debug!(
                    active_hyps = hyp_fvars.len(),
                    "linarith: build_linarith_proof returned None for certified FM"
                );
            }
            // Direct goal-driven Nat inequality proof (ineq_gap fix): when the
            // contradiction comes from the negated goal (e.g. `n + 1 > n`), the
            // hypothesis-refutation builder above has no fvar to thread and
            // returns None. Prove the goal directly (optionally weakening a
            // matching `≤` hypothesis, e.g. `(h : a ≤ b) ⊢ a ≤ b + 1`).
            // close_goal still re-checks the synthesized term in the kernel.
            let direct_hyps: Vec<(clean_kernel::Expr, clean_kernel::Expr)> = goal
                .local_ctx
                .iter()
                .map(|d| (clean_kernel::Expr::fvar(d.fvar), d.ty.clone()))
                .collect();
            if let Some(proof) =
                super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(
                    &goal.target,
                    &direct_hyps,
                )
            {
                match state.close_goal(goal, proof) {
                    Ok(()) => return Some(Ok(())),
                    Err(e) => tracing::debug!(
                        "linarith: direct Nat inequality proof rejected by close_goal: {e:?}"
                    ),
                }
            }
            // Certificate proof failed — fall back to ay_lra then decide
            if try_ay_lra(state).is_ok() || decide(state).is_ok() {
                return Some(Ok(()));
            }
            Some(certified_unsat_without_kernel_proof(
                "replay, ay_lra, and decide all failed",
            ))
        }
        FMCertifiedResult::Sat => Some(Err(TacticError::ArithmeticFailed {
            tactic: "linarith".to_string(),
            reason: "constraints are satisfiable, goal not provable".to_string(),
        })),
        FMCertifiedResult::Unknown => None,
    }
}

/// Try uncertified FM: extract constraints, check satisfiability, close via
/// ay_lra or decide if UNSAT.
fn try_uncertified_fm(state: &mut ProofState, goal: &super::Goal) -> TacticResult {
    let Some((constraints, _var_map)) = extract_linear_constraints(state, goal) else {
        // FM parser cannot extract constraints — try Ay directly
        if try_ay_lra(state).is_ok() {
            return Ok(());
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "linarith".to_string(),
            reason: "could not extract linear constraints and ay_lra failed".to_string(),
        });
    };
    match fourier_motzkin_check(&constraints) {
        FMResult::Unsat => {
            if try_ay_lra(state).is_ok() || decide(state).is_ok() {
                return Ok(());
            }
            Err(TacticError::ArithmeticFailed {
                tactic: "linarith".to_string(),
                reason: "FM found contradiction but ay_lra and decide could not close goal"
                    .to_string(),
            })
        }
        FMResult::Sat => Err(TacticError::ArithmeticFailed {
            tactic: "linarith".to_string(),
            reason: "constraints are satisfiable, goal not provable".to_string(),
        }),
        FMResult::Unknown => Err(TacticError::ArithmeticFailed {
            tactic: "linarith".to_string(),
            reason: "could not determine satisfiability".to_string(),
        }),
    }
}

/// Linear arithmetic tactic.
///
/// Proves goals involving linear (in)equalities over Nat/Int/Real using
/// Fourier-Motzkin elimination, with Ay QF_LRA as an SMT-backed fallback
/// for proof reconstruction.
///
/// # Algorithm
/// 1. Try `reduce_eq` for computational equality
/// 2. Certified Fourier-Motzkin with proof reconstruction
/// 3. Uncertified Fourier-Motzkin cross-check
/// 4. Ay QF_LRA solver (SMT bridge proof reconstruction)
/// 5. Native `decide` as final fallback
pub fn linarith(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    // Pre-processing: computational equality is cheaper than FM (#685).
    if super::reduce_eq(state).is_ok() {
        return Ok(());
    }
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Goal-driven direct Nat reconstruction (bounded slices A + B): proves the
    // `a ≤ a + b` non-negativity family and the `n <|≤ c1 ⊢ n + k <|≤ c2`
    // offset family up front. Certified FM would otherwise report `Sat` for
    // slice A (no `0 ≤ x` in the rational system) or fail the certificate
    // replay for slice B. Re-checked by `close_goal`, so false goals (None from
    // the prover) still fail closed.
    {
        let direct_hyps: Vec<(clean_kernel::Expr, clean_kernel::Expr)> = goal
            .local_ctx
            .iter()
            .map(|d| (clean_kernel::Expr::fvar(d.fvar), d.ty.clone()))
            .collect();
        if let Some(proof) =
            super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(
                &goal.target,
                &direct_hyps,
            )
        {
            if state.close_goal(&goal, proof).is_ok() {
                return Ok(());
            }
        }
    }

    // Certified FM first
    if let Some(result) = try_certified_fm(state, &goal) {
        return result;
    }
    // Uncertified FM with ay/decide fallback
    try_uncertified_fm(state, &goal)
}

/// Standalone linear arithmetic proof function.
///
/// Takes an environment, hypothesis types, and a goal type, and returns
/// a proof term if the goal follows from the hypotheses by linear arithmetic.
/// This is the non-tactic entry point for `linarith`, useful for programmatic
/// invocation outside the tactic framework.
///
/// REQUIRES: `env` contains the necessary declarations (Nat, Int, LE, etc.)
/// REQUIRES: `hypotheses` are well-typed expressions representing hypothesis types
/// REQUIRES: `goal` is a well-typed expression representing the goal type
/// ENSURES: On `Ok(proof)`, `proof` is a kernel expression whose type is `goal`
///          under the context of the given hypotheses
/// ENSURES: On `Err(_)`, the goal is not provable from the hypotheses by linear
///          arithmetic (or the expressions could not be parsed)
///
/// # Example
/// ```text
/// let proof = linarith_prove(&env, &[h1_ty, h2_ty], &goal_ty)?;
/// ```
///
/// Part of #3367.
pub fn linarith_prove(
    env: &clean_kernel::Environment,
    hypotheses: &[clean_kernel::Expr],
    goal: &clean_kernel::Expr,
) -> Result<clean_kernel::Expr, TacticError> {
    use super::LocalDecl;
    use clean_kernel::FVarId;

    // Build a ProofState with the hypotheses as local declarations.
    let mut local_ctx = Vec::with_capacity(hypotheses.len());
    for (i, hyp_ty) in hypotheses.iter().enumerate() {
        local_ctx.push(LocalDecl {
            fvar: FVarId::new(1000 + i as u64),
            name: format!("h{}", i + 1),
            ty: hyp_ty.clone(),
            value: None,
        });
    }

    let mut state = ProofState::with_context(env.clone(), goal.clone(), local_ctx);

    linarith(&mut state)?;

    state
        .proof_term()
        .ok_or_else(|| TacticError::ArithmeticFailed {
            tactic: "linarith_prove".to_string(),
            reason: "linarith closed the goal but no proof term was retained".to_string(),
        })
}
