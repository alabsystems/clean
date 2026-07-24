// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core SMT decision procedure coordinator.
//!
//! Contains the `decide` tactic entrypoint and bridge-result branching.
//! Private subsystems live in focused submodules:
//!
//! - `hypotheses`: shared non-sort local-hypothesis contract
//! - `recovery`: fail-closed diagnostics and superposition fallback
//! - `validation`: proof-term kernel checking

mod hypotheses;
mod recovery;
mod validation;

use crate::tactic::{Goal, ProofState, TacticError, TacticResult};
use clean_kernel::Expr;

use super::bridge_validation::init_bridge_validation_support;
use super::selected_proof::{accept_selected_direct_proof, SelectedDirectProof};
use super::trusted_subterms::count_embedded_trusted_ay_terms;

pub(super) use hypotheses::add_hypotheses_from_context;
// Re-exported pub(super) so smt/mod.rs wrappers can delegate into these.
pub(super) use recovery::superposition_or_fail_closed;
pub(super) use validation::validate_proof_term;

// Re-exports for smt/mod.rs and sibling test modules.
#[cfg(test)]
pub(super) use recovery::classify_trusted_ay_fallback_target;
#[cfg(test)]
pub(super) use recovery::force_trusted_ay_fail_closed_for_test;
#[cfg(test)]
pub(super) use recovery::trusted_ay_fallback_target_head;
pub(crate) use recovery::try_superposition_fallback;
#[cfg(test)]
pub(crate) use recovery::validate_superposition_candidate_for_test;

/// Decision procedure tactic using SMT solving.
///
/// The `decide` tactic attempts to prove the goal using an SMT solver.
/// It works by checking if the negation of the goal is unsatisfiable.
/// If it is, the goal must be valid.
///
/// Currently supports:
/// - Equality reasoning (reflexivity, symmetry, transitivity, congruence)
/// - Basic propositional logic (and, or, implies, not)
///
/// The tactic gathers hypotheses from the local context and uses them
/// to help prove the goal. When possible, a kernel-checkable proof term
/// is produced via proof reconstruction. The proof term is then validated
/// by the kernel type checker to ensure soundness.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed with a type-checked proof term
/// ENSURES: Proof term is kernel-validated via TypeChecker before close_goal
/// ENSURES: On reconstruction + superposition failure, fails closed with `SmtFailed`
/// ENSURES: On Err, SMT solver cannot prove the goal; state unchanged
pub fn decide(state: &mut ProofState) -> TacticResult {
    use clean_auto::bridge::SmtBridge;

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Create SMT bridge with the goal's local context for FVar type resolution
    let mut bridge = SmtBridge::new(state.env());
    bridge.set_local_ctx(state.build_local_ctx(&goal));

    add_hypotheses_from_context(state, &goal, &mut bridge);

    // Try to prove the goal
    let target = state.metas.instantiate(&goal.target);
    match bridge.prove(&target) {
        Ok(clean_auto::bridge::SmtVerificationResult::Verified(proof_result)) => {
            close_bridge_verified_goal(state, &goal, &target, proof_result.proof_term())
        }
        Ok(clean_auto::bridge::SmtVerificationResult::Unverified { .. }) => {
            // UNSAT but no kernel proof term (#2387 TB3) — superposition → fail closed
            tracing::warn!(
                tactic = "decide",
                "SMT returned Unverified (no kernel proof term), trying shared recovery lane"
            );
            let t = superposition_or_fail_closed(state, &goal, &target, "decide")?;
            state.close_goal(&goal, t)?;
            Ok(())
        }
        Ok(clean_auto::bridge::SmtVerificationResult::Refuted(_model)) => {
            Err(TacticError::SmtFailed {
                tactic: "decide".into(),
                detail: "found counterexample — goal is not valid".into(),
            })
        }
        Ok(clean_auto::bridge::SmtVerificationResult::Unknown(_reason)) => {
            // SMT inconclusive; try superposition as a fallback (#1164)
            if let Some(proof_term) = try_superposition_fallback(state, &goal, &target, "decide")? {
                state.close_goal(&goal, proof_term)?;
                Ok(())
            } else {
                Err(TacticError::SmtFailed {
                    tactic: "decide".into(),
                    detail: format!("solver inconclusive — {_reason}"),
                })
            }
        }
        // non_exhaustive: handle future variants gracefully
        Ok(_) => Err(TacticError::SmtFailed {
            tactic: "decide".into(),
            detail: "unexpected verification result".into(),
        }),
        Err(_e) => {
            // SMT bridge error; try superposition as a fallback (#1164)
            if let Some(proof_term) = try_superposition_fallback(state, &goal, &target, "decide")? {
                state.close_goal(&goal, proof_term)?;
                Ok(())
            } else {
                Err(TacticError::BridgeFailed {
                    tactic: "decide".into(),
                    source: _e,
                })
            }
        }
    }
}

pub(super) fn close_bridge_verified_goal(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    bridge_proof: &Expr,
) -> TacticResult {
    init_bridge_validation_support(state);
    let proof_term = match validate_proof_term(state, goal, bridge_proof, target) {
        Ok(v) => {
            let trust_subterm_count = count_embedded_trusted_ay_terms(&v);
            accept_selected_direct_proof(
                state,
                SelectedDirectProof::new(v, trust_subterm_count),
                "decide",
                "validated bridge",
            )
        }
        Err(e) => {
            state.record_invalid_bridge_candidate();
            tracing::warn!(
                error = %e,
                tactic = "decide",
                "proof reconstruction failed kernel validation, trying shared recovery lane"
            );
            superposition_or_fail_closed(state, goal, target, "decide")?
        }
    };
    state.close_goal(goal, proof_term)?;
    Ok(())
}
