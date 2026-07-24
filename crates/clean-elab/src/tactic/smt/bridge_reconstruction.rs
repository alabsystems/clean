// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge reconstruction helpers shared by `decide` and the Ay wrapper tactics.

#[cfg(all(test, feature = "ay-smt"))]
use std::cell::RefCell;

use crate::tactic::{Goal, ProofState, TacticError};
use clean_kernel::Expr;

#[cfg(feature = "ay-smt")]
use super::bridge_validation::init_bridge_validation_support;
use super::decide::superposition_or_fail_closed;
#[cfg(feature = "ay-smt")]
use super::decide::{add_hypotheses_from_context, validate_proof_term};
#[cfg(feature = "ay-smt")]
use super::selected_proof::record_selected_proof_trust_with_expected;
#[cfg(feature = "ay-smt")]
use super::trusted_subterms::count_embedded_trusted_ay_terms;

/// Trust requirement for bridge recovery candidates.
///
/// Controls whether `attempt_bridge_reconstruction` accepts any bridge candidate
/// or only zero-trust candidates (those with `trust_subterm_count == 0`).
/// Part of #2684.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RecoveryTrustRequirement {
    /// Accept any bridge candidate regardless of embedded trust debt.
    Any,
    /// Accept only candidates with `trust_subterm_count == 0`.
    ZeroTrust,
}

impl RecoveryTrustRequirement {
    /// Check whether `candidate` meets this trust requirement.
    #[cfg(any(feature = "ay-smt", test))]
    fn accepts(self, candidate: &BridgeReconstructionCandidate) -> bool {
        match self {
            Self::Any => true,
            Self::ZeroTrust => candidate.trust_subterm_count == 0,
        }
    }
}

/// A validated bridge proof plus its embedded `trustedAy` debt.
#[cfg(any(feature = "ay-smt", test))]
#[derive(Debug, Clone)]
pub(super) struct BridgeReconstructionCandidate {
    #[cfg_attr(not(feature = "ay-smt"), allow(dead_code))]
    pub(super) proof: Expr,
    pub(super) trust_subterm_count: usize,
}

/// Outcome of a bridge reconstruction probe.
///
/// Distinguishes "valid candidate found" from "candidate produced but rejected
/// by kernel" from "bridge could not produce any proof."  Non-recovery callers
/// flatten this to `Option<BridgeReconstructionCandidate>` via `into_candidate()`.
/// Part of #2920.
#[cfg(feature = "ay-smt")]
#[derive(Debug, Clone)]
pub(super) enum BridgeProbeOutcome {
    /// Kernel validation succeeded — caller decides whether to accept.
    Candidate(BridgeReconstructionCandidate),
    /// Bridge produced a proof but kernel validation rejected it.
    ValidationFailed,
    /// Bridge could not produce a proof at all (Unverified, Unknown, error).
    NoProof,
}

#[cfg(feature = "ay-smt")]
impl BridgeProbeOutcome {
    /// Flatten to `Option`, discarding the failure distinction.
    pub(super) fn into_candidate(self) -> Option<BridgeReconstructionCandidate> {
        match self {
            Self::Candidate(c) => Some(c),
            _ => None,
        }
    }
}

#[cfg(all(test, feature = "ay-smt"))]
thread_local! {
    static TEST_BRIDGE_RECONSTRUCTION_OUTCOME: RefCell<Option<BridgeProbeOutcome>> =
        const { RefCell::new(None) };
}

#[cfg(all(test, feature = "ay-smt"))]
pub(super) struct TestBridgeCandidateGuard;

#[cfg(all(test, feature = "ay-smt"))]
impl Drop for TestBridgeCandidateGuard {
    fn drop(&mut self) {
        TEST_BRIDGE_RECONSTRUCTION_OUTCOME.with(|slot| {
            *slot.borrow_mut() = None;
        });
    }
}

#[cfg(all(test, feature = "ay-smt"))]
pub(super) fn install_test_bridge_candidate(
    candidate: BridgeReconstructionCandidate,
) -> TestBridgeCandidateGuard {
    install_test_bridge_probe_outcome(BridgeProbeOutcome::Candidate(candidate))
}

#[cfg(all(test, feature = "ay-smt"))]
pub(super) fn install_test_bridge_probe_outcome(
    outcome: BridgeProbeOutcome,
) -> TestBridgeCandidateGuard {
    TEST_BRIDGE_RECONSTRUCTION_OUTCOME.with(|slot| {
        let mut slot = slot.borrow_mut();
        assert!(
            slot.is_none(),
            "test bridge reconstruction outcome override should not be nested"
        );
        *slot = Some(outcome);
    });
    TestBridgeCandidateGuard
}

#[cfg(all(test, feature = "ay-smt"))]
fn cloned_test_bridge_probe_outcome() -> Option<BridgeProbeOutcome> {
    TEST_BRIDGE_RECONSTRUCTION_OUTCOME.with(|slot| slot.borrow().clone())
}

/// Record success/trust accounting for a bridge proof that the caller chose to use.
#[cfg(feature = "ay-smt")]
pub(super) fn accept_bridge_reconstruction_candidate(
    state: &mut ProofState,
    candidate: BridgeReconstructionCandidate,
    tactic_name: &str,
) -> Expr {
    let BridgeReconstructionCandidate {
        proof,
        trust_subterm_count,
    } = candidate;
    let recorded_trust = record_selected_proof_trust_with_expected(
        state,
        &proof,
        trust_subterm_count,
        tactic_name,
        "bridge",
    );
    super::record_ay_reconstruction_success();
    tracing::info!(
        tactic = tactic_name,
        trust_subterm_count = recorded_trust,
        "bridge reconstruction succeeded without whole-goal trustedAy fallback"
    );
    proof
}

/// Attempt proof reconstruction via the native SmtBridge when Ay has already
/// confirmed UNSAT, subject to a trust requirement on the bridge candidate.
///
/// When the bridge candidate does not meet the requirement, logs the rejection
/// and continues to the superposition → fail-closed recovery lane.
/// Part of #2395, #2659, #2684.
///
/// # Contract
///
/// ENSURES: On Ok, returns a proof term chosen from bridge/superposition
/// ENSURES: On Err, the checked recovery lane is exhausted and the goal stays open
#[cfg(feature = "ay-smt")]
pub(super) fn attempt_bridge_reconstruction_with_requirement(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
    requirement: RecoveryTrustRequirement,
) -> Result<Expr, TacticError> {
    match try_bridge_reconstruction_candidate(state, goal, target, tactic_name) {
        BridgeProbeOutcome::Candidate(candidate) => {
            if requirement.accepts(&candidate) {
                return Ok(accept_bridge_reconstruction_candidate(
                    state,
                    candidate,
                    tactic_name,
                ));
            }
            tracing::info!(
                tactic = tactic_name,
                trust_subterm_count = candidate.trust_subterm_count,
                ?requirement,
                "strict recovery rejected trusted bridge candidate; continuing to superposition"
            );
        }
        BridgeProbeOutcome::ValidationFailed => {
            state.record_invalid_bridge_candidate();
        }
        BridgeProbeOutcome::NoProof => {}
    }
    let proof = superposition_or_fail_closed(state, goal, target, tactic_name)?;
    super::record_ay_reconstruction_success();
    tracing::info!(
        tactic = tactic_name,
        ?requirement,
        "bridge recovery succeeded via superposition fallback"
    );
    Ok(proof)
}

/// Attempt proof reconstruction via the native SmtBridge when Ay has already
/// confirmed UNSAT. Falls back through superposition and then fails closed if
/// no kernel proof can be reconstructed. Part of #2395, #2659.
///
/// # Contract
///
/// ENSURES: On Ok, returns a proof term chosen from bridge/superposition
/// ENSURES: On Err, the checked recovery lane is exhausted and the goal stays open
#[cfg(feature = "ay-smt")]
pub(super) fn attempt_bridge_reconstruction(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
) -> Result<Expr, TacticError> {
    attempt_bridge_reconstruction_with_requirement(
        state,
        goal,
        target,
        tactic_name,
        RecoveryTrustRequirement::Any,
    )
}

/// Recover a verified SMT goal when the original certificate path did not
/// produce a direct kernel proof, subject to a trust requirement on any bridge
/// candidate discovered during recovery.
///
/// With `ay-smt` enabled, prefer the native bridge first because it preserves
/// the direct-vs-bridge trust-accounting policy from the main ay tactic lane.
/// Without that feature, fall back to the shared superposition → fail-closed
/// recovery lane (the requirement is unused in that case).
/// Part of #302, #2659, #2684.
pub(super) fn recover_verified_goal_after_reconstruction_gap_with_requirement(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
    requirement: RecoveryTrustRequirement,
) -> Result<Expr, TacticError> {
    #[cfg(feature = "ay-smt")]
    {
        attempt_bridge_reconstruction_with_requirement(
            state,
            goal,
            target,
            tactic_name,
            requirement,
        )
    }

    #[cfg(not(feature = "ay-smt"))]
    {
        let _ = requirement;
        superposition_or_fail_closed(state, goal, target, tactic_name)
    }
}

/// Recover a verified SMT goal when the original certificate path did not
/// produce a direct kernel proof.
///
/// With `ay-smt` enabled, prefer the native bridge first because it preserves
/// the direct-vs-bridge trust-accounting policy from the main ay tactic lane.
/// Without that feature, fall back to the shared superposition → fail-closed
/// recovery lane. Part of #302, #2659.
///
/// Production callers now use `_with_requirement` directly; this permissive
/// wrapper is retained for test convenience (e.g. `tests.rs` fail-closed
/// regression).
#[cfg(test)]
pub(super) fn recover_verified_goal_after_reconstruction_gap(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
) -> Result<Expr, TacticError> {
    recover_verified_goal_after_reconstruction_gap_with_requirement(
        state,
        goal,
        target,
        tactic_name,
        RecoveryTrustRequirement::Any,
    )
}

/// Try to reconstruct a kernel proof term via the native SmtBridge.
///
/// Returns a [`BridgeProbeOutcome`] distinguishing validation success,
/// validation failure, and "no proof produced."  This function is a shared
/// probe used by both recovery and non-recovery selection paths — it does
/// NOT mutate recovery accounting.  Callers at recovery-only boundaries
/// should inspect `ValidationFailed` and record accordingly.
/// Part of #2395, #302, #2920.
#[cfg(feature = "ay-smt")]
pub(super) fn try_bridge_reconstruction_candidate(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic_name: &str,
) -> BridgeProbeOutcome {
    #[cfg(all(test, feature = "ay-smt"))]
    if let Some(outcome) = cloned_test_bridge_probe_outcome() {
        return outcome;
    }

    use clean_auto::bridge::SmtBridge;

    let mut bridge = SmtBridge::new(state.env());
    bridge.set_local_ctx(state.build_local_ctx(goal));
    add_hypotheses_from_context(state, goal, &mut bridge);

    match bridge.prove(target) {
        Ok(clean_auto::bridge::SmtVerificationResult::Verified(proof_result)) => {
            init_bridge_validation_support(state);
            match validate_proof_term(state, goal, proof_result.proof_term(), target) {
                Ok(proof) => BridgeProbeOutcome::Candidate(BridgeReconstructionCandidate {
                    trust_subterm_count: count_embedded_trusted_ay_terms(&proof),
                    proof,
                }),
                Err(e) => {
                    tracing::warn!(
                        tactic = tactic_name,
                        error = %e,
                        "bridge proof failed kernel validation"
                    );
                    BridgeProbeOutcome::ValidationFailed
                }
            }
        }
        Ok(clean_auto::bridge::SmtVerificationResult::Unverified { .. }) => {
            tracing::debug!(
                tactic = tactic_name,
                "bridge UNSAT but no kernel proof, trying superposition"
            );
            BridgeProbeOutcome::NoProof
        }
        _ => {
            tracing::debug!(
                tactic = tactic_name,
                "bridge could not prove, trying superposition"
            );
            BridgeProbeOutcome::NoProof
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_recovery_trust_requirement_any_accepts_trusted_candidate() {
        let candidate = BridgeReconstructionCandidate {
            proof: Expr::prop(),
            trust_subterm_count: 3,
        };
        assert!(
            RecoveryTrustRequirement::Any.accepts(&candidate),
            "Any should accept candidates with trust debt"
        );
    }

    #[test]
    fn test_recovery_trust_requirement_zero_trust_rejects_trusted_candidate() {
        let candidate = BridgeReconstructionCandidate {
            proof: Expr::prop(),
            trust_subterm_count: 1,
        };
        assert!(
            !RecoveryTrustRequirement::ZeroTrust.accepts(&candidate),
            "ZeroTrust should reject candidates with trust_subterm_count > 0"
        );
    }

    #[test]
    fn test_recovery_trust_requirement_zero_trust_accepts_clean_candidate() {
        let candidate = BridgeReconstructionCandidate {
            proof: Expr::prop(),
            trust_subterm_count: 0,
        };
        assert!(
            RecoveryTrustRequirement::ZeroTrust.accepts(&candidate),
            "ZeroTrust should accept candidates with trust_subterm_count == 0"
        );
    }
}
