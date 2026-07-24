// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-based decision tactics
//!
//! This module provides tactics that use SMT solvers for automated proving:
//! - `decide`: Core SMT-based decision procedure
//! - `ay_omega`: Linear integer arithmetic (QF_LIA)
//! - `ay_bv`: Bitvector reasoning (QF_BV)
//! - `ay_smt`: General theory combination
//! - `ay_decide`: Propositional SAT solving

#[cfg(test)]
use crate::tactic::ProofState;
#[cfg(test)]
use clean_kernel::Name;

mod ay_proof;
#[cfg(feature = "ay-smt")]
mod ay_refutation;
mod ay_solver;
#[cfg(feature = "ay-smt")]
mod ay_solver_translation;
#[cfg(feature = "ay-smt")]
mod ay_solver_types;
mod ay_tactics;
mod ay_types;
#[cfg(feature = "ay-smt")]
pub(crate) mod batch_search;
mod bridge_reconstruction;
mod bridge_validation;
mod decide;
mod reconstruction_gate;
mod selected_proof;
mod trusted_subterms;

#[cfg(test)]
mod ay_contract_ratchet_tests;
#[cfg(all(test, feature = "ay-smt"))]
mod ay_proof_tests;
#[cfg(all(test, feature = "ay-smt"))]
mod ay_solver_tests;
#[cfg(all(test, feature = "ay-smt"))]
mod ay_tactics_tests;
#[cfg(test)]
mod bridge_validation_support_tests;
#[cfg(test)]
mod reconstruction_gate_tests;
#[cfg(test)]
mod selected_proof_accounting_tests;
#[cfg(test)]
mod selected_proof_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod trusted_subterms_tests;

// ============================================================================
// Sorry Tracking (consolidated from clean_kernel::sorry)
// ============================================================================
//
// All sorry tracking is now consolidated in the kernel to ensure consistent
// counting across the codebase. Re-export from kernel for backward compatibility.
//
// See: crates/clean-kernel/src/sorry.rs for the canonical implementation.
// See: #1212 for consolidation rationale.

// Re-export sorry tracking infrastructure from kernel for backward compatibility.
// This ensures all sorry terms are tracked by the same global counter.
pub use clean_kernel::sorry::{
    assert_no_sorry, enable_sorry_location_tracking, reset_sorry_counter, reset_sorry_locations,
    sorry_count, sorry_locations,
};

// Re-export Ay proof counter from kernel — now shared with clean-auto (Part of #1144).
// Previously local to smt.rs, causing clean-auto trustedAy usage to go uncounted.
pub use clean_kernel::sorry::{ay_proof_count, reset_ay_counter};

// Re-export Ay reconstruction failure counter (#2186).
// Tracks how many times proof reconstruction misses the checked recovery lane.
pub use clean_kernel::sorry::{
    ay_reconstruction_failure_count, record_ay_reconstruction_failure,
    reset_ay_reconstruction_failure_counter,
};

// Re-export Ay reconstruction success counter (#2395).
// Tracks how many Ay-proved goals were reconstructed into kernel proofs.
pub use clean_kernel::sorry::{
    ay_reconstruction_success_count, record_ay_reconstruction_success,
    reset_ay_reconstruction_success_counter,
};

// Re-export from kernel — uses infer_sorry_level for correct universe (Part of #2117).
#[cfg(test)]
pub(crate) use clean_kernel::sorry::create_trusted_ay_term;

/// Record the actual trust kind emitted by `create_trusted_ay_term`.
///
/// When the environment does not contain `trustedAy`, the kernel helper falls
/// back to `sorry`; the proof-state ledger must mirror that distinction.
#[cfg(test)]
pub(crate) fn record_trusted_ay_or_sorry(state: &mut ProofState) {
    if state
        .env()
        .get_const(&Name::from_string("trustedAy"))
        .is_some()
    {
        state.record_trusted_ay();
    } else {
        state.record_sorry();
    }
}

// Re-export core decide tactic and helpers
pub use decide::decide;
// try_superposition_fallback is pub(crate) in decide.rs, re-exported for test access
#[cfg(test)]
pub(crate) use decide::try_superposition_fallback;
#[cfg(test)]
pub(crate) use decide::validate_superposition_candidate_for_test;
#[cfg(test)]
pub(crate) fn force_trusted_ay_fail_closed_for_test(
    state: &mut ProofState,
    goal: &crate::tactic::Goal,
    target: &clean_kernel::Expr,
) -> Result<clean_kernel::Expr, crate::tactic::TacticError> {
    decide::force_trusted_ay_fail_closed_for_test(state, goal, target)
}
#[cfg(test)]
pub(crate) fn superposition_or_fail_closed_for_test(
    state: &mut ProofState,
    goal: &crate::tactic::Goal,
    target: &clean_kernel::Expr,
) -> Result<clean_kernel::Expr, crate::tactic::TacticError> {
    decide::superposition_or_fail_closed(state, goal, target, "decide")
}

// Re-export Ay solver
#[cfg(all(test, feature = "ay-smt"))]
pub(crate) use ay_solver::SmtSolver;
// Re-export Ay types
pub use ay_types::{AyConfig, InvalidAyLogicName, SmtVerifyPolicy};

// Re-export Ay tactics
pub use ay_tactics::{ay_bv, ay_decide, ay_lra, ay_omega, ay_smt};

// Re-export Ay proof certificate tactics
pub use ay_proof::{ay_decide_with_lrat_proof, ay_decide_with_proof, AyProofConfig};
