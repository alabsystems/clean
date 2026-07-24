// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment preparation for validating bridge-produced SMT proofs.

use crate::tactic::{ProofState, TacticError};

/// Load theorem declarations that bridge-produced arithmetic proofs may reference.
///
/// Native arithmetic reconstruction uses kernel constants such as `Nat.le_trans`,
/// `Nat.lt_of_lt_of_le`, `Int.le_antisymm`, and `Real.le_trans`. Minimal tactic
/// environments often initialize only the relation/typeclass shells (`init_le`,
/// `init_lt`) without these supporting lemmas, so bridge replay must ensure they
/// are available before kernel validation.
///
/// Covers Nat, Int, and Real order lemmas so that `VerifyStrict + QF_LRA` proof
/// validation succeeds without hidden per-test Real preloading. Part of #2955.
pub(super) fn init_bridge_validation_support(state: &mut ProofState) {
    if let Err(error) = state.env_mut().init_smt_bridge_nat_order_lemmas() {
        tracing::warn!(
            error = %error,
            "failed to initialize Nat order lemmas for bridge proof validation"
        );
    }
    if let Err(error) = state.env_mut().init_int_ord_lemmas() {
        tracing::warn!(
            error = %error,
            "failed to initialize Int order lemmas for bridge proof validation"
        );
    }
    if let Err(error) = state.env_mut().init_real_linear_order() {
        tracing::warn!(
            error = %error,
            "failed to initialize Real linear order for bridge proof validation"
        );
    }
}

/// Prepare the environment for direct-proof kernel validation.
///
/// Native bridge lemmas and classical reasoning are both prerequisites for the
/// selector-side `validate_proof_term(...)` checks used by the ay tactic and
/// certificate lanes.
pub(super) fn prepare_smt_proof_validation(
    state: &mut ProofState,
    tactic_name: &str,
) -> Result<(), TacticError> {
    init_bridge_validation_support(state);
    state
        .env_mut()
        .init_classical()
        .map_err(|error| TacticError::SmtFailed {
            tactic: tactic_name.to_string(),
            detail: format!("classical bootstrap failed before proof reconstruction: {error}"),
        })?;
    Ok(())
}
