// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term validation for the SMT decide tactic.
//!
//! Kernel type-checking of SMT-reconstructed proof terms ensures soundness:
//! even a correct SMT result must produce a kernel-valid proof before closing
//! a goal.

use crate::tactic::{Goal, ProofState, TacticError};
use clean_kernel::{Expr, TypeChecker};

/// Validate a proof term against the kernel type checker.
///
/// This is a critical soundness check: even if the SMT solver proves a goal,
/// the reconstructed proof term must type-check in the kernel to be accepted.
///
/// Returns Ok(proof_term) if the proof is valid, Err with details otherwise.
///
/// # Contract
///
/// REQUIRES: `proof` is a candidate proof term for `expected_type`
/// REQUIRES: `goal` provides the local context for type checking
/// ENSURES: On Ok, `infer_type(proof) =def= expected_type` (kernel-verified)
/// ENSURES: On Err(TypeCheckFailed), proof term is ill-typed
/// ENSURES: On Err(TypeMismatch), proof type does not match expected type
pub(in crate::tactic::smt) fn validate_proof_term(
    state: &ProofState,
    goal: &Goal,
    proof: &Expr,
    expected_type: &Expr,
) -> Result<Expr, TacticError> {
    // Build the local context for type checking
    let ctx = state.build_local_ctx(goal);
    let tc = TypeChecker::with_context(state.env(), ctx);

    // Instantiate metavariables in the proof term
    let instantiated_proof = state.metas.instantiate(proof);

    // Try to infer the type of the proof
    let inferred_type = tc.infer_type(&instantiated_proof).map_err(|e| {
        TacticError::TypeCheckFailed(format!("proof term failed type inference: {e:?}"))
    })?;

    // Normalize both sides through typeclass projections before comparing.
    // Arithmetic bridge proofs often infer direct `Nat.le` / `Nat.lt` types
    // while tactic goals remain in typeclass form (`@LE.le Nat instLENat ...`).
    // `is_def_eq` alone does not reliably reduce that projection chain here,
    // so mirror `close_goal()` and compare WHNF-normalized types.
    let inferred_type = tc.whnf(&inferred_type);

    // Check that the inferred type matches the expected type (goal)
    let instantiated_expected = state.metas.instantiate(expected_type);
    let instantiated_expected = tc.whnf(&instantiated_expected);
    if tc.is_def_eq(&inferred_type, &instantiated_expected) {
        Ok(instantiated_proof)
    } else {
        Err(TacticError::TypeMismatch {
            expected: format!("{instantiated_expected:?}"),
            actual: format!("{inferred_type:?}"),
        })
    }
}
