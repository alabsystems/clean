// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term reconstruction from verified DRAT/LRAT proofs.

use clean_kernel::{Environment, Expr};

use super::drat_verifier::DratVerifier;
use super::lrat_verifier::LratVerifier;
use super::types::{CnfFormula, DratProof, DratProofResult, LratProof};

/// Reconstructs a kernel-checkable proof term from a verified DRAT/LRAT proof.
///
/// The reconstruction strategy:
/// 1. The CNF formula encodes the negation of the goal
/// 2. DRAT/LRAT derives the empty clause (contradiction)
/// 3. We construct a proof of `False` from the resolution chain
/// 4. By `False.elim`, this proves the original goal
///
/// Currently returns `None` (reconstruction not yet implemented). When
/// implemented, the reconstructor will need:
/// - An `Environment` to look up constants (`False.elim`, etc.)
/// - A variable map from SAT indices to Lean expressions
pub struct ProofReconstructor;

impl Default for ProofReconstructor {
    fn default() -> Self {
        Self
    }
}

impl ProofReconstructor {
    /// Create a new proof reconstructor.
    ///
    /// ENSURES: Returns a zero-state reconstructor ready for `reconstruct_unsat_proof`.
    pub fn new() -> Self {
        Self
    }

    /// Construct a proof term for an UNSAT result.
    ///
    /// Given a verified DRAT/LRAT proof that the negation of the goal
    /// is unsatisfiable, construct a proof of the original goal.
    ///
    /// Returns `None` when full reconstruction is not yet implemented.
    /// Callers recover through the checked bridge/superposition lane and now
    /// fail closed if that lane cannot produce a proof.
    ///
    /// Full reconstruction requires:
    /// 1. Resolution chain reconstruction from DRAT
    /// 2. Clause-to-Expr translation
    /// 3. Proof term composition via `@False.elim.{0} goal proof_of_false`
    ///
    /// ENSURES: Currently always returns `None` (reconstruction stub).
    /// ENSURES: When implemented, returned `Some(proof)` will be a well-typed
    ///   `@False.elim.{0} goal proof_of_false` term.
    pub fn reconstruct_unsat_proof(&self, _goal: &Expr) -> Option<Expr> {
        // The DRAT/LRAT proof establishes that the CNF formula is unsatisfiable.
        // The CNF encodes ¬goal, so ¬goal is false, meaning goal is true.
        //
        // The correct proof term is: @False.elim.{0} goal proof_of_false
        // where proof_of_false is derived from the DRAT resolution chain.
        //
        // Full reconstruction not yet implemented — return None so callers
        // can route through the checked bridge/superposition lane. Previously
        // this returned a bare False.elim constant without arguments, which
        // was ill-typed and caused close_goal to reject the term. See #2461.
        None
    }
}

/// Verify DRAT proof and reconstruct proof term.
///
/// **Note:** For kernel-level verification, prefer [`verify_and_reconstruct_lrat`]
/// which provides O(n) verification with explicit hints. DRAT verification is
/// O(n²) in the worst case and is considered outside the Trusted Computing Base.
/// Use this function only for external/transitional compatibility.
///
/// See module-level documentation for the kernel acceptance policy.
///
/// REQUIRES: `formula` is a well-formed CNF formula with consistent `num_vars`.
/// REQUIRES: `proof` operations reference only variables present in `formula`.
/// ENSURES: `result.verified == true` iff `DratVerifier::verify` returns `Ok(true)`.
/// ENSURES: `result.error.is_some()` iff verification failed or returned false.
/// ENSURES: `result.proof_term` is `None` until reconstruction is implemented.
pub fn verify_and_reconstruct_drat(
    _env: &Environment,
    formula: &CnfFormula,
    proof: &DratProof,
    goal: &Expr,
) -> DratProofResult {
    // First verify the DRAT proof
    match DratVerifier::verify(formula, proof) {
        Ok(true) => {
            let reconstructor = ProofReconstructor::new();
            DratProofResult {
                proof_term: reconstructor.reconstruct_unsat_proof(goal),
                verified: true,
                error: None,
            }
        }
        Ok(false) => DratProofResult {
            proof_term: None,
            verified: false,
            error: Some("DRAT verification returned false".to_string()),
        },
        Err(e) => DratProofResult {
            proof_term: None,
            verified: false,
            error: Some(format!("DRAT verification failed: {}", e)),
        },
    }
}

/// Verify LRAT proof and reconstruct proof term.
///
/// **This is the recommended function for kernel-level UNSAT proof verification.**
///
/// LRAT provides O(n) linear-time verification due to explicit clause hints,
/// compared to O(n²) for DRAT. For incremental verification with progress
/// reporting and checkpoint/resume, see [`StreamingLratVerifier`].
///
/// REQUIRES: `formula` is a well-formed CNF formula with consistent `num_vars`.
/// REQUIRES: `proof` hint clause IDs reference valid clause IDs in the derivation.
/// ENSURES: `result.verified == true` iff `LratVerifier::verify` returns `Ok(true)`.
/// ENSURES: `result.error.is_some()` iff verification failed or returned false.
/// ENSURES: `result.proof_term` is `None` until reconstruction is implemented.
pub fn verify_and_reconstruct_lrat(
    _env: &Environment,
    formula: &CnfFormula,
    proof: &LratProof,
    goal: &Expr,
) -> DratProofResult {
    // First verify the LRAT proof
    match LratVerifier::verify(formula, proof) {
        Ok(true) => {
            let reconstructor = ProofReconstructor::new();
            DratProofResult {
                proof_term: reconstructor.reconstruct_unsat_proof(goal),
                verified: true,
                error: None,
            }
        }
        Ok(false) => DratProofResult {
            proof_term: None,
            verified: false,
            error: Some("LRAT verification returned false".to_string()),
        },
        Err(e) => DratProofResult {
            proof_term: None,
            verified: false,
            error: Some(format!("LRAT verification failed: {}", e)),
        },
    }
}
