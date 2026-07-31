// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DRAT/LRAT Proof Certificate Verifier
//!
//! This module implements verification of DRAT (Deletion Resolution Asymmetric
//! Tautology) and LRAT (Linear RAT) proof certificates produced by SAT solvers
//! like Ay. These proof formats are the standard for certifying UNSAT results.
//!
//! # Kernel Acceptance Policy
//!
//! **LRAT/CLRAT is the official UNSAT certificate format for clean kernel verification.**
//!
//! Policy decision rationale (see `reports/research/2026-02-01-drat-lrat-policy.md`):
//! - LRAT enables O(n) linear-time verification with explicit hints vs O(n²) for DRAT
//! - Formally verified LRAT/CLRAT checkers exist (ACL2, per Varisat docs)
//! - DRAT proofs can be gigabytes and checking time rivals solving time
//! - Clause IDs in LRAT enable efficient checkpoint/resume for AI proof search
//!
//! **Usage guidance:**
//! - For kernel-level trust: Use [`LratVerifier`], [`StreamingLratVerifier`]
//! - For external/transitional use: [`DratVerifier`] is supported but outside TCB
//! - DRAT → LRAT conversion: Use `drat-trim -L` externally before kernel verification
//!
//! # References
//!
//! - drat-trim: <https://github.com/marijnheule/drat-trim>
//! - "Efficient Certified RAT Verification" (Heule et al.)
//! - ay SAT/SMT solver (formerly ay): <https://github.com/alabsystems/ay>
//! - Policy: `reports/research/2026-02-01-drat-lrat-policy.md`

mod drat_verifier;
mod lrat_verifier;
pub mod oracle_conformance;
mod reconstruct;
mod streaming;
mod types;

pub use drat_verifier::DratVerifier;
pub use lrat_verifier::{LratCheckpoint, LratVerifier};
pub use reconstruct::{
    verify_and_reconstruct_drat, verify_and_reconstruct_lrat, ProofReconstructor,
};
pub use streaming::{verify_lrat_streaming, StreamingLratVerifier};
pub use types::{
    CnfFormula, DratError, DratOp, DratProof, DratProofResult, LratOp, LratProof, StepResult,
};

#[cfg(test)]
mod tests;
