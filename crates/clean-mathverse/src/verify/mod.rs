// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse submission and training-data API.

// Submodules consolidated under the `verify/` namespace. Callers reach these
// via their canonical paths: `crate::verify::foreign::`,
// `crate::verify::incremental::`, and `crate::verify::integration::`.
pub mod classify;
/// Content fingerprinting for re-import deduplication (the P1 cache key).
pub(crate) mod fingerprint;
pub mod foreign;
pub mod incremental;
pub mod integration;
pub mod kernel_verified_manifest;
/// Re-import verdict-cache population post-pass (P1 brick 3a).
#[cfg(test)]
pub(crate) mod reimport_cache_pass;
pub mod sharded;
/// Merkle trust receipt over a kernel-verified declaration set (P4).
pub mod trust_receipt;
/// Persistent verdict cache keyed by the Merkle-DAG verified hash (P1 brick 2).
#[cfg(test)]
pub(crate) mod verdict_cache;

use crate::error::MathverseResult;
use crate::graph_alpha::ConjectureSource;
use crate::nn_alpha::NNVerificationCert;
use crate::types::{ConjectureIdx, ConstantIdx, ExprIdx, ImportConfidence, SourceSystem};

/// Trust gate for training data export.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustGate {
    /// Only KernelVerified theorems — safe for proof generation training.
    ProofGenEligible,
    /// KernelVerified + Translated — safe for premise selection.
    PremiseSelectEligible,
    /// All trust levels — statement-level data only.
    StatementOnly,
}

/// Training data export record.
#[derive(Clone, Debug)]
pub struct TrainingExport {
    pub name: String,
    pub type_expr: String,
    pub proof_sketch: Option<String>,
    pub source: SourceSystem,
    pub confidence: ImportConfidence,
    pub axiom_profile_bits: u64,
    pub deps: Vec<String>,
    pub trust_gate: TrustGate,
}

/// The submission and training-data API.
///
/// Foreign bytes must first pass through their format-specific ingestion path.
/// This trait accepts reconstructed terms; it does not decode proof formats.
pub trait MathverseVerify {
    /// Submit a closed, monomorphic theorem (type + proof term).
    ///
    /// Both indices refer to the library's expression arena. A proof is required;
    /// the fenced kernel checks it in an empty environment before storage.
    /// Named dependencies (including imported library declarations) and free
    /// universe parameters are refused. Refusal leaves the library unchanged.
    fn submit_proven(
        &mut self,
        name: &str,
        type_expr: ExprIdx,
        proof: ExprIdx,
        source: ConjectureSource,
    ) -> MathverseResult<ConstantIdx>;

    /// Submit a conjecture for the queue.
    fn submit_conjecture(
        &mut self,
        statement: ExprIdx,
        source: ConjectureSource,
    ) -> MathverseResult<ConjectureIdx>;

    /// Submit a neural network verification certificate.
    fn submit_nn_certificate(&mut self, cert: NNVerificationCert) -> MathverseResult<ConstantIdx>;
}
