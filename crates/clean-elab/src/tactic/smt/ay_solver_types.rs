// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared result and witness-binding types for the SMT solver.

#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::AySolveVerification;
#[cfg(feature = "ay-smt")]
use clean_kernel::{Expr, FVarId, Level};

/// Direct kernel proof reconstructed from a ay Alethe refutation.
///
/// The trust count is only meaningful when this proof exists, so it travels
/// with the reconstructed term instead of as a detached integer on the parent
/// outcome. The typed `ResidualTrustSummary` preserves the source
/// classification computed at reconstruction time so downstream selection
/// and logging can distinguish residual causes. Part of #302, #2618.
#[cfg(feature = "ay-smt")]
#[derive(Debug, Clone)]
pub(super) struct DirectAyKernelProof {
    proof: Expr,
    trust_subterm_count: usize,
    residual: clean_auto::bridge::ay_contract::ResidualTrustSummary,
}

#[cfg(feature = "ay-smt")]
impl DirectAyKernelProof {
    pub(super) fn new(
        proof: Expr,
        trust_subterm_count: usize,
        residual: clean_auto::bridge::ay_contract::ResidualTrustSummary,
    ) -> Self {
        Self {
            proof,
            trust_subterm_count,
            residual,
        }
    }

    pub(super) fn into_parts(
        self,
    ) -> (
        Expr,
        usize,
        clean_auto::bridge::ay_contract::ResidualTrustSummary,
    ) {
        (self.proof, self.trust_subterm_count, self.residual)
    }
}

#[cfg(feature = "ay-smt")]
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone)]
pub(crate) struct ExistsWitnessBinding {
    pub(crate) skolem_smt_name: String,
    pub(crate) source_hyp_fvar: FVarId,
    pub(crate) source_exists_proof: Expr,
    pub(crate) source_exists_levels: Vec<Level>,
    pub(crate) binder_type: Expr,
    pub(crate) predicate: Expr,
    pub(crate) witness_fvar: FVarId,
    pub(crate) witness_proof_fvar: FVarId,
}

/// Result of SMT proving with an optional direct ay kernel proof.
///
/// When `direct_proof()` is `Some`, the proof term is reconstructed from the
/// ay Alethe proof. It may contain embedded `trustedAy` sub-terms for proof
/// steps that ay asserted without SAT-level justification (Trust steps). The
/// trust count is recomputed from the accepted proof term, so callers receive
/// the exact embedded trust debt after reconstruction-gate pruning. When the
/// count is 0, the direct proof is fully kernel-verified.
/// Fast-path trusted solves also retain the ay verification envelope so higher
/// layers do not immediately discard solver-side observability.
/// Part of #302, #2427.
#[cfg(feature = "ay-smt")]
pub(crate) struct SmtProveOutcome {
    /// Whether the proposition was proved (negation is UNSAT).
    pub(crate) proved: bool,
    /// Direct ay kernel proof from Alethe reconstruction (Verifiable path only).
    pub(super) direct_proof: Option<DirectAyKernelProof>,
    /// Solver verification metadata retained from the fast `AyBackend` path.
    pub(crate) solver_verification: Option<AySolveVerification>,
}

#[cfg(feature = "ay-smt")]
impl SmtProveOutcome {
    /// Borrow the direct ay kernel proof, if reconstruction succeeded.
    #[cfg(test)]
    pub(crate) fn direct_proof(&self) -> Option<&Expr> {
        self.direct_proof.as_ref().map(|proof| &proof.proof)
    }

    /// Exact embedded `trustedAy` debt for the direct proof, if present.
    #[cfg(test)]
    pub(crate) fn direct_trust_subterm_count(&self) -> Option<usize> {
        self.direct_proof
            .as_ref()
            .map(|proof| proof.trust_subterm_count)
    }

    pub(crate) fn solver_verification(&self) -> Option<AySolveVerification> {
        self.solver_verification
    }

    pub(super) fn into_direct_proof(self) -> Option<DirectAyKernelProof> {
        self.direct_proof
    }
}
