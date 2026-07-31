// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Curated cross-crate ay backend contract — the only supported public in-repo ay API.
//!
//! `clean-elab`, `clean-server`, benches, and future downstream crates all import
//! ay types through this module. The raw backend (`ay_backend`) stays
//! provider-internal behind this explicit re-export list. Part of #2760.

pub use super::ay_backend::{
    certify_kernel_term, deserialize_context, deserialize_term, reconstruct_and_certify_ay_proof,
    serialize_context, serialize_term, verify_alethe_proof, AyBackend, AyBackendConfig, AyError,
    AyLogic, AyProofBackend, AyProofQuality, AyProofResult, AyResult, AySolveEnvelope,
    AySolveResult, AySolveVerification, AyTerm, AyUnknownReason, AyVerificationLevel,
    AyVerificationSummary, CertifiedPayload, KernelReconstructionCandidate, NotCertified,
    ProofProfile, ReconstructionQuality, ReducedContext, ReducedLocalDecl, ResidualTrustSource,
    ResidualTrustSummary, TriggerPolicy, TrustBudget, VariableMapping, VerifyError,
};

// Proof-carrying ay, MILESTONE 2 (BV multiplication): the NATIVE bvmul UNSAT
// kernel-certification surface. Gated with the BV bit-blast lane (`ay-bv-blast`),
// which the consumer (trust-router `ay-certify`) forwards.
#[cfg(feature = "ay-bv-blast")]
pub use super::ay_backend::{
    bvmul_certify_env, bvmul_widening_no_overflow_obligation, certify_bvmul_unsat, BvExpr,
    BvMulCertified, BvMulCertifyError,
};

// Proof-carrying ay, MILESTONE 3 (BV shift): the NATIVE bvshl/bvlshr/bvashr UNSAT
// kernel-certification surface (barrel-shifter bit-blast → OP-AGNOSTIC reflection
// → `Unsat` → Certified modulo 3). Reuses `bvmul_certify_env` for the env.
#[cfg(feature = "ay-bv-blast")]
pub use super::ay_backend::{
    bvshift_identity_obligation, certify_bvshift_unsat, BvShiftCertified, BvShiftCertifyError,
    BVSHIFT_MAX_REFLECTION_STEPS,
};

// Raw ay provider types that appear in AyBackend public method signatures.
// Re-exported here so downstream crates can name them without adding a direct
// `ay` dependency. Part of #3014.
pub use ay::{Model, SolveResult, Sort, Term, UnknownReason};

/// Build identity reported by the AY revision-evidence API linked into Clean.
///
/// This is runtime evidence about the code Cargo actually linked, not an
/// inference from a sibling checkout. Release tooling compares it with the
/// committed `Cargo.toml` and `Cargo.lock` authority and fails closed when the
/// value is unknown, dirty, malformed, or divergent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinkedAyProvenance {
    /// AY's stable revision-evidence kind.
    pub revision_kind: &'static str,
    /// AY build commit embedded by its build script.
    pub revision: &'static str,
}

/// Return revision evidence from the AY library actually linked into Clean.
#[must_use]
pub fn linked_ay_provenance() -> LinkedAyProvenance {
    let readiness =
        ay::symbolic_execution_capability_route_readiness(ay::SolverCapabilityCode::ModelBlocking);
    LinkedAyProvenance {
        revision_kind: readiness.current_ay_revision_kind,
        revision: readiness.current_ay_revision,
    }
}

/// Synthetic trust-envelope constructors for cross-crate test fixtures.
///
/// These builders are only available when the `test-utils` feature is enabled.
/// Production code must use the read-only accessors on the production types.
/// Part of #2773.
#[cfg(feature = "test-utils")]
pub mod test_utils {
    use super::{
        KernelReconstructionCandidate, ReconstructionQuality, ResidualTrustSource,
        ResidualTrustSummary,
    };
    use clean_kernel::{Expr, FVarId};

    /// Create a zero-value `ResidualTrustSummary` with no residual trust debt.
    pub fn empty_residual_trust_summary() -> ResidualTrustSummary {
        ResidualTrustSummary::empty()
    }

    /// Create a `ResidualTrustSummary` from a single residual trust source.
    pub fn residual_trust_summary_from_source(source: ResidualTrustSource) -> ResidualTrustSummary {
        ResidualTrustSummary::from_source(source)
    }

    /// Create a synthetic `KernelReconstructionCandidate` for test fixtures.
    pub fn kernel_reconstruction_candidate(
        refutation: Expr,
        negated_goal_fvar: Option<FVarId>,
        quality: ReconstructionQuality,
        residual: ResidualTrustSummary,
    ) -> KernelReconstructionCandidate {
        KernelReconstructionCandidate::new(refutation, negated_goal_fvar, quality, residual)
    }
}
