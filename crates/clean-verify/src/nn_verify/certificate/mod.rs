// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate composition for whole-network proofs (C007: T70-T72, T09).
//!
//! This is the single most valuable module in the entire NN verification
//! proof engine. T70 (entailment_transitivity) enables chaining per-block
//! Farkas certificates into whole-network proofs.
//!
//! ## Pipeline
//!
//! 1. gamma-crown verifies block N and emits Farkas certificate:
//!    "input ∈ [lN, uN] => output ∈ [lN+1, uN+1]"
//! 2. clean verifies each certificate via `verify_farkas_certificate()`
//!    (already implemented in `clean-elab/src/cert/external/verify.rs`)
//! 3. clean chains N certificates via T70 (entailment transitivity)
//! 4. Result: machine-checked proof that network maps input bounds to output bounds

pub(crate) mod chain;
pub mod composition;
pub mod compositional;
pub mod farkas_bridge;
pub mod farkas_chain;
pub(crate) mod network_sound;
pub mod pipeline;
pub mod verify;

#[cfg(test)]
mod tests_chain;
#[cfg(test)]
mod tests_composition;
#[cfg(test)]
mod tests_compositional;
#[cfg(test)]
mod tests_farkas_chain;
#[cfg(test)]
mod tests_integration;
#[cfg(test)]
mod tests_network_sound;
#[cfg(test)]
mod tests_pipeline;
#[cfg(test)]
mod tests_verify;

pub use composition::{compose_entailment_certs, ComposedCert, CompositionError};
pub use farkas_bridge::{
    box_constraints_to_interval, farkas_to_interval, interval_to_box_constraints,
    verify_farkas_certificate, ExternalFarkasCert, FarkasBridgeError, FarkasVerifyResult,
};
pub use farkas_chain::chain_farkas_certs;
pub use pipeline::{verify_and_compose_pipeline, PipelineError, PipelineResult};

pub use chain::{
    chain_trust_level, format_chain_summary, merge_chains, verify_chain_continuity,
    verify_chain_coverage, CertificateChain, CertificateEntry, ChainTrustLevel, VerificationMethod,
};

use crate::spec::ProofStatus;

/// T70: entailment_transitivity
///
/// If cert_1 proves A => B and cert_2 proves B => C, then A => C.
///
/// This is the transitivity of entailment for convex polyhedral sets
/// described by linear constraints. Each certificate establishes
/// "input ∈ polyhedron_1 => output ∈ polyhedron_2" via non-negative
/// linear combination (Farkas lemma). Chaining two certificates is
/// concatenating the Farkas multipliers.
///
/// Proof: For each `i : Fin d`, combine `le_trans` on lower/upper bounds
/// with `AndType.intro`. Zero bridging axioms -- uses `Rat.le_trans` directly
/// since #3222 fixed projection reduction.
/// Proved in `clean-kernel/src/env/nn_verify_proofs.rs` as `entailment_transitivity`.
pub const T70_ENTAILMENT_TRANSITIVITY: ProofStatus = ProofStatus::DerivedPending;

/// T71: network_cert_sound
///
/// N chained block certificates => whole-network bound.
///
/// Proof: Induction on the number of blocks, applying T70 at each step.
///
/// ```text
/// theorem network_cert_sound (certs : Fin N -> BlockCertificate)
///   (chained : ∀ i, certs i . output_bounds = certs (i+1) . input_bounds) :
///   ∀ x, certs 0 . input_bounds . contains x ->
///     certs (N-1) . output_bounds . contains (network_eval x)
/// ```
pub const T71_NETWORK_CERT_SOUND: ProofStatus = network_sound::T71_PROOF_STATUS;

/// T72: cert_composition_preserves_trust
///
/// Composed certificate inherits the maximum axiom profile (bitwise OR)
/// of all component certificates.
///
/// ```text
/// theorem cert_composition_preserves_trust (certs : ListType BlockCertificate) :
///   (compose_certs certs).axiom_profile = certs.foldl (.|.) 0
/// ```
///
/// Proved in `clean-kernel/src/env/nn_verify_proofs.rs` as `cert_composition_trust`.
/// The proof registers the pairwise composition property as a kernel theorem:
/// for all c1 c2, axiomProfile(composePair c1 c2) = Nat.lor(axiomProfile c1)(axiomProfile c2).
/// The proof term applies the composePair_axiomProfile axiom directly.
/// Machine-checked by the clean type checker (infer_type + is_def_eq).
pub const T72_CERT_COMPOSITION_TRUST: ProofStatus = ProofStatus::DerivedPending;

/// T09: farkas_to_interval
///
/// Bridge from ExternalFarkasCert (Rust-verified multiplier matrix) to
/// the formalized IntervalBounds type. Required for the certificate
/// composition pipeline to connect Track A (formal proofs) and Track B
/// (certificate replay).
pub const T09_FARKAS_TO_INTERVAL: ProofStatus = ProofStatus::DerivedPending;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        // T70 has a kernel proof (zero bridging axioms)
        assert!(matches!(
            T70_ENTAILMENT_TRANSITIVITY,
            ProofStatus::DerivedPending
        ));
        // T71 proved via structural induction on ListType intermediates
        assert!(matches!(
            T71_NETWORK_CERT_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T72_CERT_COMPOSITION_TRUST,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T09_FARKAS_TO_INTERVAL,
            ProofStatus::DerivedPending
        ));
    }
}
