// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # clean-autoform — the autoformalization honesty shell (M1 + M2)
//!
//! This crate computes a two-meter trust label for autoformalized source: a
//! **proof-depth** meter (proved, modulo the named trusted models + foundational
//! axioms) reported **side by side** with an **inference** meter (validated,
//! disclosed). It implements the honesty rails that keep a validation result
//! from masquerading as a proof.
//!
//! The map formerly called "R" — the verified meaning-map
//! `<<.>> : trust-ir -> CIC` reflecting trust-ir operational semantics into the
//! kernel's logic — is the **SemanticReflection** model. The three named trusted
//! models are `{ISA model, runtime model, semantic-reflection model}`.
//!
//! ## The 7 honesty rails (non-negotiable, design section 12)
//!
//! 1. **Proof below the Rust waist, validation above.** Below the Rust waist =
//!    PROOF to a formal ISA (modulo named axioms); above = VALIDATION, never proof.
//! 2. **Two meters never fused.** The proof-depth closure (proved, modulo
//!    `{ISA, runtime, SemanticReflection, 3 foundational axioms}`) and the
//!    inference meter (validated) are reported SIDE BY SIDE. `*Certified*` labels
//!    gate on proof-depth + PHASE ONLY; the inference meter is disclosure, NEVER
//!    an IFF precondition. Fusing them is the cardinal error.
//! 3. **General SemanticReflection is trusted/unverified.** SemanticReflection +
//!    MIR-op-sem is TRUSTED/UNVERIFIED for the GENERAL map; never claim "verified
//!    reflection" for the general case.
//! 4. **A FLAW requires a concrete counterexample.** A failed proof without one
//!    is *unknown*, never a FLAW.
//! 5. **IMPROVEMENT vs FLAW is intent-relative, not kernel-decidable.** Ship the
//!    mechanical fact (checked) separately from the intent tag (disclosed).
//! 6. **Oracle/runtime evidence caps at `RuntimeObserved`.** `RuntimeObserved`
//!    can NEVER satisfy a `Certified` requirement.
//! 7. **Outside the modeled fragment FAILS CLOSED.** No kernel Dynamic type; the
//!    static-universal claim is withheld.

#![forbid(unsafe_code)]

pub(crate) mod badge;
pub(crate) mod bundle;
pub(crate) mod divergence;
pub(crate) mod enforcement;
pub(crate) mod inference_meter;
pub(crate) mod phase;

#[cfg(test)]
mod tests;

pub use badge::{
    compute_badge, BadgeReport, DivergenceSummary, InferenceSummary, Label, ProofDepthSummary,
    ProofFloor, TrustedModels,
};
pub use bundle::FormalizedSourceBundle;
pub use divergence::{DivergenceClosure, RefinementDivergenceKind, TaggedRefinement};
pub use enforcement::{
    evidence_satisfies, runtime_never_satisfies_certified, runtime_observed_strength,
};
pub use inference_meter::InferenceMeter;
pub use phase::Phase;

/// Errors raised by the honesty shell.
///
/// `#[non_exhaustive]`: more failure modes may be added as the shell grows.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A static-universal claim was requested for input that falls outside the
    /// modeled fragment (rail 7: fail closed — the claim is withheld).
    #[error("outside the modeled fragment: {0} — static-universal claim withheld (fail closed)")]
    OutsideModeledFragment(String),

    /// Runtime/oracle evidence was offered where a certified requirement was
    /// demanded (rail 6).
    #[error("runtime-observed evidence cannot satisfy a certified requirement")]
    RuntimeCannotCertify,
}
