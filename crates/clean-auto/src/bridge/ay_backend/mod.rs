// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay SMT Backend for clean
//!
//! Integrates the ay SMT solver (a Rust port of Z3) with clean's tactic framework.
//! Uses ay-translate for unified term translation patterns shared with other consumers.
//!
//! This module provides:
//! - `AyBackend`: SMT solving using ay-translate's TranslationSession
//! - Translation from kernel `Expr` to ay `Term`
//! - Support for QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_BV, QF_AUFLIA logics (quantifier-free)
//! - Support for UF, UFLIA logics (with quantifiers and E-matching)
//! - ALL logic for auto-detection of theories from terms
//! - `AyTriggerPattern` and `TriggerPolicy` for explicit trigger control
//!
//! # Feature Flag
//!
//! This module requires the `ay-smt` feature:
//!
//! ```toml
//! [dependencies]
//! clean-auto = { version = "0.1", features = ["ay-smt"] }
//! ```

// --- Implementation leaves ---
mod carcara_verify;
mod concrete_real;
mod config;
mod proof_backend;
mod proof_format;
pub(crate) mod proof_reconstruct;
mod reconstruction_quality;
pub(crate) mod smtlib_builder;
mod solve_types;
mod solver;
mod sort_guard;
mod surface;
mod term_handle;
mod term_ops;
mod translate;
mod translate_arithmetic;
pub(crate) mod translator;
mod triggers;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_consumer_acceptance;
#[cfg(test)]
mod tests_goals;
#[cfg(test)]
mod tests_proof_backend;
#[cfg(test)]
mod tests_proof_format;
#[cfg(test)]
mod tests_quantifiers;
#[cfg(test)]
mod tests_solve_provenance;
#[cfg(test)]
mod tests_translate;
#[cfg(test)]
mod tests_translate_traits;

// --- Public re-exports (stable ay_backend / ay_contract surface) ---
pub use carcara_verify::verify_alethe_proof;
pub use config::AyBackendConfig;
pub use proof_backend::{AyProofBackend, AyProofQuality, AyProofResult, VerifyError};
pub use proof_format::ProofProfile;
pub use proof_reconstruct::certified_proof::{
    certify_kernel_term, deserialize_context, deserialize_term, reconstruct_and_certify_ay_proof,
    serialize_context, serialize_term, CertifiedPayload, NotCertified, ReducedContext,
    ReducedLocalDecl,
};
// Proof-carrying ay, MILESTONE 2 (BV multiplication): NATIVE kernel certification
// of a bvmul UNSAT obligation via array-multiplier bit-blast reflection. Gated
// with the BV bit-blast lane.
#[cfg(feature = "ay-bv-blast")]
pub use proof_reconstruct::pcay_bvmul::{
    bvmul_certify_env, bvmul_widening_no_overflow_obligation, certify_bvmul_unsat, BvMulCertified,
    BvMulCertifyError, MAX_REFLECTION_STEPS as BVMUL_MAX_REFLECTION_STEPS,
};
// Proof-carrying ay, MILESTONE 3 (BV shift): the NATIVE bvshl/bvlshr/bvashr UNSAT
// kernel-certification surface. Reuses the milestone-2 op-agnostic reflection.
#[cfg(feature = "ay-bv-blast")]
pub use proof_reconstruct::pcay_bvshift::{
    bvshift_identity_obligation, certify_bvshift_unsat, BvShiftCertified, BvShiftCertifyError,
    MAX_REFLECTION_STEPS as BVSHIFT_MAX_REFLECTION_STEPS,
};
// Re-export ay's BvExpr fragment so downstream (trust-router) can name bvmul
// obligations without a direct `ay-proof` dependency. Gated with the BV lane.
#[cfg(feature = "ay-bv-blast")]
pub use ay_proof::bv_blast_solver::BvExpr;
pub use proof_reconstruct::VariableMapping;
pub use reconstruction_quality::{
    KernelReconstructionCandidate, ReconstructionQuality, ResidualTrustSource,
    ResidualTrustSummary, TrustBudget,
};
pub use solve_types::{
    AyProofCertificateInfo, AySolveEnvelope, AySolveResult, AySolveVerification, AyUnknownReason,
    AyVerificationLevel, AyVerificationSummary,
};
pub use surface::{AyBackend, AyError, AyLogic, AyResult};
pub use term_handle::AyTerm;
pub use triggers::TriggerPolicy;

// --- Crate-internal re-exports (sibling modules use `super::*`) ---
pub(crate) use sort_guard::{
    bignat_to_bigint, infer_sort_from_lean_type, reject_unsound_domain_ty,
};
pub(crate) use surface::panic_payload_to_string;

// Backend-internal re-exports: not part of the curated ay_contract surface but
// needed by ay_backend test submodules (tests use `use super::*`). Part of #2774.
#[cfg(test)]
use proof_format::{proof_formats, ProofFormat};
#[cfg(test)]
use triggers::{AyTriggerPattern, SmtlibTriggerPattern};
