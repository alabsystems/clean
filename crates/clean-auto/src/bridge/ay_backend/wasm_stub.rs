// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! wasm32 replacement root for the ay backend (`mod.rs` stays native-only).
//!
//! The ay solver crates have no wasm32 port (libc signal APIs, native-only
//! timers), so on wasm this tree compiles only the ay-free pieces of the
//! backend — reused verbatim where the source file never touches ay, and
//! mirrored (`wasm_surface.rs`, `wasm_proof_reconstruct.rs`) where the native
//! file owns solver handles. Every solver entry point is native-only; the
//! curated `ay_contract` exports the pure-data subset re-exported below.

// Real, ay-free submodules reused verbatim.
#[path = "config.rs"]
mod config;
#[path = "proof_format/mod.rs"]
mod proof_format;
#[path = "reconstruction_quality.rs"]
mod reconstruction_quality;
#[path = "solve_types.rs"]
mod solve_types;
#[path = "triggers.rs"]
mod triggers;

// Pure-data mirrors of the ay-entangled definition sites.
#[path = "wasm_proof_backend.rs"]
mod proof_backend;
#[path = "wasm_proof_reconstruct.rs"]
mod proof_reconstruct;
#[path = "wasm_surface.rs"]
mod surface;

pub use config::AyBackendConfig;
pub use proof_backend::{
    verify_alethe_proof, AyProofBackend, AyProofQuality, AyProofResult, VerifyError,
};
pub use proof_format::ProofProfile;
pub use proof_reconstruct::VariableMapping;
pub use reconstruction_quality::{
    KernelReconstructionCandidate, ReconstructionQuality, ResidualTrustSource,
    ResidualTrustSummary, TrustBudget,
};
pub use solve_types::{
    AySolveEnvelope, AySolveResult, AySolveVerification, AyUnknownReason, AyVerificationLevel,
    AyVerificationSummary,
};
pub use surface::{AyBackend, AyError, AyLogic, AyResult, AyTerm};
pub use triggers::TriggerPolicy;
