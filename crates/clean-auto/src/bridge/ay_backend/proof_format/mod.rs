// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof format types, version constants, and proof profiles for SMT verification.
//!
//! Split into focused modules:
//! - [`format`]: `ProofFormat` enum, `proof_formats` constants, format helpers
//! - [`profile`]: `ProofProfile` runtime UNSAT-acceptance policy

pub(super) mod format;
mod profile;

// Re-export ProofProfile publicly (part of the ay_contract surface).
pub use profile::ProofProfile;

// Re-export format types for test submodules (tests_proof_format.rs uses `super::proof_format::*`).
#[cfg(test)]
pub(super) use format::{proof_formats, ProofFormat};
