// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Program verification tool importers for the Mathverse Library (MVP: Dafny + Why3).
//!
//! Parses verification conditions (VCs) from Dafny (via Boogie) and Why3
//! (via WhyML) and writes them to `.mathverse` shard files with trust tracking
//! and axiom profiles.
//!
//! # Module structure
//!
//! - [`types`]: Core types — `VerificationCondition`, `VcFormula`, `ProgramSpec`
//! - [`boogie`]: Boogie VC parser (Dafny backend format)
//! - [`whyml`]: WhyML VC parser (Why3 VC export format)
//! - [`shard_writer`]: Write program VCs to `.mathverse` shards

pub mod boogie;
pub mod shard_writer;
pub mod types;
pub mod whyml;

// Re-export key types for convenience.
pub use boogie::parse_boogie_vcs;
pub use shard_writer::{write_program_vcs_to_file, write_program_vcs_to_shard, ShardStats};
pub use types::{
    ProgramSpec, ProgramVerifyStats, VcFormula, VcFormulaKind, VcProofResult, VcStatus,
    VerificationCondition,
};
pub use whyml::parse_whyml_vcs;
