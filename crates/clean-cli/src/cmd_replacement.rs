// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean replacement ...` command group for the Lean4 replacement launch gate.
//!
//! Split into focused submodules (each under the 500-line paragon limit);
//! every submodule re-exports through this root so the module surface seen
//! by the rest of the crate (`handle_replacement_command`,
//! `ReplacementCommands`, `FEATURES`) is unchanged.

mod artifact_io;
mod artifact_types;
mod cert_gates;
mod cli;
mod consts;
mod corpus_discovery;
mod corpus_fixture;
mod corpus_manifest;
mod evidence_generation;
mod features;
mod features_catalog;
mod gate_checks;
mod generated_cases;
mod generated_cases_ext;
mod handlers;
mod informational;
mod launch_evidence;
mod launch_validation;
mod readiness;
mod release_issue_report;
mod release_issue_rules;
mod render;
mod render_evidence;
mod report_validation;
mod report_validators;
mod reviewer_deck;
mod rows;
mod sorry_bypass_lint;
mod sorry_bypass_syntax;
mod tactic_count_artifact;
mod tactic_count_consistency;
mod tactic_count_fingerprints;
mod tactic_parity_types;
mod tactic_rows;
mod tactic_summaries;
mod trust_boundary;
mod trust_core_report;
mod wrapper_free_checks;
mod wrapper_free_gate;

#[cfg(test)]
mod tests;

// Shared imports re-exported so submodules can `use super::*;` exactly like
// the original single-file module body did.
pub(crate) use std::collections::{BTreeMap, BTreeSet};
pub(crate) use std::fs;
pub(crate) use std::io::{self, Write};
pub(crate) use std::path::{Path, PathBuf};
pub(crate) use std::process::Command;

pub(crate) use clap::{Args, Subcommand, ValueEnum};
pub(crate) use clean_features::{
    Category, Example, FeatureDescriptor, RefKind, Reference, Stability,
};
pub(crate) use serde::{Deserialize, Serialize};
pub(crate) use sha2::{Digest, Sha256};
pub(crate) use walkdir::WalkDir;

pub(crate) use crate::cmd_native_library::{
    handle_native_library_command, NativeLibraryCommands, NativeLibraryError,
};

pub(crate) use self::artifact_io::*;
pub(crate) use self::artifact_types::*;
pub(crate) use self::cert_gates::*;
pub(crate) use self::cli::*;
pub(crate) use self::consts::*;
pub(crate) use self::corpus_discovery::*;
pub(crate) use self::corpus_fixture::*;
pub(crate) use self::corpus_manifest::*;
pub(crate) use self::evidence_generation::*;
pub(crate) use self::features::*;
pub(crate) use self::features_catalog::*;
pub(crate) use self::gate_checks::*;
pub(crate) use self::generated_cases::*;
pub(crate) use self::generated_cases_ext::*;
pub(crate) use self::handlers::*;
pub(crate) use self::informational::*;
pub(crate) use self::launch_evidence::*;
pub(crate) use self::launch_validation::*;
pub(crate) use self::readiness::*;
pub(crate) use self::release_issue_report::*;
pub(crate) use self::release_issue_rules::*;
pub(crate) use self::render::*;
pub(crate) use self::render_evidence::*;
pub(crate) use self::report_validation::*;
pub(crate) use self::report_validators::*;
pub(crate) use self::reviewer_deck::*;
pub(crate) use self::rows::*;
pub(crate) use self::sorry_bypass_lint::*;
pub(crate) use self::tactic_count_artifact::*;
pub(crate) use self::tactic_count_consistency::*;
pub(crate) use self::tactic_count_fingerprints::*;
pub(crate) use self::tactic_parity_types::*;
pub(crate) use self::tactic_rows::*;
pub(crate) use self::tactic_summaries::*;
pub(crate) use self::trust_boundary::*;
pub(crate) use self::trust_core_report::*;
pub(crate) use self::wrapper_free_checks::*;
pub(crate) use self::wrapper_free_gate::*;
