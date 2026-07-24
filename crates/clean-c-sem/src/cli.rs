// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean verify-c` (ACSL/Frama-C–style C verification).
//!
//! Part of Epic #3436 Phase 2. The `verify-c` top-level command does not
//! currently have nested verbs so this module exposes a small [`VerifyCArgs`]
//! struct consumable by the `clean-cli` dispatcher and one [`FeatureDescriptor`]
//! in [`FEATURES`].
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments for `clean verify-c`.
#[derive(Args, Debug)]
pub struct VerifyCArgs {
    /// C file to verify
    pub file: PathBuf,
    /// Treat unknown obligations as failures
    #[arg(long)]
    pub fail_unknown: bool,
    /// Show detailed per-VC output
    #[arg(short, long)]
    pub verbose: bool,
}

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-c-sem",
    target: "clean-c-sem",
};

/// Descriptors for the `clean verify-c` command.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["verify-c"],
    summary: "Verify a C source file against its ACSL specification",
    description: "Parses the supplied C file, generates verification \
conditions for the ACSL-style specification, and discharges them via the \
kernel + auto pipeline. `--fail-unknown` treats unresolved obligations as \
hard failures; `--verbose` prints the per-VC outcome.",
    category: Category::Verification,
    stability: Stability::V1,
    examples: &[Example {
        cmd: "clean verify-c examples/safe_add.c --fail-unknown",
        what: "verify a C file and fail on any unresolved obligation",
    }],
    see_also: &["cert verify", "check"],
    references: &[DESIGN_REF, CRATE_REF],
    domain_root: Some("verify-c"),
    alternative_forms: &[],
    feature_gate: None,
}];
