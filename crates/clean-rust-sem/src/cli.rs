// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean verify rust` (Rust ownership / borrow / aliasing
//! verification).
//!
//! Epic #3436 Phase 3, issue #3451. The verb is nested under a top-level
//! `verify` aggregator so that sibling languages (`c`, future additions) can
//! be added as further subcommands. The descriptor is registered as
//! `Stability::Experimental` because `clean-rust-sem` intentionally does not
//! yet commit to a stable library API.
//!
//! Design: `designs/2026-04-18-cli-orphan-inventory.md` §4.1 and
//! `designs/2026-04-18-unified-cli-feature-index.md`.
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-rust-sem` keep a minimal dependency graph (no clap, no
//! `clean-features`).
//!
//! File layout:
//! - [`cli.rs`](self) — `RustVerifyArgs`, `RustSemCliError`, `run`, and
//!   the `FEATURES` descriptor registry. Kept under 500 lines to satisfy
//!   the file-size cap.
//! - [`cli/pipeline.rs`](pipeline) — `ExampleReport`, per-stage outcome
//!   enums, and the `run_example` pipeline driver.

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

pub mod pipeline;

pub use pipeline::{
    example_error_to_cli, run_example, AliasingOutcome, BorrowOutcome, ExampleReport,
    ProofBundleOutcome,
};

// -- Arguments ----------------------------------------------------------------

/// Arguments for `clean verify rust`.
///
/// `--example <name>` runs the named worked example through the ownership /
/// aliasing / proof-bundle pipeline end-to-end. `--list` prints the catalog of
/// available examples and exits. Exactly one of the two must be supplied.
#[derive(Debug, Clone, Args)]
pub struct RustVerifyArgs {
    /// Name of a bundled example program to verify (see `--list`).
    #[arg(long, value_name = "NAME", conflicts_with = "list")]
    pub example: Option<String>,
    /// List every bundled example and exit.
    #[arg(long)]
    pub list: bool,
    /// Show per-stage details for the verified example.
    #[arg(short, long)]
    pub verbose: bool,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean verify rust` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum RustSemCliError {
    /// Caller passed neither `--example <name>` nor `--list`.
    #[error("`clean verify rust` requires either --example <NAME> or --list")]
    NoAction,
    /// The requested example name is not in the bundled catalog.
    #[error("unknown example `{name}`; run `clean verify rust --list` to see known names")]
    UnknownExample {
        /// Name that was requested.
        name: String,
    },
    /// Parsing or validation of the bundled source failed.
    #[error("parse failure for example `{name}`: {source}")]
    ParseFailed {
        /// Example name whose source failed to parse.
        name: String,
        /// Underlying error from `SourceProgram::parse`.
        #[source]
        source: crate::source::SourceError,
    },
    /// VIR lowering / NLL borrow checking failed for an example that was
    /// expected to pass.
    #[error("borrow check failure for example `{name}`: {detail}")]
    BorrowCheckFailed {
        /// Example name whose borrow check pipeline failed.
        name: String,
        /// Human-readable failure detail (error message of `ExampleError`).
        detail: String,
    },
    /// A negative example that was expected to be rejected was accepted by the
    /// borrow checker (expectation regression).
    #[error(
        "expectation regression for example `{name}`: expected borrow error in \
         function `{function}`, but pipeline reported none"
    )]
    ExpectedErrorNotReported {
        /// Example name.
        name: String,
        /// Function that was expected to produce the borrow error.
        function: String,
    },
    /// Proof bundle construction failed for an example that was expected to
    /// build cleanly.
    #[error("proof bundle failure for example `{name}`: {detail}")]
    ProofBundleFailed {
        /// Example name.
        name: String,
        /// Human-readable failure detail.
        detail: String,
    },
}

// -- Public entry points ------------------------------------------------------

/// Dispatch entry point for `clean verify rust`. Called from the top-level
/// `clean-cli` binary via `cmd_rust_sem::handle`.
pub fn run(args: RustVerifyArgs) -> Result<(), RustSemCliError> {
    if args.list {
        pipeline::print_catalog();
        return Ok(());
    }
    let Some(name) = args.example.as_deref() else {
        return Err(RustSemCliError::NoAction);
    };
    let report = run_example(name)?;
    report.print(args.verbose);
    Ok(())
}

// -- Feature descriptor registry ---------------------------------------------

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — clean-rust-sem",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3451: Reference = Reference {
    kind: RefKind::Issue,
    label: "Add clean verify rust --example (Experimental)",
    target: "#3451",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-rust-sem",
    target: "clean-rust-sem",
};

/// Feature descriptors surfaced by the Rust-semantics crate.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`. The path is nested
/// (`["verify", "rust"]`) so that sibling migrations (`verify c`, future
/// languages) can drop in without rewriting the top-level clap tree.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["verify", "rust"],
    domain_root: Some("verify"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Verify a bundled Rust ownership example end-to-end (Experimental)",
    description: "\
Run a bundled Rust source program through the clean-rust-sem pipeline: \
parse with syn, lower each function body into VIR, run NLL borrow-check, \
execute the stacked-borrows aliasing interpreter, and build the ownership \
proof bundle. Pass `--list` to enumerate the available examples. Pass \
`--example <NAME>` to verify one. Marked `Stability::Experimental` because \
the underlying library APIs (`SourceProgram`, `ProofBundleBuilder`, VIR \
lowering) intentionally do not yet commit to a stable surface — arbitrary-\
file verification is deferred to a follow-up issue once the translate / \
VIR pipeline stabilizes. Part of Epic #3436 (#3451).",
    category: Category::Verification,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean verify rust --list",
            what: "list every bundled Rust example the verifier understands",
        },
        Example {
            cmd: "clean verify rust --example inventory_restock",
            what: "run the positive inventory-restock example through the full pipeline",
        },
        Example {
            cmd: "clean verify rust --example overlapping_mut_borrows --verbose",
            what: "verify a negative example and show per-stage summary",
        },
    ],
    see_also: &["verify-c", "check"],
    references: &[
        DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3451,
        CRATE_REF,
    ],
}];

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-rust-sem cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
