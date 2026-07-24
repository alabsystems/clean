// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean verify proof` (SAT/SMT proof checking).
//!
//! Epic #3436 Phase 3.5, issue #3511. Absorbs the standalone `proof_check`
//! competition-grade proof checker under the unified `clean verify <verb>`
//! aggregator so future format migrations (e.g. VeriPB-specific verbs) can
//! drop in without reshaping the top-level clap tree.
//!
//! # Output modes
//!
//! Four output modes are preserved byte-for-byte from `proof_check`:
//!
//! | Mode             | Flag             | Output                                         |
//! |------------------|------------------|------------------------------------------------|
//! | default pipeline | (none)           | `s VERIFIED` / `s INVALID`                     |
//! | competition      | `--competition`  | LRAT-only; `s VERIFIED` / `s INVALID`          |
//! | SMT-COMP         | `--smtcomp`      | `valid` / `holey` / `invalid` / `unknown`      |
//! | SAT-COMP         | `--satcomp`      | `s VERIFIED` / `s NOT VERIFIED`                |
//!
//! Exit codes are a competition-judging contract:
//!   * `0` — verified
//!   * `10` — invalid (not a refutation)
//!   * `1` — error (I/O, parse, unknown format)
//!
//! # File layout
//!
//! - [`mod.rs`](self) — `VerifyProofArgs`, `VerifyProofError`, `run`, and the
//!   `FEATURES` descriptor registry. Kept under 500 lines to satisfy the
//!   file-size cap.
//! - [`pipeline`] — the four per-mode runners (`run_pipeline`,
//!   `run_competition`, `run_smtcomp`, `run_satcomp`).
//! - [`helpers`] — `ProofCheckInputs`, `OwnedProofCheckInputs`, `parse_format`,
//!   certificate emission, and LRAT trim. Split out of `pipeline` so each
//!   file stays under the 500-line cap.
//!
//! Design: `designs/2026-04-18-cli-orphan-inventory.md` §5 and
//! `designs/2026-04-18-unified-cli-feature-index.md`.

pub mod helpers;
pub mod pipeline;

use std::path::PathBuf;

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

pub use pipeline::{
    parse_format, run_competition, run_pipeline, run_satcomp, run_smtcomp, OwnedProofCheckInputs,
    ProofCheckInputs, EXIT_ERROR, EXIT_INVALID, EXIT_VERIFIED,
};

use crate::sat_verify::pipeline::ProofFormat;

// -- Arguments ----------------------------------------------------------------

/// Arguments for `clean verify proof`.
///
/// Mirrors the `proof_check` standalone binary (Epic #3436 Phase 3.5, #3511).
/// The positional `formula` / `proof` pair is always required; the four output
/// modes (`--competition`, `--smtcomp`, `--satcomp`, and the implicit default
/// pipeline) are mutually exclusive.
#[derive(Debug, Clone, Args)]
pub struct VerifyProofArgs {
    /// Path to the formula file (CNF for LRAT/DRAT/VeriPB; SMT-LIB2 for Alethe).
    pub formula: PathBuf,
    /// Path to the proof file.
    pub proof: PathBuf,
    /// Override format auto-detection (lrat|drat|alethe|smtlib2|veripb|auto).
    #[arg(long, value_name = "FMT")]
    pub format: Option<String>,
    /// Reject proofs containing trusted (unverified) steps.
    #[arg(long)]
    pub strict: bool,
    /// Emit parse / verification timings to stderr.
    #[arg(long)]
    pub timing: bool,
    /// Competition mode: LRAT-only, maximum performance.
    #[arg(long, conflicts_with_all = ["smtcomp", "satcomp"])]
    pub competition: bool,
    /// SMT-COMP proof exhibition track output.
    #[arg(long, conflicts_with_all = ["competition", "satcomp"])]
    pub smtcomp: bool,
    /// SAT-COMP unsat certificate output.
    #[arg(long, conflicts_with_all = ["competition", "smtcomp"])]
    pub satcomp: bool,
    /// Emit a JSON verification certificate to the given path.
    #[arg(long, value_name = "PATH")]
    pub certificate: Option<PathBuf>,
    /// Trim the LRAT proof and write the minimized output to PATH.
    #[arg(long, value_name = "PATH")]
    pub trim: Option<PathBuf>,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean verify proof` argument handling.
///
/// Runtime I/O / parse failures are reported directly by the runners in
/// [`pipeline`] and surface as numeric exit codes rather than typed errors,
/// per the competition contract. This enum carries only argument-level
/// failures that the dispatcher should report before any runner executes.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum VerifyProofError {
    /// The `--format` argument was not one of the recognized tokens.
    #[error("invalid --format value: {detail}")]
    InvalidFormat {
        /// Parser diagnostic.
        detail: String,
    },
}

// -- Public entry points ------------------------------------------------------

/// Dispatch entry point for `clean verify proof`. Called from the top-level
/// `clean-cli` binary via `cmd_sat_verify::handle`.
///
/// Returns the process exit code (0/10/1 per the competition contract) or a
/// [`VerifyProofError`] for argument-level failures that must be surfaced
/// before any runner executes.
pub fn run(args: VerifyProofArgs) -> Result<i32, VerifyProofError> {
    let format: Option<ProofFormat> = match args.format.as_deref() {
        Some(token) => {
            parse_format(token).map_err(|detail| VerifyProofError::InvalidFormat { detail })?
        }
        None => None,
    };

    let inputs = OwnedProofCheckInputs {
        formula_path: args.formula,
        proof_path: args.proof,
        format,
        strict: args.strict,
        timing: args.timing,
        certificate_path: args.certificate,
        trim_output: args.trim,
    };

    let view = inputs.as_inputs();
    let exit = if args.smtcomp {
        run_smtcomp(&view)
    } else if args.satcomp {
        run_satcomp(&view)
    } else if args.competition {
        run_competition(&view)
    } else {
        run_pipeline(&view)
    };
    Ok(exit)
}

// -- Feature descriptor registry ---------------------------------------------

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Epic 3436 orphan triage — proof_check",
    target: "designs/2026-04-19-epic-3436-orphan-triage.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3511: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb proof_check → clean verify proof",
    target: "#3511",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-verify",
    target: "clean-verify",
};

/// Feature descriptors surfaced by the SAT/SMT proof-checker CLI.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`. Marked `Stability::V1` because
/// the exit-code contract is consumed by SAT-COMP / SMT-COMP judging and the
/// binary is already in the hands of external users.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["verify", "proof"],
    domain_root: Some("verify"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Verify a SAT/SMT proof (LRAT/DRAT/Alethe/SMT-LIB2/VeriPB)",
    description: "\
Competition-grade checker for SAT and SMT refutation proofs. Accepts LRAT \
(text/binary), DRAT (text/binary), Alethe, SMT-LIB2 proof, and VeriPB \
formats; auto-detects by default or via `--format <fmt>`. \n\n\
Four output modes are preserved byte-for-byte from the legacy `proof_check` \
binary:\n\
  * default — `s VERIFIED` / `s INVALID` with optional timing;\n\
  * `--competition` — LRAT-only, maximum-performance path;\n\
  * `--smtcomp` — SMT-COMP exhibition track (`valid` / `holey` / `invalid` / \
    `unknown` + hole count);\n\
  * `--satcomp` — SAT-COMP unsat certificate (`s VERIFIED` / `s NOT VERIFIED`).\n\n\
Exit codes are contractual: `0` verified, `10` invalid (not a refutation), \
`1` error. `--strict` rejects proofs containing trusted steps; `--certificate \
<PATH>` emits a JSON certificate (full Alethe trust summary, hash-only for \
other formats); `--trim <PATH>` minimizes LRAT proofs (other formats are \
skipped with an explicit message).\n\n\
Absorbs the deprecated `proof_check` standalone binary (#3511). The standalone \
binary is retained as a compat shim for one release because competition judges \
hard-code the path.",
    category: Category::Verification,
    stability: Stability::V1,
    examples: &[
        Example {
            cmd: "clean verify proof formula.cnf proof.lrat",
            what: "verify an LRAT refutation of a CNF formula (auto-detected)",
        },
        Example {
            cmd: "clean verify proof formula.cnf proof.lrat --competition",
            what: "run the LRAT-only competition pipeline",
        },
        Example {
            cmd: "clean verify proof formula.smt2 proof.alethe --smtcomp",
            what: "emit SMT-COMP exhibition-track output with hole count",
        },
        Example {
            cmd: "clean verify proof formula.cnf proof.lrat --trim trimmed.lrat",
            what: "verify and write a minimized LRAT proof to trimmed.lrat",
        },
    ],
    see_also: &["verify rust", "verify-c", "cert verify"],
    references: &[
        DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3511,
        CRATE_REF,
    ],
}];

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-verify cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
