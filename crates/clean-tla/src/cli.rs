// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean verify tla` (TLA+ proof-obligation verification).
//!
//! Epic #3436 Phase 4, issue #3452. The verb is nested under the top-level
//! `verify` aggregator so that sibling languages (`rust`, `c`, …) live next
//! to each other. The descriptor is registered as
//! `Stability::Experimental` because `clean-tla` intentionally does not yet
//! commit to a stable obligation-JSON wire format — the schema tracks
//! [`crate::obligation::TlaObligation`]'s `#[derive(Serialize, Deserialize)]`
//! shape and may evolve.
//!
//! Design: `designs/2026-04-18-cli-orphan-inventory.md` §4.2 and
//! `designs/2026-04-18-unified-cli-feature-index.md` (Phase 4).
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-tla` (the in-crate `bench` runner core, the TLA+ tactic engine,
//! kernel tests)
//! keep a minimal dependency graph — no clap, no `clean-features`.
//!
//! # Obligation JSON schema
//!
//! The CLI reads files encoded in the native `TlaObligation` serde layout:
//!
//! ```json
//! {
//!   "module": "Example",
//!   "line": null,
//!   "declares": [{ "Prop": { "name": "P" } }],
//!   "hypotheses": [
//!     { "name": "h1", "formula": { "Expr": { "Var": "P" } } }
//!   ],
//!   "goal": { "Expr": { "Var": "P" } },
//!   "tactic_hint": "auto"
//! }
//! ```
//!
//! `TlaFormula` and `TlaExpr` use serde's default externally-tagged enum
//! representation (variant name as a key). See `benchmarks/tla/` for
//! committed sample obligations that round-trip through this module.

use std::fs;
use std::path::{Path, PathBuf};

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

use crate::obligation::TlaObligation;
use crate::tactic::{verify_obligation, TlaAutoResult};

// -- Arguments ----------------------------------------------------------------

/// Arguments for `clean verify tla`.
///
/// `--path <FILE>` runs the named obligation through the automation. `--list`
/// enumerates bundled sample obligations under `benchmarks/tla/` (if that
/// directory is reachable from the current working directory) and exits.
/// Exactly one of the two modes must be supplied.
#[derive(Debug, Clone, Args)]
pub struct TlaVerifyArgs {
    /// Path to a JSON-encoded `TlaObligation` file to verify.
    #[arg(
        value_name = "FILE",
        conflicts_with = "list",
        conflicts_with = "sample"
    )]
    pub path: Option<PathBuf>,
    /// List bundled sample obligations under `benchmarks/tla/` and exit.
    #[arg(long)]
    pub list: bool,
    /// Verify a bundled sample obligation by name (see `--list`).
    #[arg(long, value_name = "NAME", conflicts_with = "list")]
    pub sample: Option<String>,
    /// Emit the verification result as JSON instead of a human summary.
    #[arg(long)]
    pub json: bool,
    /// Show per-tactic trace detail for the verified obligation.
    #[arg(short, long)]
    pub verbose: bool,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean verify tla` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TlaCliError {
    /// Caller passed neither a path, `--sample <NAME>`, nor `--list`.
    #[error("`clean verify tla` requires a <FILE> argument, --sample <NAME>, or --list")]
    NoAction,
    /// The obligation file could not be read.
    #[error("cannot read obligation file `{path}`: {source}")]
    ReadFailed {
        /// Path the caller requested.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },
    /// The obligation JSON failed to parse into a `TlaObligation`.
    #[error("cannot parse obligation JSON in `{path}`: {source}")]
    ParseFailed {
        /// Path whose contents were malformed.
        path: PathBuf,
        /// Underlying serde error.
        #[source]
        source: serde_json::Error,
    },
    /// The requested sample name is not bundled.
    #[error("unknown sample `{name}`; run `clean verify tla --list` to see known names")]
    UnknownSample {
        /// Sample name the caller requested.
        name: String,
    },
    /// Automation rejected the obligation (goal not proved).
    #[error("`clean verify tla` could not prove obligation: {detail}")]
    ProofFailed {
        /// Human-readable failure message from the TLA tactic engine.
        detail: String,
    },
    /// JSON output serialization failed.
    #[error("cannot serialize result as JSON: {source}")]
    JsonOutputFailed {
        /// Underlying serde error.
        #[source]
        source: serde_json::Error,
    },
}

// -- Sample obligation catalog ------------------------------------------------

/// Bundled sample obligations shipped next to the source so `--sample <NAME>`
/// works without a filesystem fixture. Keeps the CLI self-contained for
/// smoke testing even when `benchmarks/tla/` is not on disk.
pub(crate) const BUNDLED_SAMPLES: &[(&str, &str)] = &[(
    "trivial_true",
    include_str!("../../../benchmarks/tla/trivial_true.json"),
)];

/// Print the bundled catalog to stdout.
fn print_catalog() {
    println!("Bundled TLA+ obligation samples:");
    for (name, _) in BUNDLED_SAMPLES {
        println!("  {name}");
    }
    println!();
    println!("Run `clean verify tla --sample <NAME>` to verify a bundled sample,");
    println!("or `clean verify tla <FILE>` to verify a local JSON obligation.");
}

fn load_sample(name: &str) -> Result<TlaObligation, TlaCliError> {
    let entry = BUNDLED_SAMPLES
        .iter()
        .find(|(candidate, _)| *candidate == name)
        .ok_or_else(|| TlaCliError::UnknownSample {
            name: name.to_owned(),
        })?;
    serde_json::from_str::<TlaObligation>(entry.1).map_err(|source| TlaCliError::ParseFailed {
        path: PathBuf::from(format!("<bundled:{name}>")),
        source,
    })
}

fn load_from_path(path: &Path) -> Result<TlaObligation, TlaCliError> {
    let content = fs::read_to_string(path).map_err(|source| TlaCliError::ReadFailed {
        path: path.to_path_buf(),
        source,
    })?;
    serde_json::from_str::<TlaObligation>(&content).map_err(|source| TlaCliError::ParseFailed {
        path: path.to_path_buf(),
        source,
    })
}

// -- Public entry points ------------------------------------------------------

/// Dispatch entry point for `clean verify tla`. Called from the top-level
/// `clean-cli` binary via `cmd_tla_sem::handle`.
pub fn run(args: TlaVerifyArgs) -> Result<(), TlaCliError> {
    if args.list {
        print_catalog();
        return Ok(());
    }

    let obligation = if let Some(sample) = args.sample.as_deref() {
        load_sample(sample)?
    } else if let Some(path) = args.path.as_deref() {
        load_from_path(path)?
    } else {
        return Err(TlaCliError::NoAction);
    };

    let result = verify_obligation(&obligation);

    if args.json {
        print_json_result(&obligation, &result)?;
    } else {
        print_human_result(&obligation, &result, args.verbose);
    }

    if !result.solved {
        return Err(TlaCliError::ProofFailed {
            detail: result
                .error
                .unwrap_or_else(|| "unknown automation failure".to_string()),
        });
    }

    Ok(())
}

fn print_human_result(obligation: &TlaObligation, result: &TlaAutoResult, verbose: bool) {
    let status = if result.solved { "PROVED" } else { "FAILED" };
    let module = if obligation.module.is_empty() {
        "<anonymous>"
    } else {
        obligation.module.as_str()
    };
    println!(
        "{status}: obligation in module `{module}` (hypotheses: {}, declares: {})",
        obligation.hypotheses.len(),
        obligation.declares.len()
    );

    if !result.tactics_used.is_empty() {
        println!("  tactics: {:?}", result.tactics_used);
    }

    if let Some(error) = result.error.as_deref() {
        println!("  error: {error}");
    }

    if verbose {
        println!(
            "  temporal: {}, likely_needs_induction: {}",
            obligation.is_temporal(),
            obligation.likely_needs_induction()
        );
        if let Some(hint) = obligation.tactic_hint.as_deref() {
            println!("  tactic_hint: {hint}");
        }
        if let Some(certificate) = result.certificate.as_deref() {
            println!("  certificate_bytes: {}", certificate.len());
        }
    }
}

fn print_json_result(
    obligation: &TlaObligation,
    result: &TlaAutoResult,
) -> Result<(), TlaCliError> {
    // Small DTO: we cannot derive Serialize on TlaAutoResult without
    // bumping the public API surface.
    let payload = serde_json::json!({
        "module": obligation.module,
        "line": obligation.line,
        "solved": result.solved,
        "tactics_used": result.tactics_used,
        "error": result.error,
        "temporal": obligation.is_temporal(),
        "likely_needs_induction": obligation.likely_needs_induction(),
    });
    let rendered = serde_json::to_string_pretty(&payload)
        .map_err(|source| TlaCliError::JsonOutputFailed { source })?;
    println!("{rendered}");
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
    label: "CLI orphan inventory — clean-tla",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3452: Reference = Reference {
    kind: RefKind::Issue,
    label: "Add clean verify tla (Experimental)",
    target: "#3452",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-tla",
    target: "clean-tla",
};

/// Feature descriptors surfaced by the TLA+ crate.
///
/// Registered into the top-level CLI by
/// `clean-cli/src/registry.rs::all_features()`. The path is nested
/// (`["verify", "tla"]`) so the `verify` aggregator contains sibling
/// languages side-by-side.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["verify", "tla"],
    domain_root: Some("verify"),
    alternative_forms: &[],
    feature_gate: None,
    summary: "Verify a TLA+ proof obligation via the clean-tla backend (Experimental)",
    description: "\
Run a JSON-encoded `TlaObligation` through the clean-tla automation and \
print the result. Accepts a filesystem path to a serde-encoded obligation, \
`--sample <NAME>` to verify a bundled smoke-test fixture, or `--list` to \
enumerate bundled fixtures. Pass `--json` for a machine-readable result and \
`--verbose` to include per-tactic trace. Marked `Stability::Experimental` \
because the obligation JSON schema tracks `TlaObligation`'s default serde \
layout and the tactic engine (`tla_auto`, `tla_force`, `tla_blast`, \
`tla_induction`, `tla_temporal`) is still under active development — the \
goal of this verb is exposing the automation surface, not a \
production-complete TLAPS pipeline. Part of Epic #3436 (#3452).",
    category: Category::Verification,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean verify tla --list",
            what: "list every bundled TLA+ sample obligation",
        },
        Example {
            cmd: "clean verify tla --sample trivial_true",
            what: "verify the bundled `trivial_true` sample obligation",
        },
        Example {
            cmd: "clean verify tla benchmarks/tla/trivial_true.json --json",
            what: "verify a local obligation file and emit a JSON result",
        },
    ],
    see_also: &["verify rust", "tlaps bench"],
    references: &[
        DESIGN_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3452,
        CRATE_REF,
    ],
}];

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-tla cli must expose at least one FeatureDescriptor"
    );
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
