// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean <verb>` — unified CLI surface for the `.olean` toolchain.
//!
//! This module exposes the clap argument structs, the descriptor array used by
//! `clean features` / `clean help`, and the dispatch entry point [`run`]. It
//! absorbs the standalone `.olean` binaries into the top-level `clean` CLI per
//! Epic #3436 (see `designs/2026-04-18-unified-cli-feature-index.md` and
//! `designs/2026-04-18-cli-orphan-inventory.md`).
//!
//! | Old binary                              | New CLI path                        |
//! |-----------------------------------------|-------------------------------------|
//! | `generate_namespace_overlay --...`      | `clean olean generate-overlay --...` |
//! | `verify_olean_batch <dir> [OPTIONS]`    | `clean olean verify-batch <dir>`    |
//!
//! The module is gated behind the `cli` Cargo feature so non-CLI consumers of
//! `clean-olean` keep a minimal dependency graph (no clap, no
//! `clean-features`).
//!
//! The verb layout uses a `Subcommand` enum so that sibling PRs absorbing
//! other `.olean` binaries can append new variants to [`OleanCommands`]
//! without rewriting the top-level clap tree.
//!
//! Part of #3441 and #3442. Epic: #3436.

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};
use clean_features::FeatureDescriptor;
use clean_kernel::env::ProofValueElision;

/// CLI surface for [`ProofValueElision`]: which never-(safely)-read proof
/// VALUES to free as soon as their OWN `check_type` passes during a streaming
/// `--full-validation` re-check, to bound peak resident memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, ValueEnum)]
pub enum StreamElidePolicy {
    /// Never free any value (legacy full-resident behaviour). Verdict-identical
    /// to historical runs.
    #[default]
    None,
    /// Free only `Opaque`-kind values. STATICALLY SOUND: the kernel never
    /// δ-unfolds an `Opaque` value, so the pass/fail set is IDENTICAL to
    /// `none`. This is the safe-to-ship default-eligible policy.
    OpaqueOnly,
    /// Free `Opaque`- AND `Theorem`-kind values. NOT statically sound (this
    /// kernel CAN δ-unfold theorem bodies): refusal-only — the pass set is a
    /// SUBSET of `none` (verifications may be lost, never gained). Use only
    /// behind the unchanged-kernel-verified-count gate for the target corpus.
    OpaqueAndTheorem,
}

impl From<StreamElidePolicy> for ProofValueElision {
    fn from(p: StreamElidePolicy) -> Self {
        match p {
            StreamElidePolicy::None => ProofValueElision::None,
            StreamElidePolicy::OpaqueOnly => ProofValueElision::OpaqueOnly,
            StreamElidePolicy::OpaqueAndTheorem => ProofValueElision::OpaqueAndTheorem,
        }
    }
}

mod descriptors;
mod overlay;
mod runner;

pub use descriptors::FEATURES;
pub use overlay::{generate_namespace_overlay, OverlayConfig, OverlayError, OverlayReport};

/// `clean olean <subcommand>` argument tree.
#[derive(Debug, Args)]
pub struct OleanArgs {
    /// The subcommand selected under `clean olean`.
    #[command(subcommand)]
    pub command: OleanCommands,
}

/// Every verb under `clean olean`.
///
/// Marked `#[non_exhaustive]` so sibling migrations can add new variants
/// without breaking downstream tooling.
#[derive(Debug, Subcommand)]
#[non_exhaustive]
pub enum OleanCommands {
    /// Generate namespace overlay payload modules for `clean-kernel`.
    ///
    /// Absorbs the `generate_namespace_overlay` standalone binary (#3442).
    GenerateOverlay(GenerateOverlayArgs),
    /// Type-check every `.olean` module in a directory using a shared cumulative
    /// kernel environment.
    ///
    /// Absorbs the `verify_olean_batch` standalone binary (#3441).
    VerifyBatch(VerifyBatchArgs),
    /// Measure + record the dep-closure re-verified fraction over a bounded
    /// import lane (Pillar-2 item 5).
    ///
    /// Loads the requested bootstrap module closure, runs the kernel's
    /// `add_decl`-equivalent re-check over exactly those imported constants, and
    /// writes `{total_imported, reverified, fraction, ...}` to a JSON metric
    /// file. The write RATCHETS: a measurement that regresses (fraction dropped)
    /// below the recorded baseline for the same lane is refused. Turns the
    /// import-trust residual into a measured, monotonically-rising number.
    ImportReverifyMetric(ImportReverifyMetricArgs),
}

/// Arguments for `clean olean generate-overlay`.
///
/// Mirrors the flag surface of the legacy `generate_namespace_overlay`
/// binary so downstream tooling keeps working verbatim after the migration.
#[derive(Debug, Args)]
pub struct GenerateOverlayArgs {
    /// Output directory where namespace overlay modules and payload blobs are
    /// emitted (typically `crates/clean-kernel/src/env/generated/`).
    #[arg(long)]
    pub output_dir: PathBuf,

    /// Namespace prefix to snapshot. May be repeated to emit multiple
    /// overlays in a single run (e.g. `--namespace Topology.Manifold
    /// --namespace Topology.LieGroup`).
    #[arg(long = "namespace", value_name = "PREFIX", required = true)]
    pub namespaces: Vec<String>,

    /// `.olean` module(s) to load before snapshotting. Either `--module` or
    /// `--seed-topology-env` must be supplied.
    #[arg(long = "module", value_name = "MODULE")]
    pub modules: Vec<String>,

    /// Additional `.olean` search paths. When empty, the crate's
    /// [`default_search_paths`](crate::default_search_paths) are used.
    #[arg(long = "search-path", value_name = "PATH")]
    pub search_paths: Vec<PathBuf>,

    /// Seed the source environment from kernel init paths for
    /// `Topology.Manifold` and `Topology.LieGroup`. Useful for namespaces
    /// that are not available in stdlib `.olean` files on this machine.
    #[arg(long)]
    pub seed_topology_env: bool,
}

/// Arguments for `clean olean verify-batch`.
///
/// Mirrors the flag surface of the legacy `verify_olean_batch` binary so
/// downstream scripts keep working verbatim after the prefix change.
#[derive(Debug, Args)]
pub struct VerifyBatchArgs {
    /// Directory containing the `.olean` files to verify.
    pub olean_dir: PathBuf,

    /// Additional search path for Init and imported modules. May be passed
    /// multiple times.
    #[arg(long = "init-path", value_name = "PATH")]
    pub init_paths: Vec<PathBuf>,

    /// Emit a structured JSON report to stdout instead of human-readable logs.
    #[arg(long)]
    pub json: bool,

    /// Write a comprehensive verification report to a file (in addition to
    /// stdout output).
    #[arg(long = "json-report", value_name = "FILE")]
    pub json_report: Option<PathBuf>,

    /// Process at most N modules (applied after dependency ordering).
    #[arg(long, value_name = "N")]
    pub limit: Option<usize>,

    /// Use isolated per-module verification instead of the cumulative shared
    /// environment.
    #[arg(long)]
    pub isolated: bool,

    /// Only load modules, skip type-checking.
    #[arg(long = "load-only")]
    pub load_only: bool,

    /// Number of threads to use when type-checking new constants (1 = serial).
    #[arg(long, default_value_t = 1)]
    pub parallel: usize,

    /// Path to an incremental verification cache (JSON). Modules whose content
    /// hash matches a cached entry skip type-checking.
    #[arg(long = "cache-file", value_name = "FILE")]
    pub cache_file: Option<PathBuf>,

    /// Run the full `add_decl` validation path (infer_sort + check_type)
    /// instead of the faster infer-only mode.
    #[arg(long = "full-validation")]
    pub full_validation: bool,

    /// Per-constant kernel heartbeat budget for `--full-validation`: the number
    /// of reduction/inference steps allowed before a single check aborts with
    /// `HeartbeatExceeded`. `0` = UNLIMITED. Defaults to the kernel default
    /// (2,000,000), which a handful of compute-heavy-but-VALID constants
    /// (e.g. `CbvSimproc`-class) legitimately exceed.
    ///
    /// SOUNDNESS: this is a RESOURCE budget only, not a correctness gate. On
    /// exhaustion the kernel conservatively REJECTS, so raising/disabling it
    /// can only let valid constants COMPLETE — an ill-typed constant still
    /// fails (TypeMismatch). PERF: `--max-heartbeats 0` (unlimited) on a
    /// pathological/non-terminating reduction can hang the checker; prefer a
    /// high-but-finite value and opt into unlimited explicitly.
    #[arg(long = "max-heartbeats", value_name = "N")]
    pub max_heartbeats: Option<u32>,

    /// Stream-free never-(safely)-read proof VALUES during `--full-validation`
    /// to bound peak RAM, letting a full-Init re-check COMPLETE where the eager
    /// (never-free) path OOMs. As soon as a constant of the selected kind PASSES
    /// its own `check_type`, its proof value (NOT its type) is dropped.
    ///
    /// * `none` (default): never free — verdict-identical to historical runs.
    /// * `opaque-only`: free `Opaque` values only. STATICALLY SOUND — the kernel
    ///   never δ-unfolds an opaque value, so the pass/fail set is IDENTICAL to
    ///   `none`. Safe to ship.
    /// * `opaque-and-theorem`: also free `Theorem` values. This kernel CAN
    ///   δ-unfold theorem bodies, so this is REFUSAL-ONLY: the pass set is a
    ///   SUBSET of `none` (verifications may be lost, never gained). Gate behind
    ///   an unchanged-kernel-verified-count check per corpus.
    ///
    /// SOUNDNESS: a value is freed strictly AFTER its own check_type succeeded
    /// (an ill-typed value still FAILS first), and freeing it can never turn
    /// another constant's verdict from FAIL to PASS. No unsafe.
    #[arg(long = "stream-elide-proof-values", value_enum, default_value_t = StreamElidePolicy::None)]
    pub stream_elide_proof_values: StreamElidePolicy,

    /// Directory for the `.clean-cache` Init snapshot. When set, the Init
    /// pre-load tries to restore a versioned snapshot (warm path, seconds) and
    /// — on a cold run with `--full-validation` — writes one after a successful
    /// full re-verify. Off by default (opt-in). The snapshot is a cache of a
    /// prior re-verification, NEVER a trust claim: any header mismatch falls
    /// back to a full re-verify, and a snapshot is only written after a
    /// `--full-validation` re-check of the Init closure succeeded this run.
    #[arg(long = "cache-dir", value_name = "DIR")]
    pub cache_dir: Option<PathBuf>,
}

/// Arguments for `clean olean import-reverify-metric`.
#[derive(Debug, Args)]
pub struct ImportReverifyMetricArgs {
    /// Bootstrap module(s) whose dependency closure defines the bounded lane to
    /// measure (e.g. `--module Init`, optionally `--module Std`). Their
    /// transitive imports are loaded automatically. Defaults to `Init`.
    #[arg(long = "module", value_name = "MODULE")]
    pub modules: Vec<String>,

    /// A descriptive name for the lane recorded in the metric (defaults to the
    /// module list joined by `+`, e.g. `Init` or `Init+Std`).
    #[arg(long = "lane", value_name = "NAME")]
    pub lane: Option<String>,

    /// Additional `.olean` search paths. When empty, the crate's
    /// [`default_search_paths`](crate::default_search_paths) are used.
    #[arg(long = "search-path", value_name = "PATH")]
    pub search_paths: Vec<PathBuf>,

    /// Output JSON metric file. The write RATCHETS against any existing metric
    /// for the same lane at this path. Defaults to
    /// `data/import_reverification_metric.json`.
    #[arg(long = "out", value_name = "FILE")]
    pub out: Option<PathBuf>,

    /// Per-constant kernel heartbeat budget (`0` = UNLIMITED). Pure RESOURCE
    /// limit — never a soundness gate (see `verify-batch --max-heartbeats`).
    #[arg(long = "max-heartbeats", value_name = "N")]
    pub max_heartbeats: Option<u32>,

    /// Record an ISO-8601 timestamp in the metric. Off by default so the metric
    /// is deterministic/reproducible; pass to stamp the run time.
    #[arg(long = "timestamp")]
    pub timestamp: bool,
}

// -- Errors -------------------------------------------------------------------

/// Errors surfaced by `clean olean <verb>` dispatch.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum OleanCliError {
    /// `generate-overlay` requires at least one module or
    /// `--seed-topology-env`.
    #[error("`generate-overlay` requires --module entries and/or --seed-topology-env")]
    NoOverlaySource,
    /// Namespace-overlay generation failed for a concrete reason (I/O,
    /// serialization, empty snapshot, kernel init failure).
    #[error(transparent)]
    Overlay(#[from] OverlayError),
    /// Requested `.olean` directory is not a directory.
    #[error("`{0}` is not a directory")]
    NotADirectory(PathBuf),
    /// `--parallel` must be >= 1.
    #[error("--parallel must be >= 1")]
    InvalidParallel,
    /// Loading the bootstrap closure for `import-reverify-metric` failed.
    #[error("loading import-reverify lane: {0}")]
    Import(#[from] crate::import::ImportError),
    /// Writing / ratcheting the import re-verification metric failed (including a
    /// ratchet regression — the re-verified fraction must only rise).
    #[error(transparent)]
    Metric(#[from] crate::import_reverification_metric::MetricError),
}

// -- Entry points -------------------------------------------------------------

/// Dispatch entry point for `clean olean <verb>`.
///
/// Callers (the top-level `clean-cli` binary) construct the clap args via
/// their own parser and pass the resulting [`OleanArgs`] here.
pub fn run(args: OleanArgs) -> Result<(), OleanCliError> {
    match args.command {
        OleanCommands::GenerateOverlay(a) => dispatch_generate_overlay(a),
        OleanCommands::VerifyBatch(a) => runner::run_verify_batch(a),
        OleanCommands::ImportReverifyMetric(a) => dispatch_import_reverify_metric(a),
    }
}

/// Default path for the persisted metric, relative to the workspace root.
const DEFAULT_METRIC_PATH: &str = "data/import_reverification_metric.json";

/// Dispatch `clean olean import-reverify-metric`: load a bootstrap lane's
/// closure, re-check it with the kernel, and record the re-verified fraction —
/// ratcheting (a regression is refused, so the recorded fraction only rises).
///
/// SOUNDNESS: the re-check ([`verify_bootstrap_lane`]) runs read-only over the
/// loaded env and can only ADD verification; `reverified` counts exactly the
/// constants the Clean kernel accepted. The metric is an honest lower bound on
/// genuinely-kernel-verified imports for the lane. This entry point performs
/// real I/O + loading, so it is exercised live only with a Lean toolchain
/// present; the in-memory metric logic is unit-tested without one.
fn dispatch_import_reverify_metric(args: ImportReverifyMetricArgs) -> Result<(), OleanCliError> {
    use crate::import_reverification_metric::ImportReverificationMetric;

    let modules: Vec<String> = if args.modules.is_empty() {
        crate::bootstrap_verify::INIT_BOOTSTRAP_MODULES
            .iter()
            .map(|s| (*s).to_string())
            .collect()
    } else {
        args.modules
    };
    let lane = args.lane.unwrap_or_else(|| modules.join("+"));
    let search_paths = if args.search_paths.is_empty() {
        crate::default_search_paths()
    } else {
        args.search_paths
    };
    let max_heartbeats = args
        .max_heartbeats
        .unwrap_or(clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);
    let out = args
        .out
        .unwrap_or_else(|| PathBuf::from(DEFAULT_METRIC_PATH));
    let timestamp = if args.timestamp {
        let secs = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        Some(crate::verify_report::format_epoch_as_iso8601(secs))
    } else {
        None
    };

    // Load the closure + re-check exactly the lane's imported constants.
    let report =
        crate::bootstrap_verify::verify_bootstrap_lane(&modules, &search_paths, max_heartbeats)?;

    let metric = ImportReverificationMetric::new(
        lane,
        report.loaded_constants,
        report.kernel_verified,
        timestamp,
    );
    println!(
        "import re-verification metric [{}]: {}/{} re-verified (fraction {:.4}); {} findings",
        metric.lane,
        metric.reverified,
        metric.total_imported,
        metric.fraction,
        report.failures.len(),
    );
    metric.write_ratcheting(&out)?;
    println!("wrote {} (ratchet: fraction only rises)", out.display());
    Ok(())
}

/// Public entry point for `verify-batch`, usable by both the unified
/// `clean olean verify-batch` dispatcher and any in-process caller that
/// bypasses the clap layer.
pub fn run_verify_batch(args: VerifyBatchArgs) -> Result<(), OleanCliError> {
    runner::run_verify_batch(args)
}

fn dispatch_generate_overlay(args: GenerateOverlayArgs) -> Result<(), OleanCliError> {
    if args.modules.is_empty() && !args.seed_topology_env {
        return Err(OleanCliError::NoOverlaySource);
    }

    let cfg = OverlayConfig {
        output_dir: args.output_dir,
        namespaces: args.namespaces,
        modules: args.modules,
        search_paths: args.search_paths,
        seed_topology_env: args.seed_topology_env,
    };

    let _report = generate_namespace_overlay(&cfg)?;
    Ok(())
}

/// Compile-time assertion that [`FEATURES`] is non-empty. Guards against
/// accidentally shipping an empty descriptor array, which would silently
/// disappear from `clean features` without any drift-test failure.
const _: () = {
    assert!(
        !FEATURES.is_empty(),
        "clean-olean cli must expose at least one FeatureDescriptor"
    );
    // `FeatureDescriptor` already asserts ≥1 example per path at the type
    // level; no further compile-time check needed here.
    let _: &[FeatureDescriptor] = FEATURES;
};

#[cfg(test)]
mod tests;
