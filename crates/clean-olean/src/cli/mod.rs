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
mod ir_census;
mod overlay;
mod replay;
mod runner;

pub use descriptors::FEATURES;
pub use ir_census::IrCensusArgs;
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
    /// Measure + record the fraction of a bounded import lane that passes the
    /// LOCAL assumed-environment check (Pillar-2 item 5).
    ///
    /// Loads the requested module closure and measures local type/value checks
    /// against that already populated, assumed environment. This is not fresh
    /// import admission or a proof-grade increase. Writes raw counts, errors,
    /// and a fraction only for valid nonempty accounting. An invalid metric
    /// or regression below the saved same-lane fraction is refused.
    ImportReverifyMetric(ImportReverifyMetricArgs),
    /// Report the `@[simp]` set a module closure actually DECODES.
    ///
    /// There was no way to ask this question: an imported `@[simp]` entry that
    /// never reaches `Environment::get_simp_lemmas()` surfaces only as
    /// "simp made no progress" in a Mathlib row, days later and one layer
    /// away from the decoder that dropped it. `--require <NAME>` turns that
    /// into a fail-closed assertion at the decoder.
    ///
    /// It reads `is_simp_lemma`/`get_simp_lemmas` and NOTHING else: a
    /// `simp only [name]` proof would pass with an empty registry, because
    /// simp's by-name path looks the constant up with `get_const` and never
    /// consults the decoded set.
    SimpSet(SimpSetArgs),
    /// Decode every module's compiled IR (`Lean.IR.declMapExt` in the
    /// `.olean` parts and the `.ir` file, plus the `extern` / `implemented_by`
    /// / `init` / `builtin_init` attribute entries) and print a per-module
    /// census in the pinned-Lean oracle's format.
    ///
    /// Each row is backed by a full decode: an undecodable declaration fails
    /// the command, it is never skipped. `--print-decl NAME` renders matching
    /// declarations with a port of Lean's `IR.Decl` formatter
    /// (`Lean.IR.formatDecl`) for a structural diff.
    IrCensus(IrCensusArgs),
    /// Replay `.olean` modules through Clean's kernel with `leanchecker`'s
    /// semantics.
    ///
    /// The environment is built from `.olean` files only, in Lean's kernel
    /// theory: no Clean prelude, and before the load no declaration but the
    /// kernel's quotient (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, as
    /// Lean's `quotDecl` adds them, and `Quot.sound`, which Lean declares in
    /// `Init.Core`). By default each module's imports are the trusted
    /// starting environment and its own declarations are replayed in Lean's
    /// order, each checked before it is admitted, every inductive block
    /// rebuilt by the kernel and its stored constructors and recursors
    /// compared with the rebuilt ones (`leanchecker <Module>`); `--fresh`
    /// replays the whole closure (`leanchecker --fresh <Module>`). Exits 1
    /// when any module is refused on a finding, naming the first refused
    /// declaration and the reason, or the load error when a module's `.olean`
    /// closure could not be loaded, and 2 when every refusal is only the
    /// `--max-heartbeats` budget running out.
    ///
    /// `--from-export <FILE>` reads a lean4export NDJSON export (format 3.1)
    /// instead and replays every declaration it declares from an empty
    /// environment: exit 0 accepts, 1 rejects (a malformed export, an
    /// inductive record that is not one block or stores `isRec`/`isReflexive`
    /// flags its constructors contradict, or a refused declaration), 2
    /// declines (an unsupported format or Lean version, a resource budget, a
    /// limit of Clean's representation, a level the kernel's constructors build
    /// otherwise than Lean reads it, an inductive block over a rewritten level,
    /// two names stored alike, a declared name Lean's kernel computes by name
    /// that Clean does not compute as Lean does (an unadmitted fold head,
    /// `Lean.reduceBool`, `Lean.reduceNat`), a replay that panicked, or a
    /// `partial` definition left unchecked), the contract of Lake's external
    /// kernels and the Kernel Arena.
    // A struct variant, so its arguments need no bare-`pub` type of their own.
    Replay {
        /// Module(s) to replay. Without `--fresh` each one selects every module on
        /// the search path whose dotted name it is a prefix of (`Init` selects every
        /// `Init.*` module), as `leanchecker <Module>` does.
        #[arg(required_unless_present = "from_export", value_name = "MODULE")]
        modules: Vec<String>,

        /// Replay a lean4export NDJSON export (format 3.1) instead of `.olean`
        /// modules: read strictly (`clean_olean::ndjson`), registered in the
        /// `.olean` loader's structural tier, every declaration replayed in Lean's
        /// order into an environment that holds nothing the export does not
        /// declare (the quotient enters only through `add_quot`, after `Eq`).
        /// Exit 0 accepts, 1 rejects, 2 declines; a decline never counts as an
        /// accept.
        #[arg(
            long = "from-export",
            value_name = "FILE",
            conflicts_with_all = ["modules", "fresh", "exact", "search_paths", "keep_going"]
        )]
        from_export: Option<PathBuf>,

        /// Replay every declaration of the module's import closure, not only the
        /// module's own, into an environment that holds no declaration but the
        /// seeded quotient (`leanchecker --fresh`). Exactly one module.
        #[arg(long)]
        fresh: bool,

        /// Select exactly the named modules, not every module they are a prefix
        /// of. A Clean addition for per-module sweeps: `leanchecker` has no such
        /// flag (`--fresh` already selects exactly one module).
        #[arg(long)]
        exact: bool,

        /// `.olean` search roots searched before `LEAN_PATH` and the pinned
        /// toolchain's `lib/lean` (the only toolchain searched). May be repeated.
        #[arg(long = "search-path", value_name = "PATH")]
        search_paths: Vec<PathBuf>,

        /// Kernel heartbeat budget of each declaration check: a declaration's
        /// stored type(s), its header and its value are each checked under a
        /// fresh budget of N. `0` (the default) is unlimited, as Lean's replay
        /// runs (`addDeclCore 0`). Neither the rebuild of an inductive block
        /// nor the loader's check of a `.olean.private` value is under N: both
        /// run under the kernel's default heartbeat limit whatever N is, `0`
        /// included. A finite budget never turns a check into a pass. A check
        /// that spent its budget decided nothing, whatever it failed with (the
        /// kernel's `whnf` and `is_def_eq` stop silently once it is spent), and
        /// the kernel checker is replaced after it, so nothing the starved check
        /// computed answers a later one. A declaration whose every failed check
        /// had spent its budget is refused as `budget exhausted` (JSON
        /// `outcome: "budget-exhausted"`, counted in `budget_exhausted`), and so
        /// is one refused only through such declarations; neither is a finding
        /// that it is ill-typed. A declaration check that failed with budget to
        /// spare is the kernel's verdict, reported as what it failed with.
        #[arg(long = "max-heartbeats", value_name = "N", default_value_t = 0)]
        max_heartbeats: u32,

        /// Keep replaying the remaining modules after one is refused; the exit
        /// status still reports the refusal. Without it the verb stops at the
        /// first refused module, as `leanchecker` does.
        #[arg(long = "keep-going")]
        keep_going: bool,

        /// Print one JSON record per module (module, mode, constants checked,
        /// admitted, refusals — the ones found before the replay (load, import
        /// merge, accounting) first, then the replay's in replay order —, load
        /// and replay milliseconds, the process's peak RSS so far) instead of
        /// human-readable lines. With `--from-export`, one JSON report: the
        /// verdict, the export's header and one record per declaration with its
        /// structural axiom closure.
        #[arg(long)]
        json: bool,
    },
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

    /// Run the local assumed-environment check (`infer_sort` + `check_type`
    /// on each new constant, against the environment that already holds every
    /// other one) instead of the faster infer-only mode. The new constants are
    /// replayed in Lean's order under Lean's kernel theory: one that mentions
    /// itself, a cycle, or a constant refused before it is refused, and each
    /// new inductive block is rebuilt by the kernel and must match its stored
    /// constructors and recursors. This is NOT `add_decl` and NOT a
    /// dependency-closed replay: constants outside the new set are believed at
    /// their declared types.
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
    /// to bound peak RAM, letting the local assumed-environment check of every
    /// Init constant COMPLETE where the eager (never-free) path OOMs. As soon as a constant of the selected kind PASSES
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
    /// — on a cold run with `--full-validation` — writes one after every Init
    /// constant passed that run's LOCAL assumed-environment check (each
    /// declaration checked against the loaded environment, dependencies
    /// assumed; not a dependency-closed re-check). Off by default (opt-in). The
    /// snapshot caches the loaded environment of such a run, NEVER a trust
    /// claim: any header or receipt mismatch falls back to the cold load, and a
    /// snapshot is only written after that local check of the Init closure
    /// reported no failure this run.
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
    /// `ir-census --jobs` must be >= 1.
    #[error("--jobs must be >= 1")]
    InvalidJobs,
    /// Loading a module closure failed: `import-reverify-metric`'s bootstrap
    /// lane, or the modules `simp-set` loads.
    #[error("loading the .olean closure: {0}")]
    Import(#[from] crate::import::ImportError),
    /// Writing / ratcheting the import local-check metric failed (including a
    /// ratchet regression — the local-check pass fraction must only rise).
    #[error(transparent)]
    Metric(#[from] crate::import_reverification_metric::MetricError),
    /// `replay` could not resolve the modules it was asked for, or the pinned
    /// toolchain's `lib/lean` it searches them in.
    #[error("{0}")]
    ReplayTargets(String),
    /// `replay` refused at least one module: the replay refused one of its
    /// declarations, or its `.olean` closure could not be loaded.
    #[error("replay refused {refused} of {replayed} replayed module(s) ({selected} selected); first: {first}")]
    ReplayRefused {
        /// Modules refused or not loadable.
        refused: usize,
        /// Modules replayed before the run stopped.
        replayed: usize,
        /// Modules the arguments selected.
        selected: usize,
        /// The first refused module, with its first refused declaration and
        /// the reason, or its load error.
        first: String,
        /// Every refusal of every refused module was the `--max-heartbeats`
        /// budget running out: nothing was found, nothing admitted (exit 2).
        undecided: bool,
    },
    /// `replay --from-export` rejected the export: it is malformed, or a
    /// declaration was refused (exit 1).
    #[error("replay --from-export rejected {path}: {first}")]
    ExportRejected {
        /// The export.
        path: String,
        /// The reader's refusal, or the first refused declaration and why.
        first: String,
    },
    /// `replay --from-export` declined the export (exit 2).
    #[error("replay --from-export declined {path}: {reason}")]
    ExportDeclined {
        /// The export.
        path: String,
        /// Why nothing was judged.
        reason: String,
    },
    /// `replay` could not run or report.
    #[error("replay: {0}")]
    ReplayReport(String),
    /// `simp-set --require` named a constant the loaded closure did not decode
    /// as a simp lemma.
    #[error("{missing} of {required} required simp lemma(s) are NOT in the decoded set: {names}")]
    SimpLemmasMissing {
        /// How many of the `--require` names were absent.
        missing: usize,
        /// How many names were required in total.
        required: usize,
        /// The absent names, comma-separated, in the order they were given.
        names: String,
    },
    /// `ir-census` could not resolve or read a module of the census.
    #[error("ir-census: {0}")]
    IrCensus(String),
    /// `ir-census` could not decode every module of the census; the census is
    /// refused.
    #[error("ir-census: {failed} of {total} module(s) failed to decode (see stderr)")]
    IrCensusFailed {
        /// Modules whose IR did not decode.
        failed: usize,
        /// Modules in the census.
        total: usize,
    },
}

impl OleanCliError {
    /// The process exit code: 2 when the verb declined to judge (`replay`
    /// when every refusal was the heartbeat budget, `replay --from-export`'s
    /// declines), 1 for every other error — the 0/1/2 split of Lake's external
    /// kernels and the Kernel Arena.
    #[must_use]
    pub fn exit_code(&self) -> u8 {
        match self {
            OleanCliError::ExportDeclined { .. }
            | OleanCliError::ReplayRefused {
                undecided: true, ..
            } => 2,
            _ => 1,
        }
    }
}

// -- Entry points -------------------------------------------------------------

/// Arguments for `clean olean simp-set`.
///
/// Bare `pub` like its siblings because the workspace lint gate requires it:
/// the enum variant `OleanCommands::SimpSet` is reachable at `pub`, and a
/// `pub(crate)` payload trips `private_interfaces`, which
/// `clippy -- -D warnings` turns into an error. (A plain `targo check`
/// reports nothing, which is how an earlier narrowing looked safe.)
#[derive(Debug, Args)]
pub struct SimpSetArgs {
    /// Module(s) to load before reading the decoded simp set. Defaults to the
    /// Init bootstrap lane.
    #[arg(long = "module", value_name = "MODULE")]
    pub modules: Vec<String>,

    /// Additional `.olean` search paths. When empty, the crate's
    /// [`default_search_paths`](crate::default_search_paths) are used.
    #[arg(long = "search-path", value_name = "PATH")]
    pub search_paths: Vec<PathBuf>,

    /// Refuse unless EVERY named constant is in the decoded simp set. May be
    /// repeated. This is the fail-closed form; without it the verb only
    /// reports.
    #[arg(long = "require", value_name = "NAME")]
    pub require: Vec<String>,

    /// Print every decoded entry, one `<priority> <name>` per line.
    #[arg(long)]
    pub list: bool,

    /// Emit a JSON object instead of human-readable lines.
    #[arg(long)]
    pub json: bool,
}

/// Dispatch entry point for `clean olean <verb>`.
///
/// Callers (the top-level `clean-cli` binary) construct the clap args via
/// their own parser and pass the resulting [`OleanArgs`] here.
pub fn run(args: OleanArgs) -> Result<(), OleanCliError> {
    match args.command {
        OleanCommands::GenerateOverlay(a) => dispatch_generate_overlay(a),
        OleanCommands::VerifyBatch(a) => runner::run_verify_batch(a),
        OleanCommands::ImportReverifyMetric(a) => dispatch_import_reverify_metric(a),
        OleanCommands::SimpSet(a) => dispatch_simp_set(a),
        OleanCommands::IrCensus(a) => ir_census::dispatch_ir_census(a),
        OleanCommands::Replay {
            from_export: Some(path),
            max_heartbeats,
            json,
            ..
        } => replay::run_from_export(&path, max_heartbeats, json),
        OleanCommands::Replay {
            modules,
            fresh,
            exact,
            search_paths,
            max_heartbeats,
            keep_going,
            json,
            from_export: None,
        } => replay::run_replay(replay::ReplayOptions {
            modules,
            fresh,
            exact,
            search_paths,
            max_heartbeats,
            keep_going,
            json,
        }),
    }
}

/// Default path for the persisted metric, relative to the workspace root.
const DEFAULT_METRIC_PATH: &str = "data/import_reverification_metric.json";

/// Dispatch `clean olean import-reverify-metric`: load a bootstrap lane's
/// closure, run the local assumed-environment check over it, and record the
/// pass fraction — ratcheting (a regression is refused, so the recorded
/// fraction only rises).
///
/// This reports local checks against the loaded, assumed environment, not
/// dependency-closed fresh admission or an import-trust reduction. Raw counts
/// and failures are retained; invalid accounting cannot become a ratchet
/// baseline. Real loading needs a Lean toolchain; metric logic is unit-tested.
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
    )
    .with_check_results(
        report.failed_constants,
        report
            .failures
            .iter()
            .enumerate()
            .map(|(index, failure)| {
                // The report can contain multiple findings for one display name.
                // Keep every message, without treating display text as identity.
                (
                    format!("finding[{index}] {}", failure.name),
                    failure.error.clone(),
                )
            })
            .collect(),
        report.local_check_accounting_errors.clone(),
    );
    let fraction = match metric.fraction {
        Some(value) => format!("{value:.4}"),
        None => format!("unavailable ({:?})", metric.state),
    };
    println!(
        "local import-check metric [{}]: {}/{} passed (fraction {}); {} failed; {} findings; dependencies assumed",
        metric.lane,
        metric.reverified,
        metric.total_imported,
        fraction,
        report.failed_constants,
        report.failures.len(),
    );
    metric.write_ratcheting(&out)?;
    println!("wrote {} (ratchet: fraction only rises)", out.display());
    Ok(())
}

/// Dispatch `clean olean simp-set`: load a module closure and report the
/// `@[simp]` set the importer actually decoded.
///
/// # Why this exists
///
/// `beq_iff_eq` is `@[simp]` in `Init/Core.lean`, so a bare `simp` closes
/// `(a == b) = true ↔ a = b` in Lean for any `[BEq α] [LawfulBEq α]`. Clean
/// reported "no progress made" on exactly that goal while
/// `simp only [beq_iff_eq]` closed it — and the second fact says nothing
/// about the first, because simp's by-name path
/// (`tactic/simp/lemmas.rs::collect_extra_lemmas`) resolves the constant with
/// `get_const` and never reads the decoded set. Without this verb there was
/// no way to distinguish "the decoder dropped it" from "the rewrite is
/// mis-instantiated", which is why that root cause shipped as a hypothesis.
///
/// The answer comes from [`Environment::is_simp_lemma`] /
/// [`Environment::get_simp_lemmas`] and from nothing else.
fn dispatch_simp_set(args: SimpSetArgs) -> Result<(), OleanCliError> {
    let modules: Vec<String> = if args.modules.is_empty() {
        crate::bootstrap_verify::INIT_BOOTSTRAP_MODULES
            .iter()
            .map(|s| (*s).to_string())
            .collect()
    } else {
        args.modules
    };
    let search_paths = if args.search_paths.is_empty() {
        crate::default_search_paths()
    } else {
        args.search_paths
    };

    let mut env = clean_kernel::Environment::new();
    crate::import::load_modules_with_deps(&mut env, &modules, &search_paths)?;

    let mut decoded: Vec<(i64, String)> = env
        .get_simp_lemmas()
        .map(|info| (i64::from(info.priority.value()), info.name.to_string()))
        .collect();
    decoded.sort();

    let missing: Vec<String> = args
        .require
        .iter()
        .filter(|name| !env.is_simp_lemma(&clean_kernel::Name::from_string(name.as_str())))
        .cloned()
        .collect();

    if args.json {
        let entries: Vec<serde_json::Value> = decoded
            .iter()
            .map(|(priority, name)| serde_json::json!({ "name": name, "priority": priority }))
            .collect();
        let report = serde_json::json!({
            "modules": modules,
            "decoded_simp_lemmas": decoded.len(),
            "required": args.require,
            "missing": missing,
            "entries": if args.list { serde_json::Value::Array(entries) } else { serde_json::Value::Null },
        });
        println!("{report}");
    } else {
        println!(
            "decoded simp set: {} lemma(s) after loading {}",
            decoded.len(),
            modules.join(", ")
        );
        if args.list {
            for (priority, name) in &decoded {
                println!("  {priority} {name}");
            }
        }
        for name in &args.require {
            let present = !missing.contains(name);
            println!(
                "  require {name}: {}",
                if present { "present" } else { "ABSENT" }
            );
        }
    }

    if !missing.is_empty() {
        return Err(OleanCliError::SimpLemmasMissing {
            missing: missing.len(),
            required: args.require.len(),
            names: missing.join(", "),
        });
    }
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
