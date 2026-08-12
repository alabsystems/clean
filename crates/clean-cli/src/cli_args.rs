// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI argument definitions for clean.
//!
//! Phase 2 of Epic #3436 moves most top-level `Subcommand` enums into each
//! owning crate's `cli` module:
//!
//! - `fold ...` → `clean_fold::cli::FoldCommands`
//! - `commit ...` → `clean_fold::commit::cli::CommitCommands`
//! - `cert ...` → `clean_kernel::cli::CertCommands`
//! - `server` args → `clean_server::cli::ServerArgs`
//! - `verify-c` args → `clean_c_sem::cli::VerifyCArgs`
//! - `lake ...` → `clean_lake::cli::LakeCommands` (#3479)
//! - `olean ...` → `clean_olean::cli::OleanCommands` (#3441, #3442)
//! - `bench ...` → `crate::cli::bench::BenchCommands` (stays in clean-cli)
//! - `promote ...` → `crate::cmd_promote::PromoteCommands` (stays in clean-cli)
//!
//! `cli_args::Cli` remains the single Parser root — top-level commands re-use
//! the imported `Subcommand` / `Args` types via `#[command(subcommand)]` or
//! `#[command(flatten)]`.

use clap::{Parser, Subcommand};

use clean_auto::cli::AutoCommands;
use clean_c_sem::cli::VerifyCArgs;
use clean_compiler::cli::CompileArgs;
use clean_fold::cli::FoldCommands;
use clean_fold::commit::cli::CommitCommands;
use clean_kernel::cli::{CertCommands, KernelCommands};
use clean_lake::cli::LakeArgs;
use clean_rust_sem::cli::RustVerifyArgs;
use clean_server::cli::ServerArgs;
use clean_tla::cli::TlaVerifyArgs;
#[cfg(feature = "sat-verify")]
use clean_verify::cli::VerifyProofArgs;

pub(crate) use clean_lake::cli::{CacheCommands, LakeCommands, ScriptCommands};

use crate::cli::bench::BenchCommands;
use crate::cmd_attempts::AttemptCommands;
use crate::cmd_audit::AuditCommands;
use crate::cmd_drift::DriftCommands;
use crate::cmd_factory::FactoryCommands;
use crate::cmd_false_controls::FalseControlCommands;
use crate::cmd_math::MathCommands;
use crate::cmd_math_map::MathMapCommands;
use crate::cmd_project::ProjectCommands;
use crate::cmd_promote::PromoteCommands;
use crate::cmd_release::ReleaseCommands;
use crate::cmd_replacement::ReplacementCommands;

#[derive(Parser)]
#[command(name = "clean")]
#[command(about = "Pure-Rust, Lean 4-compatible theorem prover for AI agents")]
#[command(
    long_about = "Pure-Rust, Lean 4-compatible theorem-proving infrastructure for AI agents.\n\n\
Navigating Clean as an agent:\n  \
clean features            flat index of every registered capability\n  \
clean replacement status  Lean 4 replacement scorecard + trust gates\n  \
clean audit soundness     the kernel soundness certificate (C1-C5)\n  \
clean help <path>         Markdown help for any feature path"
)]
#[command(version)]
#[command(disable_help_subcommand = true)]
pub struct Cli {
    #[command(subcommand)]
    pub(crate) command: Commands,
}

#[derive(Subcommand)]
pub(crate) enum Commands {
    /// Type check a file containing declarations
    ///
    /// Owned by `clean-kernel::cli::CheckArgs` (Epic #3436 Phase 2).
    Check(clean_kernel::cli::CheckArgs),
    /// Export every accepted top-level theorem in a `.lean` file as a
    /// `.cleancert` proof-certificate bundle (audit item 6, source → bundle
    /// → `clean kernel cert verify`).
    #[command(name = "export-cert")]
    ExportCert(crate::cli::ExportCertArgs),
    /// Verify a C source file with ACSL specifications
    VerifyC(VerifyCArgs),
    /// Verification verbs for multiple languages (Rust, C, …).
    ///
    /// Nested aggregator so sibling migrations can drop in without
    /// reshaping the top-level clap tree. Epic #3436 Phase 3, #3451.
    Verify {
        #[command(subcommand)]
        command: VerifyCommands,
    },
    /// Native automation verbs — SMT / superposition / premise selection
    /// (Experimental).
    ///
    /// Nested aggregator so sibling verbs (`auto premise`, `auto smt`, …)
    /// can drop in without reshaping the top-level clap tree. Epic #3436
    /// Phase 4, #3454.
    Auto {
        #[command(subcommand)]
        command: AutoCommands,
    },
    /// Evaluate a single expression and show its type
    ///
    /// Owned by `clean-elab::cli::EvalArgs` (Epic #3436 Phase 2).
    Eval(clean_elab::cli::EvalArgs),
    /// Start the JSON-RPC server
    Server(ServerArgs),
    /// Interactive REPL
    ///
    /// Owned by `clean_cli::cli::ReplArgs` (Epic #3436 Phase 2).
    Repl(crate::cli::ReplArgs),
    /// Lake build system commands
    Lake(LakeArgs),
    /// Nova-style folding operations for proof compression
    Fold {
        #[command(subcommand)]
        command: FoldCommands,
    },
    /// Polynomial commitment operations for proof certificates
    Commit {
        #[command(subcommand)]
        command: CommitCommands,
    },
    /// Proof certificate verification
    Cert {
        #[command(subcommand)]
        command: CertCommands,
    },
    /// Kernel verification surface — LRAT oracle conformance, soundness gate,
    /// gamma-crown verification, and `.cleancert` bundle inspection.
    ///
    /// Absorbs four orphan binaries under a single `clean kernel` verb tree
    /// (Epic #3436 Phase 3; issues #3443, #3444, #3446, #3447).
    Kernel {
        #[command(subcommand)]
        command: KernelCommands,
    },
    /// Geometry benchmark operations
    Bench {
        #[command(subcommand)]
        command: BenchCommands,
    },
    /// DerivedPending to DerivedProved promotion pipeline (#3221)
    Promote {
        #[command(subcommand)]
        command: PromoteCommands,
    },
    /// Prove a Lean goal via a remote / automated prover backend, then verify
    /// the retrieved proof locally.
    ///
    /// Integrates three working backends — Harmonic Aristotle (default,
    /// remote) and the Axiom Math `ax-prover` agent on its DeepSeek and
    /// local-`claude`-CLI (no API key) backends — behind a single verb.
    /// Verification-after-retrieval is non-negotiable: `clean prove` re-runs
    /// `lake build`, scans for residual `sorry`/`admit`, and checks
    /// `#print axioms` against a foundational allowlist before reporting
    /// success. Verbs: `run`, `status`, `list`.
    Prove {
        #[command(subcommand)]
        command: crate::cmd_prove::ProveCommands,
    },
    /// Research program dashboard and workbench commands
    Research {
        #[command(subcommand)]
        command: crate::cmd_research::ResearchCommands,
    },
    /// Lean4 ecosystem replacement scorecard and launch gates
    Replacement {
        #[command(subcommand)]
        command: ReplacementCommands,
    },
    /// Release readiness proof surfaces
    Release {
        #[command(subcommand)]
        command: ReleaseCommands,
    },
    /// AI-factory release health and launch gate surfaces
    Factory {
        #[command(subcommand)]
        command: FactoryCommands,
    },
    /// General mathematics project framework and proof-project tooling
    Math {
        #[command(subcommand)]
        command: MathCommands,
    },
    /// MathMap/Harmonic Lean patch-bundle ingest and trusted-key surfaces
    ///
    /// Drives the fail-closed `clean_mathverse::math_map` ingest pipeline:
    /// `math-map ingest` validates a signed `clean-math_map-bundle-v1`
    /// directory against the trusted-key registry and the ingest policy, and
    /// `math-map keys list|verify` inspects and validates that registry.
    /// Nothing in a bundle is trusted; a rejected or blocked ingest exits
    /// non-zero unless `--report-only` is set.
    MathMap {
        #[command(subcommand)]
        command: MathMapCommands,
    },
    /// Environment snapshot drift and statement-preservation gates
    ///
    /// Drives the `clean_mathverse::drift` snapshot/diff engine: `drift
    /// snapshot` freezes a kernel environment's declaration surface into
    /// deterministic JSON, and `drift diff` compares two such snapshots under
    /// the statement-preservation authority gate. Blocking drift exits
    /// non-zero unless `--allow-weaker` / `--allow-authority-gate-blocking`
    /// are passed explicitly.
    Drift {
        #[command(subcommand)]
        command: DriftCommands,
    },
    /// Run false-control rejection probes for release gating
    ///
    /// Drives the `clean_mathverse::false_control_suite` probe engine. Every
    /// probe feeds a verifier an input that is known to be wrong, so the only
    /// healthy outcome is rejection: a control that accepted its bad input —
    /// or never ran — exits non-zero as a soundness alarm.
    FalseControls {
        #[command(subcommand)]
        command: FalseControlCommands,
    },
    /// Clean-native project authority surfaces
    Project {
        #[command(subcommand)]
        command: ProjectCommands,
    },
    /// Proof-attempt log commands
    Attempts {
        #[command(subcommand)]
        command: AttemptCommands,
    },
    /// Release-artifact logistics — list/get/verify/extract with mandatory
    /// fail-closed blake3 manifest verification (artifact system v0,
    /// `designs/2026-06-09-master-design-v2.md` §5.6).
    Artifacts {
        #[command(subcommand)]
        command: crate::cmd_artifacts::ArtifactsCommands,
    },
    /// Trust audit commands for project and kernel boundaries
    Audit {
        #[command(subcommand)]
        command: AuditCommands,
    },
    /// AI-driven proof discovery loop (see `clean help discover`)
    Discover(clean_discovery::cli::DiscoverArgs),
    /// TLAPS benchmark and obligation tooling (absorbs `tlaps-bench`, #3448).
    Tlaps(clean_tla::bench::cli::TlapsArgs),
    /// List every registered feature as a flat index
    ///
    /// Part of Epic #3436. The descriptor registry is empty in Phase 1; domain
    /// crates register into it in Phase 2+.
    Features {
        /// Restrict to a single category (verification, import, build, proof, kernel, meta, dev)
        #[arg(long)]
        category: Option<String>,
        /// Restrict to a single stability level (v1, usable, building, experimental)
        #[arg(long)]
        stability: Option<String>,
        /// Case-insensitive substring filter over paths, summaries, and descriptions
        #[arg(long)]
        search: Option<String>,
        /// Emit JSON instead of the human-readable index
        #[arg(long)]
        json: bool,
    },
    /// Render the Markdown help for a feature path, or point at the index
    ///
    /// `clean help` with no path prints the index pointer. `clean help
    /// "kernel verify"` (or `kernel.verify`) renders that descriptor's full
    /// Markdown description via termimad.
    Help {
        /// Feature path, space- or dot-joined (e.g. "kernel verify")
        path: Option<String>,
    },
    /// Mathverse Library — cross-system math corpus search and inspection
    ///
    /// Absorbs the deprecated `mathverse_search` standalone binary (see #3440,
    /// Epic #3436). Verbs: `search`, `info`, `stats`, `systems`.
    Mathverse(clean_mathverse::cli::MathverseArgs),
    /// CAKE project lifecycle — `cake build|graduate|verify`.
    ///
    /// The Layer-1 project front-end over the graduation engine + the full cake
    /// gate, driven by a single self-contained cake-project manifest (a
    /// math-project JSON with a `cake` block) instead of the
    /// `--lake-project/--olean-module/--candidates/--baseline/--out` flag soup.
    Cake {
        #[command(subcommand)]
        command: crate::cmd_cake::CakeCommands,
    },
    /// Solver-results cache tooling — `solver index-build|stats|weak|vbs-gap|export-dataset`.
    ///
    /// Phase-1 read/analysis surface over the `solver-attempt-record-v1`
    /// telemetry captured by `clean-auto` (the producer side, env-gated by
    /// `$CLEAN_SOLVER_TELEMETRY_DIR` / `$CLEAN_SOLVER_CACHE_DIR`). Builds the
    /// fail-closed, corpus-pinned `VCIDX01` index and reports per-solver/theory/
    /// strategy success + PAR-2, weak areas, the VBS−SBS gap, and NN datasets.
    /// See `designs/2026-06-24-solver-results-cache-service.md`.
    Solver {
        #[command(subcommand)]
        command: crate::cmd_solver::SolverCommands,
    },
    /// Vendored crate sources for offline / reproducible builds.
    ///
    /// Artifact-based: the external deps are published as a `vendor.tar.zst`
    /// release asset (NOT committed to git) and fetched on demand. Verbs:
    /// `fetch`, `package`, `status`, `clean`. Replaces `scripts/fetch_vendor.sh`.
    Vendor {
        #[command(subcommand)]
        command: crate::cmd_vendor::VendorCommands,
    },
    /// `.olean` toolchain verbs (overlay generation, batch verification, …)
    ///
    /// Aggregates absorbed `.olean` standalone binaries under a single verb
    /// per Epic #3436. Sub-verbs live in `clean_olean::cli::OleanCommands`
    /// so sibling migrations (#3441 verify-batch, #3442 generate-overlay)
    /// can add variants without re-shaping the top-level clap tree.
    Olean(clean_olean::cli::OleanArgs),
    /// clean Language Server Protocol (LSP) entry point
    ///
    /// Absorbs the standalone `clean-lsp` binary (#3450, Epic #3436). The
    /// standalone binary is retained as a passthrough shim because editor
    /// configurations hard-code its path; it re-exec's `clean lsp` with the
    /// user's argv.
    Lsp(clean_lsp::cli::LspArgs),
    /// Compile a Lean declaration through the clean-compiler pipeline
    ///
    /// MVP surface for Epic #3436 Phase 4 (#3453). Accepts `<FILE>` and
    /// `--decl <NAME>` plus `--emit <FORMAT>` and `--opt-level <N>`.
    /// `Stability::Experimental` — the end-to-end file-to-emit pipeline is
    /// an explicit non-goal for this MVP; the handler currently short-
    /// circuits with a `NotYetImplemented` error.
    Compile(CompileArgs),
    /// Build and run a nullary `Nat`-returning declaration natively.
    ///
    /// Phase 5 link step of Epic #3436: takes `<FILE>` + `--decl <NAME>`
    /// through the same emit-C closure as `clean compile --emit c`, synthesizes
    /// a `main()` plus the small-`Nat` prelude shims the closure calls,
    /// `cc`-compiles + links against the embedded Clean C runtime, runs the
    /// resulting native binary, and prints its `Nat` output. The MVP entry
    /// contract is a nullary `Nat`-returning def (e.g.
    /// `def answer : Nat := Nat.succ (Nat.succ 0)`). `Stability::Experimental`.
    Run(crate::cli::RunArgs),
    /// Extract a first-order computational declaration to differential-checked
    /// C (`Stability::Experimental`; see the `extract` feature descriptor).
    Extract(crate::cli::ExtractArgs),
    /// Rank every `sorry` site in the kernel / verify crates by estimated
    /// first-order proof cost (Experimental).
    ///
    /// Rust wrapper around `scripts/sorry_to_axiom_tracer.py`
    /// (#3423). Owns the flag surface in `clean_cli::cli::SorryTraceArgs` so
    /// agents and scripts can replace direct `python3` invocations without
    /// relearning flags.
    #[command(name = "sorry-trace")]
    SorryTrace(crate::cli::SorryTraceArgs),
    /// Run the sorry-count census and ratchet against the baseline.
    ///
    /// Rust wrapper around `scripts/sorry_census.sh` (#1144). Owns the
    /// flag surface in `clean_cli::cli::SorryCensusArgs`. Part of the
    /// bucket-B script consolidation (`docs/SCRIPTS_MIGRATION.md`).
    #[command(name = "sorry-census")]
    SorryCensus(crate::cli::SorryCensusArgs),
}

/// Verbs under `clean verify <language>`.
///
/// Marked `#[non_exhaustive]` so later migrations (e.g. moving `verify-c`
/// into `verify c`) can add variants without breaking downstream tooling.
/// Epic #3436 Phase 3 (#3451) added `Rust`; Phase 4 (#3452) added `Tla`;
/// Phase 3.5 (#3511) added `Proof` behind the `sat-verify` feature gate.
#[derive(Subcommand)]
#[non_exhaustive]
pub(crate) enum VerifyCommands {
    /// Verify Rust programs via `clean-rust-sem` (Experimental).
    ///
    /// MVP exposes `--example <NAME>` against the bundled example catalog and
    /// `--list` to enumerate it. Arbitrary-file verification is deferred to a
    /// follow-up issue — see descriptor documentation.
    Rust(RustVerifyArgs),
    /// Verify a TLA+ proof obligation via `clean-tla` (Experimental).
    ///
    /// Accepts a JSON-encoded `TlaObligation` file path, `--sample <NAME>` to
    /// verify a bundled fixture, or `--list` to enumerate fixtures. See
    /// `clean help "verify tla"` for the obligation schema. Epic #3436
    /// Phase 4 (#3452).
    Tla(TlaVerifyArgs),
    /// Verify a SAT/SMT proof (LRAT/DRAT/Alethe/SMT-LIB2/VeriPB).
    ///
    /// Absorbs the `proof_check` standalone binary (Epic #3436, #3511).
    /// Feature-gated behind `sat-verify` so the heavy SAT/SMT dependency
    /// graph (parsers, Ay integration, certificate emission) does not link
    /// into the default `clean` binary. Stability: V1 — the four output
    /// modes and their exit codes are consumed by SAT-COMP / SMT-COMP
    /// judging and must not regress.
    #[cfg(feature = "sat-verify")]
    Proof(VerifyProofArgs),
}
