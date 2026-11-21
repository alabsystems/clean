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

use std::path::PathBuf;

use clap::{Args, Parser, Subcommand};

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
clean audit soundness     the kernel soundness certificate (C1-C5 + C4')\n  \
clean help <path>         Markdown help for any feature path"
)]
// `clean --version` prints `clean <crate version>+g<git sha>` — the build
// identity `build.rs` stamps (two-language roadmap WS6.13, F-118: a bare
// crate version cannot tell an installed pack, a stage1 tree and a source
// build apart). A build without git provenance says so in words instead of
// minting a fake `+g…`.
#[command(version = env!("CLEAN_BUILD_VERSION"))]
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
    /// Verification verbs grouped by language — `rust`, `tla`, and the
    /// `sat-verify`-gated `proof`. C stays at the top-level `verify-c` until it
    /// migrates here.
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
    /// Run Clean with `lean`'s command line and Lean's semantics: print a
    /// file's messages in `lean FILE`'s format and exit 1 iff one is an
    /// error (`clean lean --help` lists `lean`'s flags).
    Lean(crate::cmd_lean::LeanArgs),
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
    /// Absorbs six orphan binaries (plus the native `classify` verb) under a single
    /// `clean kernel` verb tree (Epic #3436 Phase 3; issues #3443–#3447, #3510).
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
    /// Inspect recorded evidence offline
    Evidence {
        #[command(subcommand)]
        command: EvidenceCommands,
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
        /// Restrict to a single category (verification, import, build, proof, kernel, meta,
        /// dev, operator-tools — an unknown slug's error names the live set)
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
    /// "cert verify"` (or `cert.verify`) renders that descriptor's full
    /// Markdown description via termimad.
    ///
    /// Matching is EXACT. The example here read `kernel verify` until
    /// 2026-08-31 and no descriptor has that path, so the help system's own
    /// worked example answered `no feature matches 'kernel verify'` — the
    /// first thing a reader tries, failing.
    Help {
        /// Feature path, space- or dot-joined (e.g. "cert verify")
        path: Option<String>,
    },
    /// Mathverse Library — cross-system math corpus search and inspection
    ///
    /// Absorbs the deprecated `mathverse_search` standalone binary (see #3440,
    /// Epic #3436). Verbs: every variant of `clean_mathverse::cli::MathverseCommands`
    /// — `clean mathverse --help` lists them (search, info, stats, systems, list,
    /// sample, deps, find, graph, diff, verify, stamp-verified, …).
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
    /// Accepts `<FILE>` and `--decl <NAME>` plus `--emit <FORMAT>` and
    /// `--opt-level <N>`. The file-to-emit pipeline RUNS: the declaration is
    /// parsed, elaborated, kernel-checked and lowered through its compilable
    /// dependency closure, and the selected format is written to stdout or
    /// `-o`. `--emit l5ir`/`l5cnf` dump the IR structurally; `--emit c`/`rust`
    /// emit source.
    ///
    /// `Stability::Experimental` because this verb stops at IR or source text — it
    /// does not link or run (the `trust-ir-backend` cargo feature adds `--emit obj`,
    /// a native object via trust-cg). Running is `clean run`, which takes the same emit-C
    /// closure through `cc` to a native binary and executes it.
    ///
    /// This text used to say the handler "short-circuits with a
    /// `NotYetImplemented` error". It does not, and had not for some time:
    /// that describes `clean_compiler::cli::run`, which the dispatch does not
    /// call (see its own doc comment).
    Compile(CompileArgs),
    /// Build and run a `Nat`-returning or `IO` declaration natively.
    ///
    /// Phase 5 link step of Epic #3436: takes `<FILE>` + `--decl <NAME>`
    /// through the same emit-C closure as `clean compile --emit c`, synthesizes
    /// a `main()` plus the prelude shims the closure calls, `cc`-compiles +
    /// links against the embedded Clean C runtime, and runs the resulting
    /// native binary. A nullary `Nat`-returning def (e.g.
    /// `def answer : Nat := Nat.succ (Nat.succ 0)`) has its result printed;
    /// Lean's own entry contract (`def main : IO Unit`, `def main : IO UInt32`,
    /// either optionally taking `(args : List String)`) is driven to completion
    /// and its returned `UInt32` becomes this command's exit status.
    /// `Stability::Experimental`.
    Run(crate::cli::RunArgs),
    /// Write the linkable Clean runtime archive for this host.
    ///
    /// Materializes `clean_runtime.h`, `clean_runtime.c`, `runtime_extern.c`
    /// and `clean_prelude_shims.c` into `--out-dir` and builds them into
    /// `libclean_runtime.a` with the host C compiler — what an object from
    /// `clean compile --emit obj` links against (`cc <emitted>.o
    /// libclean_runtime.a -lm`). The runtime ships inside this binary; this
    /// verb is how a package writes it out (two-language roadmap WS6.13).
    /// `Stability::Experimental`.
    #[command(name = "native-runtime")]
    NativeRuntime(crate::cli::NativeRuntimeArgs),
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

#[derive(Args)]
pub(crate) struct K3PacketSyntaxArgs {
    /// Print the frame lengths, parsed rows, and reported summary as JSON
    #[arg(long)]
    pub(crate) json: bool,
    /// Check agreement between frames, rows, and summary, and scan accepted tokens
    #[arg(long)]
    pub(crate) check_consistency: bool,
    /// Check packet consistency and bind declaration lines and kinds to the export
    #[arg(long)]
    pub(crate) check_declaration_index: bool,
    /// Check non-inductive declaration bodies, the declaration index, and packet consistency
    #[arg(long)]
    pub(crate) check_non_inductive_bodies: bool,
    /// Check all declaration bodies and unique declared names, including inductive members
    #[arg(long)]
    pub(crate) check_declaration_bodies: bool,
    /// Check declaration bodies and bind exact declaration names to the transcript
    #[arg(long)]
    pub(crate) check_declaration_names: bool,
    /// Bind accepted statement echoes and level parameter counts to the export
    #[arg(long)]
    pub(crate) check_accepted_statements: bool,
    /// Check accepted statements and compare recognition of the pinned base families
    #[arg(long)]
    pub(crate) check_base_families: bool,
    /// Check base families and bind every declaration's fragment class to the export
    #[arg(long)]
    pub(crate) check_fragment_classes: bool,
    /// Check fragment classes and bind dependency refusals to earlier inside declarations
    #[arg(long)]
    pub(crate) check_dependency_refusals: bool,
    /// Validate the packet and export, then print canonical coverage figure JSON
    #[arg(long)]
    pub(crate) coverage_figures: bool,
    /// Path to the Clean checkout (defaults to the current directory)
    #[arg(long, value_name = "PATH")]
    pub(crate) repo_root: Option<PathBuf>,
}

#[derive(Subcommand)]
pub(crate) enum EvidenceCommands {
    /// Show the evidence board: headline rows in design order, then other figures
    Status {
        /// Print the board rows, or the derived scoreboard, as JSON
        #[arg(long, conflicts_with = "markdown")]
        json: bool,
        /// Write the board as a Markdown table to this path
        #[arg(long, value_name = "OUT", conflicts_with = "scoreboard")]
        markdown: Option<PathBuf>,
        /// Derive the full W0 scoreboard from its source artifacts
        #[arg(long)]
        scoreboard: bool,
        /// Compare the saved scoreboard with the canonical source derivation
        #[arg(long, requires = "scoreboard", conflicts_with = "json")]
        check: bool,
        /// Save the canonical scoreboard to data/self_proof_scoreboard.json
        #[arg(long, requires = "scoreboard", conflicts_with_all = ["check", "json"])]
        write: bool,
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// List supported evidence figures and their check inputs
    List {
        /// Print the catalog as JSON
        #[arg(long)]
        json: bool,
    },
    /// Check recorded evidence figures against their local inputs
    Check {
        /// Evidence figure identifiers
        #[arg(value_name = "FIGURE", required_unless_present = "all")]
        figures: Vec<String>,
        /// Check every registered figure
        #[arg(long, conflicts_with = "figures")]
        all: bool,
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// Compute a canonical root digest over an exported environment and module inventory
    MeaningDigest {
        /// Uncompressed lean4export NDJSON stream
        #[arg(long, value_name = "FILE")]
        export: PathBuf,
        /// Caller-supplied label for the compiled module inventory
        #[arg(long, value_name = "MODULE")]
        module: String,
        /// Compiled module inventory, including its companion parts when present
        #[arg(long, value_name = "FILE")]
        olean: PathBuf,
        /// Unambiguous Lean name of the package declaration to measure
        #[arg(long, value_name = "NAME")]
        root: String,
    },
    /// Check the recorded K3 executable source closure and digests
    #[command(name = "check-k3-sources")]
    CheckK3Sources {
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// Check Lean rule references and discover unlisted controls
    #[command(name = "check-rule-lean-references")]
    CheckRuleLeanReferences {
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// Check pinned C++ rule source files and raw line digests
    #[command(name = "check-rule-cpp-anchors")]
    CheckRuleCppAnchors {
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
        /// Also check that inventory rows cover the pinned definitions and their contents
        #[arg(long)]
        coverage: bool,
    },
    /// Check rule inventory sources, row shape, and incomplete-family status
    #[command(name = "check-rule-inventory")]
    CheckRuleInventory {
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
        /// Require every rule family to be specified after the consistency checks pass
        #[arg(long)]
        require_complete: bool,
    },
    /// Check the canonical K3 coverage receipt against its packet and sources
    #[command(name = "check-k3-coverage")]
    CheckK3Coverage {
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// Check K3 advice framing and version-1 transcript syntax
    #[command(name = "check-k3-packet-syntax")]
    CheckK3PacketSyntax(K3PacketSyntaxArgs),
    /// Check K3 export syntax and the lean4export 3.1.0 header
    #[command(name = "check-k3-export-syntax")]
    CheckK3ExportSyntax {
        /// Check consecutive name IDs, earlier parents, and unique names
        #[arg(long)]
        check_names: bool,
        /// Check the name and level tables, including the unfolded level size limit
        #[arg(long)]
        check_levels: bool,
        /// Check name, level, and expression tables and unfolded expression sizes
        #[arg(long)]
        check_expressions: bool,
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
    /// Show the recorded provenance of an evidence figure
    Explain {
        /// Evidence figure identifier
        #[arg(value_name = "FIGURE")]
        figure: String,
        /// Path to the Clean checkout (defaults to the current directory)
        #[arg(long, value_name = "PATH")]
        repo_root: Option<PathBuf>,
    },
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
