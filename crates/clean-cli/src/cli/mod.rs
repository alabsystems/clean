// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-domain `cli` modules owned by the `clean-cli` crate itself.
//!
//! Most Phase 2 commands live in their owning domain crate's `cli` module
//! (e.g. `clean_fold::cli`, `clean_kernel::cli`). Several are scoped here
//! because their current implementations live in `clean-cli`:
//!
//! - [`ReplArgs`] / [`FEATURES`] — the `clean repl` entry point. The REPL
//!   event loop runs in the binary itself, so its clap args + descriptor
//!   stay here.
//! - [`bench`] — geometry benchmarks under `crates/clean-cli/src/benchmarks/`;
//!   kernel benches can migrate into a dedicated `clean_kernel::cli::bench`
//!   later.
//! - [`promote`] — `DerivedPending -> DerivedProved` pipeline whose handler
//!   already lives in `crate::cmd_promote` and links against `clean-verify`.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

pub mod bench;
pub mod promote;

use std::path::PathBuf;

use clap::{Args, ValueEnum};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments accepted by `clean sorry-trace`.
///
/// Thin Rust wrapper around
/// `scripts/sorry_to_axiom_tracer.py`. The CLI preserves the
/// Python tracer's flag surface byte-for-byte so the Rust entry point can
/// replace direct `python3` invocations in tooling and agent scripts without
/// re-learning flags. Part of #3423 follow-up.
#[derive(Debug, Clone, Default, Args)]
pub struct SorryTraceArgs {
    /// Emit JSON instead of the human-readable table.
    #[arg(long)]
    pub json: bool,
    /// Write a Markdown report to `reports/audits/` alongside stdout.
    #[arg(long)]
    pub report: bool,
    /// Override the Markdown report output path (implies `--report`).
    #[arg(long = "report-path", value_name = "PATH")]
    pub report_path: Option<PathBuf>,
    /// Increase log verbosity (`-v` for INFO, `-vv` for DEBUG).
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,
}

/// Arguments accepted by `clean sorry-census`.
///
/// Thin Rust wrapper around `scripts/sorry_census.sh`. Preserves the
/// shell script's flag surface (`--update`) so the Rust entry point can
/// replace direct `bash scripts/sorry_census.sh` invocations in tooling
/// and CI without re-learning flags.
#[derive(Debug, Clone, Default, Args)]
pub struct SorryCensusArgs {
    /// Update the baseline JSON if the current sorry count is lower.
    #[arg(long)]
    pub update: bool,
}

/// Arguments accepted by `clean repl`.
///
/// The REPL currently takes no flags; this struct is an empty argument
/// carrier that keeps the `Commands::Repl` variant uniform with the other
/// migrated subcommands and reserves a place for future options without
/// breaking the top-level clap tree.
#[derive(Debug, Clone, Default, Args)]
pub struct ReplArgs {}

/// Arguments accepted by `clean export-cert`.
///
/// Closes audit item 6 from `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md`:
/// drives parser → elaborator → kernel on a Lean source file and serializes
/// the accepted theorems as a `.cleancert` bundle. The bundle is the
/// soundness-grounded artifact `clean kernel cert verify` consumes — this
/// command closes the in-tree gap (source → bundle → verify chain).
#[derive(Debug, Clone, Args)]
pub struct ExportCertArgs {
    /// The `.lean` source file to elaborate.
    pub file: PathBuf,
    /// Destination path for the `.cleancert` bundle.
    #[arg(long, value_name = "PATH")]
    pub out: PathBuf,
    /// Optional path for a JSON export report (counts, per-decl status).
    #[arg(long = "json-report", value_name = "PATH")]
    pub json_report: Option<PathBuf>,
    /// Also include axioms in the bundle's environment snapshot.
    /// Axioms have no proof term so they cannot be replayed as theorems;
    /// they are recorded in the report only.
    #[arg(long = "include-axioms")]
    pub include_axioms: bool,
    /// Exit 0 even when no theorems were exported.
    #[arg(long = "allow-empty")]
    pub allow_empty: bool,
}

/// Arguments accepted by `clean run`.
///
/// The native build-and-run path: elaborate `<FILE>`, lower `--decl <NAME>`
/// (plus its transitive compilable dependency closure) to C via the same
/// pipeline as `clean compile --emit c`, synthesize a `main()` that calls the
/// entry and prints its `Nat` result, then `cc`-compile + link against the
/// embedded Clean C runtime and execute the resulting native binary. Phase 5
/// link step of Epic #3436 — proves the emit closure links and runs.
///
/// Two entry contracts are supported: a nullary `Nat`-returning declaration
/// (e.g. `def answer : Nat := Nat.succ (Nat.succ 0)`), where the synthesized
/// `main` unboxes the small-`Nat` result and prints it; and an `IO Unit`
/// program (e.g. `def main : IO Unit := IO.println "hello"`), where the
/// synthesized `main` drives the lowered IO action to completion (printing its
/// effects) and exits `0`. Entries that need prelude externs the embedded shim
/// tables do not cover are rejected with an explicit message rather than
/// mis-linked.
#[derive(Debug, Clone, Args)]
pub struct RunArgs {
    /// Path to the `.lean` source file containing the entry declaration.
    #[arg(value_name = "FILE")]
    pub file: PathBuf,
    /// Name of the nullary `Nat`-returning or `IO Unit` entry declaration to
    /// build and run.
    #[arg(long, value_name = "NAME")]
    pub decl: String,
    /// Optimization level hint forwarded to the C emit pipeline (`0`..`2`).
    #[arg(long, default_value_t = 0, value_name = "N")]
    pub opt_level: u8,
    /// Keep the scratch build directory (emitted C, runtime, executable) and
    /// print its path instead of deleting it on exit.
    #[arg(long)]
    pub keep_temp: bool,
}

/// Target language for `clean extract`.
///
/// Both backends run the SAME extraction gate, the SAME battery and the SAME
/// differential against kernel-side evaluation; they differ only in the emitted
/// artifact. `c` links against the embedded `clean-runtime`; `rust` emits a
/// self-contained, `unsafe`-free module with plain scalar signatures.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, ValueEnum)]
pub enum ExtractBackend {
    /// Emit C through the `clean compile --emit c` closure (default).
    #[default]
    C,
    /// Emit readable, safe Rust with plain `u8`/`u16`/`u32`/`u64`/`bool` types.
    Rust,
    /// Emit WebAssembly (`.wat` text plus the matching `.wasm` module).
    ///
    /// Fixed-width integer declarations only: Wasm `i32`/`i64` arithmetic is
    /// modular, which matches Lean's `UIntW`, whereas Lean `Nat` is unbounded
    /// and has no faithful Wasm scalar. Running the battery needs a Wasm host
    /// on PATH; without one the extraction REFUSES rather than shipping an
    /// artifact whose differential never ran.
    Wasm,
}

/// Arguments for `clean extract` — width-1 differential-checked
/// extraction (`designs/2026-08-06-clean-extract-width1.md`). The battery
/// always runs; a refusal or differential mismatch writes no artifacts.
#[derive(Debug, Clone, Args)]
pub struct ExtractArgs {
    /// Path to the `.lean` source file containing the declaration.
    #[arg(value_name = "FILE")]
    pub file: PathBuf,
    /// Name of the first-order computational declaration to extract.
    #[arg(long, value_name = "NAME")]
    pub decl: String,
    /// Output directory for the emitted source + manifest (must not exist).
    #[arg(long, value_name = "DIR")]
    pub out: PathBuf,
    /// Target language of the emitted artifact.
    #[arg(long, value_enum, default_value_t = ExtractBackend::C)]
    pub backend: ExtractBackend,
    /// Keep the scratch build directory and print its path.
    #[arg(long)]
    pub keep_temp: bool,
}

/// Feature descriptors surfaced by `clean-cli` itself
/// (`repl`, `sorry-trace`, `sorry-census`).
pub const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["repl"],
        summary: "Start an interactive clean read-eval-print loop",
        description: "\
Open an interactive session that reads expressions, elaborates them, and \
reports inferred types. Holds a persistent `Environment::with_prelude()` \
across prompts so that declarations registered via `:load <file>` remain \
visible to later queries. Meta-commands: `:type <expr>`, `:load <file>`, \
`:env [substr]`, `:help`, `:quit`. Input history persists under \
`$XDG_CACHE_HOME/clean/repl_history` (or `~/.cache/clean/repl_history`).\n\n\
Use `clean eval <expr>` for one-shot evaluation of a single expression. \
Use `clean check <file>` to type-check an entire source file.",
        category: Category::Dev,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean repl",
            what: "start the interactive read-eval-print loop",
        }],
        see_also: &["eval", "check"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "Unified CLI feature index",
                target: "designs/2026-04-18-unified-cli-feature-index.md",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Epic #3436",
                target: "3436",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Phase 2 migration #3478",
                target: "3478",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("repl"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["sorry-trace"],
        summary: "Estimate first-order proof cost for every `sorry` site (Experimental)",
        description: "\
Experimental Rust wrapper around \
`scripts/sorry_to_axiom_tracer.py`. Scans every \
`sorry`-bearing call-site in the clean kernel / verify crates, maps each \
site to its containing Rust fn, best-effort Lean declaration name, \
conjecture bucket (C001..CNNN), and a first-order proof-cost estimate \
`max(1, axioms) * max(1, pi_sites)` pulled from \
`data/axiom_audit.json`.\n\n\
Useful for answering: \"if I prove this sorry, does it actually help?\" \
Ranking primitive only — the cost is a heuristic, not a kernel-backed \
bound. Delegates execution to the Python tracer so the single source of \
truth stays in `scripts/`. Part of #3423.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean sorry-trace",
                what: "print the ranked human-readable table of sorry sites",
            },
            Example {
                cmd: "clean sorry-trace --json",
                what: "emit machine-readable JSON for tooling and agents",
            },
            Example {
                cmd: "clean sorry-trace --report",
                what: "also write a Markdown report under reports/audits/",
            },
        ],
        see_also: &["kernel verify-constructive-claims", "kernel classify"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "Unified CLI feature index",
                target: "designs/2026-04-18-unified-cli-feature-index.md",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Sorry-to-axiom tracer + cost #3423",
                target: "3423",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("sorry-trace"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["export-cert"],
        summary: "Run parser → elaborator → kernel on a .lean file and emit a .cleancert bundle",
        description: "\
Drives the full Clean verification pipeline (parser → elaborator → kernel) \
over a single `.lean` source file, then serializes the accepted theorems \
as a `.cleancert` proof-certificate bundle. The bundle is the \
soundness-grounded artifact that `clean kernel cert verify` consumes, \
closing the in-tree gap identified by audit item 6 of \
`docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md`:\n\n\
```\n\
.lean source --[clean export-cert]--> .cleancert bundle --[clean kernel \
cert verify]--> PASS/FAIL\n\
```\n\n\
For each accepted top-level `theorem` / `lemma`, the handler re-runs type \
inference with proof-certificate emission (`infer_type_with_cert`) over \
the elaborated proof term, builds a `CrossProjectCert` from the registered \
declaration, and adds both to the bundle. Definitions, inductives, \
instances, and structures are loaded into the bundle's environment \
snapshot (so they remain visible to dependent theorems) but produce no \
replayable cert; axioms are reported as such.\n\n\
The bundle is written via `CertBundle::save`, the same path the kernel \
tests exercise. On bundle build success the command emits a short text \
summary (parsed, exported, skipped, failures). Use `--json-report` for \
machine-readable export status alongside the bundle.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd:
                    "clean export-cert demos/public/kernel_check_success.lean --out demo.cleancert",
                what: "export every accepted theorem in the demo file as a replayable bundle",
            },
            Example {
                cmd: "clean export-cert proof.lean --out proof.cleancert --json-report proof.json",
                what: "also emit a JSON report next to the bundle",
            },
        ],
        see_also: &["kernel cert verify", "check"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "Clean verifier audit (2026-05-27)",
                target: "docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("export-cert"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["sorry-census"],
        summary: "Run the sorry-count census and ratchet against the baseline",
        description: "\
Runs the tactic test suite with sorry-tracking enabled, extracts the \
cumulative sorry count from the output, and compares it against \
`scripts/sorry_baseline.json`. Fails closed if the count increased \
(proof reconstruction regressed). Pass `--update` to write a new \
baseline when the count decreased.\n\n\
Delegates execution to `scripts/sorry_census.sh` so the single source \
of truth for the cargo invocation + jq comparison stays under \
`scripts/`. The Rust entry point exists so `clean sorry-census` \
participates in the unified CLI feature index. Part of the bucket-B \
script consolidation (see `docs/SCRIPTS_MIGRATION.md`).",
        category: Category::Dev,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean sorry-census",
                what: "run the census and compare against the baseline",
            },
            Example {
                cmd: "clean sorry-census --update",
                what: "update the baseline if the count decreased",
            },
        ],
        see_also: &["sorry-trace", "kernel verify-constructive-claims"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "Unified CLI feature index",
                target: "designs/2026-04-18-unified-cli-feature-index.md",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Sorry ratchet #1144",
                target: "1144",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("sorry-census"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["run"],
        summary: "Build and run a nullary `Nat`-returning declaration natively (Experimental)",
        description: "\
Phase 5 link step of the file -> elaborate -> compile -> emit -> LINK -> RUN \
pipeline (Epic #3436). Takes `<FILE>` + `--decl <NAME>` through the same \
emit-C closure as `clean compile --emit c`, synthesizes a C `main()` plus the \
small-`Nat` prelude shims the closure calls (e.g. `l_Nat_add`), `cc`-compiles \
and links the emitted C together with the embedded Clean C runtime into a \
native executable, runs it, and prints the entry's `Nat` result.\n\n\
The MVP entry contract is a nullary `Nat`-returning definition such as \
`def answer : Nat := Nat.succ (Nat.succ 0)`; the synthesized `main` unboxes \
the small-`Nat` result and prints it. Entries with parameters, non-`Nat` \
return types, `IO Unit` actions, or prelude externs outside the small-`Nat` \
shim table are rejected with an explicit message rather than mis-linked. \
Override the compiler with `$CC`; pass `--keep-temp` to retain the scratch \
build directory (emitted C + runtime + binary) for inspection.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean run answer.lean --decl answer",
                what: "build and run the nullary Nat entry `answer`, printing its value",
            },
            Example {
                cmd: "clean run answer.lean --decl answer --keep-temp",
                what: "keep the scratch build directory (emitted C, runtime, binary)",
            },
        ],
        see_also: &["compile", "check"],
        references: &[
            Reference {
                kind: RefKind::Design,
                label: "Unified CLI feature index",
                target: "designs/2026-04-18-unified-cli-feature-index.md",
            },
            Reference {
                kind: RefKind::Issue,
                label: "Epic #3436",
                target: "3436",
            },
            Reference {
                kind: RefKind::Crate,
                label: "clean-cli",
                target: "clean-cli",
            },
        ],
        domain_root: Some("run"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["extract"],
        summary:
            "Extract a first-order computational decl to differential-checked C (Experimental)",
        description: "\
Width-1 C extraction (the Rocq `Extraction` analog, fail-closed; \
`designs/2026-08-06-clean-extract-width1.md`). Elaborates `<FILE>`, gates \
`--decl <NAME>` to the v1 computational class (no Prop anywhere in the type, \
no universe params, first-order `Nat`/`Bool`/`UIntW` telescope, straight-line \
body), emits C through the same closure as `clean compile --emit c`, verifies \
shim coverage over the emitted text, `cc`-links against the embedded runtime \
with a synthesized battery driver, and DIFFERENTIALLY checks every battery \
point against kernel-side evaluation before writing the C file plus a \
blake3-digested `manifest.json` into `--out`.\n\n\
The manifest records the claim honestly: a differential check over the \
recorded battery, not a proof of translation correctness. Any refusal \
(stable `E_*` codes) or differential mismatch exits nonzero and writes \
nothing.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean extract arith.lean --decl double --out out/double",
            what: "extract `double` to C with a differential-checked manifest",
        }],
        see_also: &["run", "compile"],
        references: &[],
        domain_root: None,
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{ensure_has_example, ensure_unique_paths};

    #[test]
    fn features_are_lint_clean() {
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("cli descriptor paths are unique");
        for descriptor in FEATURES {
            ensure_has_example(descriptor).expect("every cli descriptor has ≥1 example");
        }
    }

    #[test]
    fn repl_has_expected_path() {
        assert_eq!(FEATURES.len(), 6);
        assert_eq!(FEATURES[0].path, &["repl"]);
        assert_eq!(FEATURES[1].path, &["sorry-trace"]);
        assert_eq!(FEATURES[2].path, &["export-cert"]);
        assert_eq!(FEATURES[3].path, &["sorry-census"]);
        assert_eq!(FEATURES[4].path, &["run"]);
        assert_eq!(FEATURES[5].path, &["extract"]);
    }
}
