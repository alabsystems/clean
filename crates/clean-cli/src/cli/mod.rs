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
//! - [`bench`] — the geometry benchmark runner from
//!   `clean_kernel::cert::benchmark` (inputs under the repo's
//!   `benchmarks/geometry/` data dir); kernel benches can migrate into a
//!   dedicated `clean_kernel::cli::bench` later.
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
pub(crate) struct SorryTraceArgs {
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
pub(crate) struct SorryCensusArgs {
    /// Rewrite the baseline JSON after a passing census: a LOWER count
    /// ratchets it down, an EQUAL count refreshes its date, and a missing
    /// baseline file is created. (A higher count fails the census before the
    /// rewrite, so the ratchet still cannot go up — but "only if lower" was
    /// not what the script does.)
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
pub(crate) struct ReplArgs {}

/// Arguments accepted by `clean export-cert`.
///
/// Closes audit item 6 from `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md`:
/// drives parser → elaborator → kernel on a Lean source file and serializes
/// the accepted theorems as a `.cleancert` bundle. The bundle is the
/// soundness-grounded artifact `clean kernel cert verify` consumes — this
/// command closes the in-tree gap (source → bundle → verify chain).
#[derive(Debug, Clone, Args)]
pub(crate) struct ExportCertArgs {
    /// The `.lean` source file to elaborate.
    pub file: PathBuf,
    /// Destination path for the `.cleancert` bundle.
    #[arg(long, value_name = "PATH")]
    pub out: PathBuf,
    /// Optional path for a JSON export report (counts, per-decl status).
    #[arg(long = "json-report", value_name = "PATH")]
    pub json_report: Option<PathBuf>,
    /// List axioms in the export REPORT's exported_theorems (as `(axiom)`
    /// rows). The bundle's environment snapshot is unaffected either way:
    /// axioms are registered during elaboration and the WHOLE environment is
    /// snapshotted, flag or no flag. Axioms have no proof term so they cannot
    /// be replayed as theorems.
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
/// Entry contracts: a nullary `Nat`-returning declaration (e.g. `def answer :
/// Nat := Nat.succ (Nat.succ 0)`), where the synthesized `main` unboxes the
/// small-`Nat` result and prints it; an `IO Unit` program (`def main : IO Unit
/// := IO.println "hello"`), where the synthesized `main` drives the lowered IO
/// action and exits `0`; and Lean's real entry shapes — `def main : IO UInt32`
/// EXITS WITH ITS RESULT (not always 0), and `main (args : List String)`
/// receives its argv. Entries that need prelude externs the embedded shim
/// tables do not cover are rejected with an explicit message rather than
/// mis-linked.
#[derive(Debug, Clone, Args)]
pub(crate) struct RunArgs {
    /// Path to the `.lean` source file containing the entry declaration.
    #[arg(value_name = "FILE")]
    pub file: PathBuf,
    /// Name of the nullary `Nat`-returning or `IO` entry declaration to build
    /// and run.
    #[arg(long, value_name = "NAME")]
    pub decl: String,
    /// Optimization level hint forwarded to the C emit pipeline (`0`..`2`).
    #[arg(long, default_value_t = 0, value_name = "N")]
    pub opt_level: u8,
    /// Keep the scratch build directory (emitted C, runtime, executable) and
    /// print its path instead of deleting it on exit. With `--backend trust-cg`,
    /// also keep the input IR, diagnostics and receipt when codegen or linking fails.
    #[arg(long)]
    pub keep_temp: bool,
    /// EXPERIMENTAL code generator. `c` (the default) is the C lane above.
    /// `trust-cg` lowers the same core output to trust-ir, stamps each body
    /// that passed every core self-check `clean-compiler-unvalidated`, compiles
    /// it with the external `trust-cg` (`CLEAN_TRUST_CG_BIN`, else `PATH`), and
    /// links the object with the C runtime, the prelude shims and the entry
    /// driver. Its receipt reads `lowered: clean-compiler-unvalidated` and
    /// `runtime: C via cc`; it is a measurement lane that claims nothing about
    /// the binary (designs/2026-09-30-clean-trust-unified-vision.md, LX0).
    #[cfg(feature = "trust-ir-backend")]
    #[arg(long, value_enum, default_value_t = RunBackend::C, value_name = "BACKEND")]
    pub backend: RunBackend,
    /// With `--backend trust-cg`: write the build receipt to this JSON file
    /// instead of printing its line on stderr, so the program's own stdout
    /// and stderr are exactly what it wrote.
    #[cfg(feature = "trust-ir-backend")]
    #[arg(long, value_name = "PATH")]
    pub receipt: Option<PathBuf>,
    /// Arguments handed to the built program as its `argv`, i.e. what a
    /// `def main (args : List String)` entry receives.
    ///
    /// Trailing pass-through, spelled exactly as `clean lake run` /
    /// `clean lake exe` spell theirs (`trailing_var_arg` +
    /// `allow_hyphen_values`), so `clean run f.lean --decl main -- --flag x`
    /// hands the program `["--flag", "x"]` rather than trying to parse
    /// `--flag` as one of `clean run`'s own options. `clean run`'s flags must
    /// therefore precede the first program argument.
    ///
    /// Like Lean, an entry that takes no `List String` simply never sees
    /// these: `argv` is a property of the program's own contract, and the
    /// driver only marshals a list when the entry's elaborated type asks for
    /// one.
    #[arg(
        trailing_var_arg = true,
        allow_hyphen_values = true,
        value_name = "ARG"
    )]
    pub args: Vec<String>,
}

/// Code generator for `clean run` (experimental `--backend`, `trust-ir-backend`
/// feature only).
#[cfg(feature = "trust-ir-backend")]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, ValueEnum)]
pub enum RunBackend {
    /// Emit C and compile it with the host C compiler (the default lane).
    #[default]
    C,
    /// Emit trust-ir and compile it with the external trust-cg (LX0 lane).
    #[value(name = "trust-cg")]
    TrustCg,
}

/// Target language for `clean extract`.
///
/// All three backends run the SAME extraction gate, the SAME battery and the
/// SAME differential against kernel-side evaluation. `c` links against the
/// embedded `clean-runtime`; `rust` emits a self-contained, `unsafe`-free
/// module with plain scalar signatures and compiles its battery only with an
/// admitted Trust compiler — the `trustc` beside the running `clean`, or the
/// absolute path in `CLEAN_NATIVE_DECIDE_TRUSTC` — refusing with
/// `E_RUST_TOOLCHAIN` without one (never a compiler from PATH or `$RUSTC`);
/// `wasm` emits `.wat` + `.wasm` and adds two refusals of its own — a `Nat` or
/// `Bool` in the signature (`E_WASM_SCALAR`) and no usable Wasm host on PATH
/// (`E_WASM_NO_HOST`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum ExtractBackend {
    /// Emit C through the `clean compile --emit c` closure (default).
    #[default]
    C,
    /// Emit readable, safe Rust with plain `u8`/`u16`/`u32`/`u64`/`bool` types.
    ///
    /// The battery is compiled by an admitted Trust `trustc` (the one beside
    /// this `clean`, or `CLEAN_NATIVE_DECIDE_TRUSTC`); without one the lane
    /// refuses with `E_RUST_TOOLCHAIN`.
    Rust,
    /// Emit WebAssembly (`.wat` text plus the matching `.wasm` module).
    ///
    /// Fixed-width integer declarations only: Wasm `i32`/`i64` arithmetic is
    /// modular, which matches Lean's `UIntW`, whereas Lean `Nat` is unbounded
    /// and has no faithful Wasm scalar. Running the battery needs `node` on
    /// PATH — specifically node: wasmtime/wasmer are probed but have no wired
    /// driver, so a machine with only those is refused too — and without a
    /// usable host the extraction REFUSES rather than shipping an artifact
    /// whose differential never ran.
    Wasm,
}

/// Arguments for `clean extract` — width-1 differential-checked
/// extraction (`designs/2026-08-06-clean-extract-width1.md`). The battery
/// always runs; a refusal or differential mismatch writes no artifacts.
#[derive(Debug, Clone, Args)]
pub(crate) struct ExtractArgs {
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
    /// Print the scratch build directory's path as it is used. The directory
    /// itself is a `TempDir` and is DELETED on exit regardless — no backend
    /// keeps it; copy what you need while the run prints, or read the emitted
    /// artifact paths instead. (The flag's name predates the deletion.)
    #[arg(long)]
    pub keep_temp: bool,
}

/// Feature descriptors surfaced by `clean-cli` itself (`repl`,
/// `sorry-trace`, `export-cert`, `sorry-census`, `run`, `extract` — six, as
/// the sibling test pins).
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
(proof reconstruction regressed). Pass `--update` to rewrite the \
baseline after a passing census: a LOWER count ratchets it down, an \
EQUAL count refreshes its date, and a missing baseline file is \
created.\n\n\
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
                what: "rewrite the baseline after a census that did not regress",
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
        summary: "Build and run a `Nat`-returning or `IO` declaration natively (Experimental)",
        description: "\
Phase 5 link step of the file -> elaborate -> compile -> emit -> LINK -> RUN \
pipeline (Epic #3436). Takes `<FILE>` + `--decl <NAME>` through the same \
emit-C closure as `clean compile --emit c`, synthesizes a C `main()` plus the \
prelude shims the closure calls (e.g. `l_Nat_add`), `cc`-compiles and links \
the emitted C together with the embedded Clean C runtime into a native \
executable, and runs it.\n\n\
Two entry shapes are supported. A nullary `Nat`-returning definition such as \
`def answer : Nat := Nat.succ (Nat.succ 0)`: the synthesized `main` unboxes \
the small-`Nat` result and prints it. And Lean 4's own entry contract — \
`def main : IO Unit`, `def main : IO UInt32`, and either of those taking \
`(args : List String)`: the driver marshals the process arguments into a \
`List String` when the entry takes one, drives every IO effect, and \
PROPAGATES the returned `UInt32` as its own exit status (an `IO Unit` entry \
exits 0). Trailing arguments after `--` ARE the program's `argv`: \
`clean run main.lean --decl main -- alpha beta` hands the entry \
`[\"alpha\", \"beta\"]`, flag-like tokens included, the same trailing \
pass-through `clean lake run <target> -- <args>` uses. Entries taking \
anything other than one `List String`, and prelude externs outside the shim \
tables, are rejected with an explicit message rather than mis-linked. \
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
                cmd: "clean run main.lean --decl main",
                what: "run a `def main : IO UInt32` entry; `clean run` exits with the status it returns",
            },
            Example {
                cmd: "clean run main.lean --decl main -- alpha beta",
                what: "hand `[\"alpha\", \"beta\"]` to a `def main (args : List String)` entry as its argv",
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
    FeatureDescriptor {
        path: &["native-runtime"],
        summary: "Write the linkable Clean runtime archive for this host (Experimental)",
        description: "\
Materialize the Clean C runtime an emitted object links against, as sources \
plus a host archive: `clean_runtime.h`, `clean_runtime.c` (the runtime \
proper), `runtime_extern.c` (one exported forwarder per header `static \
inline` primitive — `clean_inc`, `clean_box`, `clean_ctor_get`, … — which a \
trust-cg object binds at link time) and `clean_prelude_shims.c` (every `l_*` \
prelude shim `clean run` links, e.g. `l_Nat_add`, `l_Nat_land`), compiled \
with the host C compiler and archived as `libclean_runtime.a` in \
`--out-dir`. An object from `clean compile --emit obj` links as \
`cc <emitted>.o libclean_runtime.a -lm`.\n\n\
The archive ships INSIDE the `clean` binary and is written out on demand: \
the runtime sources are embedded in the `clean-runtime` crate and the \
prelude shims are Rust tables in `clean-native`, so there is no C file a \
package could copy (two-language roadmap WS6.13, F-119). Fail-closed: a \
missing C compiler (`$CLEAN_CC`, `$CC`, then `cc`/`gcc`/`clang`) or archiver \
(`$CLEAN_AR`, `$AR`, then `ar`) is an error, never a partial archive; \
every run first removes any `libclean_runtime.a` or member `.o` an earlier \
run left in `--out-dir` (reported as `removed stale: <path>`), so the \
directory never holds a product this run did not make; `--sources-only` \
writes the header and the three `.c` files without compiling, for a packer \
that builds with its own toolchain. There is no option to drop a member: \
the archive is the whole runtime or nothing.",
        category: Category::Build,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean native-runtime --out-dir out/runtime",
                what: "write the sources and build `out/runtime/libclean_runtime.a` with the host cc",
            },
            Example {
                cmd: "clean native-runtime --out-dir out/runtime --sources-only",
                what: "write only the header and the three C sources",
            },
        ],
        see_also: &["compile", "run"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-runtime",
            target: "clean-runtime",
        }],
        domain_root: Some("native-runtime"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// Arguments accepted by `clean native-runtime`.
///
/// See the `native-runtime` descriptor in [`FEATURES`] and
/// [`clean_native::native_runtime`] for what is written and why the archive
/// lives inside the binary.
#[derive(Debug, Clone, Args)]
pub(crate) struct NativeRuntimeArgs {
    /// Directory to write the header, the three C sources and
    /// `libclean_runtime.a` into (created if absent).
    #[arg(long, value_name = "DIR")]
    pub out_dir: PathBuf,
    /// Write the header and sources only; do not compile or archive them.
    #[arg(long)]
    pub sources_only: bool,
}

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
        assert_eq!(FEATURES.len(), 7);
        assert_eq!(FEATURES[0].path, &["repl"]);
        assert_eq!(FEATURES[1].path, &["sorry-trace"]);
        assert_eq!(FEATURES[2].path, &["export-cert"]);
        assert_eq!(FEATURES[3].path, &["sorry-census"]);
        assert_eq!(FEATURES[4].path, &["run"]);
        assert_eq!(FEATURES[5].path, &["extract"]);
        // WS6.13: the packaging requirement's own subcommand. Named here, not
        // just counted, so adding a feature without declaring its path still
        // fails this test.
        assert_eq!(FEATURES[6].path, &["native-runtime"]);
    }
}
