// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI argument structs and feature descriptors owned by `clean-kernel`.
//!
//! Phase 2 of Epic #3436. This module provides the clap-derived argument
//! structs for kernel-driven commands (`check`, `cert ...`) and the matching
//! `FeatureDescriptor` entries consumed by the `clean features`,
//! `clean help`, and `clean explore` surfaces.
//!
//! The owning-crate pattern keeps each domain in charge of its own user
//! interface: clap struct + descriptor live here, the top-level `clean`
//! binary only aggregates them. Handler logic for `check` and `cert ...`
//! currently lives in `clean-cli::cmd_core` and `clean-cli::cmd_cert` (they
//! depend on `clean-elab` and `clean-server`, which the kernel crate cannot
//! depend on without introducing a cycle). The structs are pure data carriers:
//! the dispatcher in `clean-cli` consumes their fields and invokes the
//! existing handlers unchanged.
//!
//! Phase 3 (#3443/#3444/#3446/#3447) introduces the nested `clean kernel
//! <verb>` command tree that absorbs six orphan binaries. The enums and
//! descriptors for those verbs live in the [`kernel_verbs`] submodule and are
//! re-exported here; the submodule also publishes
//! [`kernel_verbs::KERNEL_VERB_FEATURES`] which `clean-cli::registry` extends
//! into the top-level feature index alongside [`FEATURES`].
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

mod constructive_claims;
mod kernel_verbs;

pub use constructive_claims::run_verify_constructive_claims;
pub use kernel_verbs::{KernelCertCommands, KernelCommands, KERNEL_VERB_FEATURES};

/// Prelude mode for `clean check` (added by #3516).
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum PreludeMode {
    /// Clean's hand-registered prelude — NOT kernel built-ins alone.
    ///
    /// `Environment::with_prelude()` plus the check path's own registrars.
    /// Alongside the kernel primitives it seeds twenty non-foundational
    /// VALUE-LESS axioms: the `IO` operations, `tryCatchThe`, `tryFinally`,
    /// and the `sorry` / `sorryAx` / `trustedArith` / `trustedAy` trust
    /// markers. (The `SetTheory.*` symbols and the `Fact` class stubs moved to
    /// the opt-in stub theory, `init_stub_theory`, in KR1 slice 1,
    /// `docs/DECISIONS.md` R132; the `Subgroup` / `RingHom` / `Finite` / …
    /// placeholders followed them, and the `Set` operations became
    /// definitions, in R143.) A theorem
    /// checked against this prelude is a PROOF only if its transitive closure
    /// avoids them — the live census, and the ratchet that keeps the count
    /// falling, are in `data/prelude_axiom_ratchet.json`.
    ///
    /// `Nat.lt_succ_iff`, `Nat.mul_lt_mul` and `Nat.mul_lt_mul_right` used to
    /// be named here as real Mathlib lemmas asserted rather than proved; #49
    /// retired all three (and the `instIrreflNatLt` instance) to kernel-checked
    /// declarations with empty axiom closures; `Fact.mk` and `Fact.out`, the
    /// last asserted PROPOSITIONS, left with the stub theory, so this prelude
    /// ships none.
    #[default]
    Builtin,
    /// The same hand-registered prelude as `builtin`, with Lean-4-core parity
    /// gating switched on: `List` gets no `Pure`/`Bind` instance and a
    /// `do`-block over a monad Lean core lacks is rejected. This mode loads no
    /// `.olean`; `.olean` files come in through `import` resolution, whichever
    /// mode is selected.
    Lean4Core,
}

/// Default ambient per-declaration budget for `clean check`, in kernel
/// operations (see [`CheckArgs::decl_budget`]).
///
/// **Deliberately far above anything a finishing declaration plausibly costs,
/// so that switching the mechanism on cannot move a verdict.** A budget that
/// turned a slow-but-finishing declaration into `diverged` would be
/// measurement damage, not measurement, so the margin is the point and the
/// number is knowingly loose. It is the "cannot move a verdict" setting, NOT a
/// recommendation for a sweep.
///
/// **What has been measured** (2026-08-27, `reports/decl-budget-calibration.json`,
/// minted by `scripts/decl_budget_calibrate.sh` — a corpus checked with the
/// budget armed at `u64::MAX`, running so the counter is meaningful,
/// unreachable so nothing can be cut off):
///
/// * 136 declarations over 18 files, including a real `Mathlib/Logic/Basic.lean`
///   under `--imports-prefer-olean`. Median **127** ticks, p99 **2,071,624**,
///   max **7,727,977**. This constant clears that maximum by **259×**.
/// * The maximum is a Mathlib top-level unit, and that matters: the budget's
///   unit is the TOP-LEVEL SURFACE DECLARATION, so a `namespace` / `section` /
///   `mutual` block is ONE unit sharing one budget. Logic/Basic's 255 leaf
///   declarations arrive as 5 such units.
///
/// **What has not**: a wide Mathlib-source census. The repo's own
/// `tests/fixtures` tree did not finish a sweep inside a 900 s bound (some
/// fixtures are deliberately pathological), so the corpus above is narrow by
/// construction. Widen it before treating the 259× as a general margin rather
/// than a measured one on this corpus.
///
/// A run that wants tight, uniform bounds should pass its own `--decl-budget`
/// derived from that census rather than inheriting this.
///
/// `0` would mean unlimited. It is not the default: an unbounded default is
/// exactly the state that made whole-file source-elaboration runs
/// unmeasurable.
pub const DEFAULT_DECL_BUDGET: u64 = 2_000_000_000;

/// Default per-declaration automation work budget for `clean check`, in
/// automation work units (see [`CheckArgs::automation_budget`]).
///
/// Unlike [`DEFAULT_DECL_BUDGET`] this one is MEANT to cut: its purpose is to
/// make a search that cannot succeed fail fast, the way Lean's
/// `maxHeartbeats` does. So it is chosen between two measured lines, not far
/// above one.
///
/// **Measured 2026-09-26** over the whole pinned source-elaboration slice
/// (`scripts/source_elab_gate.sh`'s five files, 764 declarations), with the
/// budget armed at `u64::MAX` — counting, never cutting — and every verdict
/// equal to the unbudgeted run's:
///
/// * the heaviest PASSING declaration spent **328,138** units
///   (`Ne.instIsEquiv_compl`, `Mathlib/Order/Basic.lean`); no other passing
///   declaration reached 250,000;
/// * the heavy FAILING ones spent **150,371,835** (`Function.Injective.dite`,
///   1,537 s in one `grind` → `decide` → superposition path) and **62,340,969**
///   (`Function.Injective.linearOrder`, 151 s in one `simp_rw`), then
///   7,979,897, 1,759,861 and below.
///
/// 10,000,000 clears the heaviest passing declaration by **30×** and stops the
/// two runaways at about a fifteenth and a sixth of what they spent.
/// Re-derive it from the per-declaration `timing.per_declaration[].
/// automation_work` of a `clean check --json --automation-budget
/// 18446744073709551615` run before moving it; a corpus wider than the slice
/// is not yet measured, which is why the margin is thirty rather than two.
pub const DEFAULT_AUTOMATION_BUDGET: u64 = 10_000_000;

/// Arguments accepted by `clean check`.
///
/// Exported so `clean-cli` can embed this struct inside its top-level
/// `Commands` enum without re-declaring the argument surface.
#[derive(Debug, Clone, Args)]
pub struct CheckArgs {
    /// File to check.
    pub file: PathBuf,
    /// Explicit source world, as a `lean-toolchain` tag (`v4.35.0`). Otherwise
    /// use the owning project's nearest lean-toolchain, then the unchanged
    /// oracle. An unknown release given here is refused; one the project's
    /// lean-toolchain names refuses every Lean import, and the file is read in
    /// the oracle's language. Measured worlds require explicit selection and
    /// an exact installed library.
    #[arg(long)]
    pub lean_world: Option<crate::lean_world::LeanWorld>,
    /// Show per-declaration detail: the tick list, notation seeding, and the
    /// reason behind each failure.
    ///
    /// SILENTLY IGNORED in two cases. With `--json` (`verbose && !json`) the
    /// JSON report is the machine surface and carries its own detail, so the
    /// human stream is suppressed rather than interleaved — pass one or the
    /// other. Under `--parse-only` it is never read at all: that mode counts
    /// parse outcomes and has no per-declaration detail to show.
    #[arg(short, long)]
    pub verbose: bool,
    /// Allow `sorry` (don't count as failure). Useful for checking
    /// formalization type signatures without complete proofs.
    #[arg(long)]
    pub allow_sorry: bool,
    /// Emit a machine-readable JSON check report.
    #[arg(long)]
    pub json: bool,
    /// Prelude to preload before checking.
    #[arg(long, value_enum, default_value_t = PreludeMode::Builtin)]
    pub prelude: PreludeMode,
    /// Prefer loading imports from prebuilt `.olean` artifacts over recursively
    /// elaborating their `.lean` source, when both exist on disk.
    ///
    /// This matches Lean's own import model — the file under check elaborates
    /// from source while its imports load from compiled `.olean`s — and lets a
    /// single file that lives *inside* a large source tree (e.g. one Mathlib
    /// module, whose sibling `import Mathlib.X` statements would otherwise
    /// resolve to `.lean` files and drag in the entire transitive source
    /// closure) be checked against its prebuilt dependency context instead.
    /// Off by default: intra-project imports keep recursing into source, which
    /// is correct for a fresh project with no compiled artifacts.
    #[arg(long)]
    pub imports_prefer_olean: bool,
    /// Accept an `import` that resolves to nothing real, substituting a
    /// hand-written stand-in and continuing.
    ///
    /// OFF by default, and the default is the load-bearing half. Without it,
    /// `import Mathlib.Utterly.Fake.Nonsense` used to be served by the
    /// `Mathlib.*` prefix wildcard in `clean-elab`'s prelude providers: the
    /// module does not exist, ~30 hand-written structures were substituted for
    /// it, and the file reported `1 passed, 0 failed` with exit 0. Every
    /// declaration in such a file elaborates against something the source did
    /// not ask for, so the verdict is not a verification claim — which makes it
    /// worse than no verdict, and makes any aggregate measured through this
    /// command (parse rates, source-elaboration counts) unfalsifiable.
    ///
    /// With this flag the old behavior is available deliberately — for the
    /// arXiv-formalization workflow, where an LLM emits plausible-but-invented
    /// `Mathlib.*` imports and the point is to elaborate the *statement*
    /// anyway. Every substitution is logged at `warn` even here.
    ///
    /// This mirrors `clean lake build --permissive-imports`, which has been
    /// fail-closed-by-default since its own audit.
    #[arg(long)]
    pub permissive_imports: bool,
    /// Maximum entries per kernel type-checker memo cache before sliding-window
    /// eviction. `0` means unbounded (no eviction). Defaults to the kernel's
    /// built-in cap (100_000).
    ///
    /// This is a pure performance knob: the kernel still performs every
    /// reduction and still demands the same definitional-equality proof, so it
    /// is TCB-neutral. Raising it can speed up large `:= rfl` certificate checks
    /// whose working set otherwise thrashes the cache, at the cost of memory.
    #[arg(long)]
    pub max_cache_entries: Option<usize>,
    /// Ambient per-declaration budget, in kernel operations (whnf / is_def_eq
    /// / infer_type ticks). `0` means unlimited.
    ///
    /// A declaration that spends this much fuel is reported `diverged` — its
    /// OWN verdict, never a pass and never a failure-to-prove — and the run
    /// carries on to the next declaration instead of hanging. Without it, ONE
    /// diverging declaration holds the whole file's measurement hostage: a
    /// single `by grind` in `Mathlib/Logic/Basic.lean` burned 40+ minutes with
    /// no output and the run was abandoned with no verdict for any of the
    /// other declarations.
    ///
    /// This is a *cooperative* budget, not a wall clock — the counter is
    /// decremented at the kernel's existing heartbeat tick sites, so the fuel
    /// is counted in ticks, never time, and no thread is ever killed. The
    /// count is not exactly reproducible, though: identical runs of a file
    /// whose proofs call `grind` have spent a few ticks more or fewer, and a
    /// search that carries its own wall-clock timeout (`grind`'s
    /// automation-engine fallback has one) can end sooner on a slower or
    /// busier machine and tick less. It is also only as tight as those tick
    /// sites are dense: a pathology whose cost is per-tick allocation SIZE
    /// rather than tick COUNT is not bounded by it.
    ///
    /// The default is deliberately far above anything measured to pass, so
    /// turning it on cannot move a verdict; see
    /// `clean_kernel::cli::DEFAULT_DECL_BUDGET`.
    #[arg(long, default_value_t = DEFAULT_DECL_BUDGET)]
    pub decl_budget: u64,
    /// Per-declaration AUTOMATION work budget, in work units. `0` means
    /// unlimited, and then nothing is counted.
    ///
    /// The shape of Lean's `maxHeartbeats`: one pot per declaration (a
    /// `section`/`namespace` member is its own declaration here, as it is its
    /// own command in Lean), charged by the superposition given-clause loop,
    /// every `simp`/`simp_rw` traversal frame and lemma attempt, and every
    /// `grind` step and closer. Once it is spent each of those gives up at its
    /// next charge for the rest of the declaration (a tactic that reaches none
    /// of them is not bounded by it), and a declaration that then fails
    /// reports `(deterministic) automation budget exhausted` with the failure
    /// it was left with. `--decl-budget` counts only the KERNEL operations in
    /// this work: the superposition loop performs none, so no other
    /// per-declaration budget bounds it, while a `simp` or `grind` search
    /// draws on both, its steps on this budget and the kernel checks it makes
    /// on `--decl-budget`.
    ///
    /// A unit is a step of that work, never time. The units a declaration
    /// spends are nevertheless not load-independent everywhere: a search
    /// that also carries its own wall-clock timeout (`grind`'s
    /// automation-engine fallback runs superposition under one) can stop
    /// sooner on a slower or busier machine and spend fewer. See
    /// `clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET` for how the default was
    /// measured.
    #[arg(long, default_value_t = DEFAULT_AUTOMATION_BUDGET)]
    pub automation_budget: u64,
    /// Parse only: run the parser over the file and count per-declaration
    /// parse outcomes (parse OK / `RawDecl`-recovered / hard error) WITHOUT
    /// elaborating or kernel-checking anything. `RawDecl` recovery
    /// placeholders always count as failures, never as parses. With `--json`,
    /// emits a machine-readable parse report.
    ///
    /// This mode reads the file path, source-world selection and `--json`:
    /// `--verbose`, `--prelude`, `--allow-sorry`, `--imports-prefer-olean`,
    /// `--permissive-imports`, `--decl-budget`, `--automation-budget` and `-D`
    /// are all inert here — no
    /// declaration is registered and no verification verdict of any kind is
    /// minted.
    #[arg(long)]
    pub parse_only: bool,
    /// Set a Lean option for every declaration this run elaborates, as Lean's
    /// `lean -D<name>=<value>`: `-D autoImplicit=false` or
    /// `-DautoImplicit=false`, repeatable, a later one for a name winning.
    ///
    /// The value is the option's INITIAL value in every file of the run — the
    /// file under check and every intra-project import elaborated from source,
    /// as Lake compiles every module of a package with its `leanOptions` — so
    /// an in-file `set_option` still overrides it. Refused before anything is
    /// elaborated, with pinned Lean's message: an argument with no `=`, a name
    /// pinned Lean 4.8.0's `-D` does not accept (Clean-only registry names
    /// included), or a `Bool` option given anything but `true` / `false`. A
    /// `Nat` value is read as C `atoi` reads it, as Lean does (`abc` is `0`).
    /// A Lean option Clean does not implement is accepted with a warning when
    /// it only prints, lints or profiles, or is set to Lean's default, and is
    /// refused otherwise.
    #[arg(short = 'D', value_name = "NAME=VALUE")]
    pub define: Vec<String>,
}

/// Subcommands for `clean cert` (proof-certificate verification).
#[derive(Subcommand)]
pub enum CertCommands {
    /// Verify a proof certificate against a serialized expression.
    Verify {
        /// Proof certificate JSON file
        cert: PathBuf,
        /// Serialized Expr JSON file (typically from extractProof)
        expr: PathBuf,
        /// Optional serialized Environment JSON file
        #[arg(long)]
        env: Option<PathBuf>,
        /// Verify against the smallest environment, NOT an axiom-free one.
        ///
        /// `Environment::new()` registers THREE axioms, not one: `sorry`,
        /// `trustedArith` and `trustedAy`. Each is typed `{α : Sort u} → α`, so
        /// each inhabits every type and each is exactly as strong as `sorry` —
        /// a certificate whose closure reaches any of the three proves nothing.
        /// With neither this flag nor `--env` the environment is the full
        /// prelude, which carries hundreds more; when `--env <file>` is given
        /// the serialized environment in that file is used and this flag is
        /// not consulted.
        #[arg(long)]
        minimal_env: bool,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Verify an external certificate JSON payload.
    VerifyExternal {
        /// External certificate file (JSON)
        cert: PathBuf,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Milliseconds an Alethe check may take before it is refused (`timeout`); 0 = no limit.
        #[arg(long, default_value = "600000")]
        timeout_ms: u64,
    },
    /// Verify a JSON array of external certificates.
    VerifyExternalBatch {
        /// JSON array of external certificates
        certs: PathBuf,
        /// Worker threads: 0 (default) = sequential on the calling thread; N >= 1 = an N-worker pool. No auto-sizing. Alethe checks run at most one per core at once, each on its own thread with a 1 GiB stack reservation.
        #[arg(short, long, default_value = "0")]
        threads: usize,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Milliseconds each Alethe check may take before it is refused (`timeout`); 0 = no limit.
        #[arg(long, default_value = "600000")]
        timeout_ms: u64,
    },
}

pub(crate) const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

pub(crate) const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-kernel",
    target: "clean-kernel",
};

/// Feature descriptors surfaced by the kernel crate (Phase 2 verbs).
///
/// The Phase 3 `clean kernel ...` verbs are published separately via
/// [`KERNEL_VERB_FEATURES`] so this file stays under the 500-line hard cap.
/// `clean-cli::registry::all_features()` extends both slices.
pub const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["check"],
        summary: "Type-check a Lean source file against the kernel",
        description: "\
Run the trusted kernel type-checker over every declaration in a Lean source \
file. The command elaborates each declaration, registers it in a fresh \
`Environment`, and reports per-declaration success, kernel failures, and \
trust-ledger events such as `sorry` usage.\n\n\
Use `--allow-sorry` when you are iterating on type signatures and want to \
accept declarations whose proofs are still `sorry` placeholders. Use \
`--verbose` to see each declaration's outcome alongside parse and check \
timings.\n\n\
Imports are FAIL-CLOSED. An `import` that resolves to no `.olean`, no \
intra-project `.lean` source, and no Clean prelude provider named for that \
module fails the check instead of silently substituting a hand-written \
stand-in. One namespace is provider-served by prefix rather than by name: a \
module called `Lean` or `Lean.*` with no `.olean` present is served the \
meta-type prelude stand-ins, logged at `warn`. Pass `--permissive-imports` to \
restore the substituting behavior; a run under that flag is not a verification \
claim.\n\n\
Every declaration gets a bounded, COOPERATIVE budget (`--decl-budget`, in \
kernel operations; `0` disables it). A declaration that spends the whole \
budget is reported `diverged` — its own verdict, listed under `Did not \
finish`, counted as neither a pass nor a failure — and the run continues to \
the next declaration. Without it one runaway declaration takes the whole \
file's report with it. The default is set far above anything measured to \
finish, so it does not change verdicts; recalibrate it with \
`scripts/decl_budget_calibrate.sh`.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean check foo.lean",
                what: "type-check every declaration in foo.lean",
            },
            Example {
                cmd: "clean check --allow-sorry draft.lean",
                what: "accept sorry-based declarations while iterating on signatures",
            },
            Example {
                cmd: "clean check --permissive-imports sketch.lean",
                what: "substitute stand-ins for imports that resolve to nothing (not a verification claim)",
            },
            Example {
                cmd: "clean check --decl-budget 50000000 slow.lean",
                what: "bound each declaration at 50M kernel operations; ones that overrun are reported `diverged`, and the rest of the file still gets measured",
            },
            Example {
                cmd: "clean check --automation-budget 0 slow.lean",
                what: "lift the per-declaration automation budget, for a declaration whose grind/simp search legitimately needs more",
            },
            Example {
                cmd: "clean check -DautoImplicit=false Foo.lean",
                what: "check under a Lean option, as `lean -D` and a lakefile's `leanOptions` set it; a bad `-D` is refused with Lean's message before anything is elaborated",
            },
        ],
        see_also: &["eval", "repl"],
        references: &[
            DESIGN_REF,
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
            CRATE_REF,
        ],
        domain_root: Some("check"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cert", "verify"],
        summary: "Verify a proof certificate against a kernel expression",
        description: "Type-checks a serialized proof term (`expr`) using the \
kernel, consults the accompanying proof certificate, and optionally loads a \
previously serialized environment. `--minimal-env` verifies against the \
smallest environment, which is NOT axiom-free: it carries `sorry`, \
`trustedArith` and `trustedAy`, each typed `{α : Sort u} → α` and so each an \
inhabitant of every type. The default with neither flag is the full prelude, \
with hundreds more; `--env <file>` supplies a serialized environment and takes \
precedence over `--minimal-env`. Read a certificate's own axiom closure; do \
not infer it from a flag.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean cert verify proof.cert.json proof.expr.json",
            what: "verify a certificate paired with its expression",
        }],
        see_also: &[
            "cert verify-external",
            "cert verify-external-batch",
            "fold verify",
        ],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("cert"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cert", "verify-external"],
        summary: "Verify an external certificate payload",
        description: "Runs the external-certificate bridge (Ay / Alethe / \
Farkas / entailment) for a single JSON payload produced by an external \
solver. NO KERNEL CHECK OCCURS: Farkas/entailment certificates are checked by \
pure rational arithmetic and Alethe/Ay by their own validators — the verdict \
never passes through `add_decl` or `check_type`, so it carries the bridge's \
authority, not the kernel's. An Alethe check that runs longer than \
`--timeout-ms` (600000 by default; 0 for no limit) is refused as `timeout`.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean cert verify-external proof.alethe.json",
            what: "verify a single external certificate",
        }],
        see_also: &["cert verify", "cert verify-external-batch"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("cert"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["cert", "verify-external-batch"],
        summary: "Verify a batch of external certificates",
        description: "Consumes a JSON array of external certificates. \
`--threads 0` (the default) verifies SEQUENTIALLY on the calling thread; \
`--threads N` (N >= 1) verifies in parallel on an N-worker rayon pool — there \
is no automatic host-CPU sizing. Each Alethe check that runs longer than \
`--timeout-ms` (600000 by default; 0 for no limit) is refused as `timeout`.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean cert verify-external-batch certs.json --threads 8",
            what: "batch-verify external certificates on an eight-worker pool",
        }],
        see_also: &["cert verify-external", "cert verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("cert"),
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
        // Validate every descriptor the crate publishes: Phase 2 + Phase 3.
        let descriptors: Vec<&FeatureDescriptor> =
            FEATURES.iter().chain(KERNEL_VERB_FEATURES.iter()).collect();
        ensure_unique_paths(&descriptors).expect("kernel descriptor paths are unique");
        for descriptor in descriptors {
            ensure_has_example(descriptor).expect("every kernel descriptor has ≥1 example");
        }
    }

    #[test]
    fn check_has_expected_path() {
        assert_eq!(FEATURES[0].path, &["check"]);
    }

    #[test]
    fn cert_verbs_are_registered() {
        let cert_paths: Vec<&[&str]> = FEATURES
            .iter()
            .map(|d| d.path)
            .filter(|p| p.first() == Some(&"cert"))
            .collect();
        assert_eq!(cert_paths.len(), 3);
    }

    /// Epic #3436 Phase 3 (#3443/#3444/#3445/#3446/#3447/#3510) + #3598
    /// classifier expect nine `kernel <verb>` descriptors: `lrat-conform`,
    /// `soundness-gate`, `verify-gamma-crown`, `generate-lean4-baseline`,
    /// `verify-constructive-claims`, `classify`, and the three `cert ...`
    /// verbs for `.cleancert` bundles.
    #[test]
    fn kernel_verbs_are_registered() {
        let kernel_paths: Vec<&[&str]> = KERNEL_VERB_FEATURES
            .iter()
            .map(|d| d.path)
            .filter(|p| p.first() == Some(&"kernel"))
            .collect();
        // 6 direct `kernel <verb>` entries + 3 `kernel cert <verb>` entries.
        assert_eq!(kernel_paths.len(), 9, "paths: {kernel_paths:?}");

        for expected in &[
            &["kernel", "lrat-conform"][..],
            &["kernel", "soundness-gate"][..],
            &["kernel", "verify-gamma-crown"][..],
            &["kernel", "verify-constructive-claims"][..],
            &["kernel", "generate-lean4-baseline"][..],
            &["kernel", "classify"][..],
            &["kernel", "cert", "verify"][..],
            &["kernel", "cert", "inspect"][..],
            &["kernel", "cert", "stats"][..],
        ] {
            assert!(
                kernel_paths.iter().any(|p| p == expected),
                "expected `{}` in kernel paths; got {kernel_paths:?}",
                expected.join(" ")
            );
        }
    }
}
