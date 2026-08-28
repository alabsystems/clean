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
//! <verb>` command tree that absorbs four orphan binaries. The enums and
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
    /// Alongside the kernel primitives it seeds several hundred VALUE-LESS
    /// axioms: the `Set` / `Subgroup` / `RingHom` / `SetTheory` stub
    /// signatures, the `IO` operations, the `sorry` / `sorryAx` /
    /// `trustedArith` / `trustedAy` trust markers, and the value-less `Fact`
    /// class stubs (`Fact`, `Fact.mk`, `Fact.out`) that a source or `.olean`
    /// redeclaration of Mathlib's genuine `class Fact` discharges. A theorem
    /// checked against this prelude is a PROOF only if its transitive closure
    /// avoids them — the live census, and the ratchet that keeps the count
    /// falling, are in `data/prelude_axiom_ratchet.json`.
    ///
    /// `Nat.lt_succ_iff`, `Nat.mul_lt_mul` and `Nat.mul_lt_mul_right` used to
    /// be named here as real Mathlib lemmas asserted rather than proved; #49
    /// retired all three (and the `instIrreflNatLt` instance) to kernel-checked
    /// declarations with empty axiom closures, so `Fact.mk` and `Fact.out` are
    /// the only asserted PROPOSITIONS this prelude still ships.
    #[default]
    Builtin,
    /// Load the Lean 4 core prelude via clean_olean.
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

/// Arguments accepted by `clean check`.
///
/// Exported so `clean-cli` can embed this struct inside its top-level
/// `Commands` enum without re-declaring the argument surface.
#[derive(Debug, Clone, Args)]
pub struct CheckArgs {
    /// File to check.
    pub file: PathBuf,
    /// Show verbose output.
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
    /// decremented at the kernel's existing heartbeat tick sites, so the same
    /// input spends the same fuel on any machine at any load, and no thread is
    /// ever killed. It is therefore only as tight as those tick sites are
    /// dense: a pathology whose cost is per-tick allocation SIZE rather than
    /// tick COUNT is not bounded by it.
    ///
    /// The default is deliberately far above anything measured to pass, so
    /// turning it on cannot move a verdict; see
    /// `clean_kernel::cli::DEFAULT_DECL_BUDGET`.
    #[arg(long, default_value_t = DEFAULT_DECL_BUDGET)]
    pub decl_budget: u64,
    /// Parse only: run the parser over the file and count per-declaration
    /// parse outcomes (parse OK / `RawDecl`-recovered / hard error) WITHOUT
    /// elaborating or kernel-checking anything. `RawDecl` recovery
    /// placeholders always count as failures, never as parses. With `--json`,
    /// emits a machine-readable parse report. `--prelude`, `--allow-sorry`,
    /// and `--imports-prefer-olean` are ignored in this mode — no declaration
    /// is registered and no verification verdict of any kind is minted.
    #[arg(long)]
    pub parse_only: bool,
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
        /// Use minimal environment (only `sorry` axiom)
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
    },
    /// Verify a JSON array of external certificates.
    VerifyExternalBatch {
        /// JSON array of external certificates
        certs: PathBuf,
        /// Number of worker threads (0 = auto)
        #[arg(short, long, default_value = "0")]
        threads: usize,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
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
stand-in. Pass `--permissive-imports` to restore the substituting behavior; a \
run under that flag is not a verification claim.\n\n\
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
previously serialized environment. Use `--minimal-env` for self-contained \
certificates whose only axiom is `sorry`.",
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
solver, then checks the result against the kernel.",
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
        description: "Consumes a JSON array of external certificates and \
verifies each one in parallel. Use `--threads 0` to pick a worker count \
automatically from the host CPU; otherwise `--threads N` pins the pool size.",
        category: Category::Verification,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean cert verify-external-batch certs.json --threads 0",
            what: "batch-verify external certificates with auto-sized pool",
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
