// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean mathverse stamp-verified` — productionized WS5 stamping pipeline.
//!
//! Runs the full convert → re-verify → stamp flow against real `.olean`
//! input and persists the kernel's `KernelVerified` verdict into the shard
//! bytes on disk:
//!
//! 1. Convert each input `.olean` to a heuristic `.mathverse` shard via
//!    [`convert_olean_to_mathverse`]. The heuristic importer never mints
//!    `KernelVerified`, so the on-disk stored count is 0 at this point.
//! 2. Load every shard into one [`MathverseLibrary`] and re-verify the merged
//!    corpus in Clean's kernel with
//!    [`verify_corpus_incremental`], seeded by `Environment::try_with_prelude`.
//!    The report's `kernel_verified_names` are exactly the constants whose
//!    value passed the kernel's `check_type` through `add_decl`.
//! 3. Build a [`KernelVerifiedManifest`] from that report and destructively
//!    stamp `KernelVerified` into the shard headers for those names via
//!    [`stamp_shard_dir_kernel_verified`].
//! 4. Re-read the stored `KernelVerified` count from disk with
//!    [`count_stored_kernel_verified`] and print a JSON summary.
//!
//! SOUNDNESS: a constant is stamped `KernelVerified` ONLY if it appears in
//! `report.kernel_verified_names` — i.e. the kernel accepted its value. The
//! heuristic converter's confidence is never promoted. Axioms, axiom
//! fallbacks, reconstruction failures, and outright failures are excluded
//! upstream by `verify_corpus_incremental` and are therefore never stamped.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::cli::closure_load::{
    build_closure_shards_for_target, load_targets_closure, load_targets_closure_mmap,
};
use crate::cli::closure_shards_dispatch::{cache_dir_is_populated, default_closure_cache_dir};
use crate::cli::{MathverseCliError, StampVerifiedArgs};
use crate::lean4::olean::olean_bridge::convert_olean_to_mathverse;
use crate::library::{
    count_stored_kernel_verified, stamp_shard_dir_kernel_verified, MathverseLibrary,
};
use crate::manifest::{MathverseManifest, ShardEntry};
use crate::shard::ShardReader;
use crate::trust::policy::TrustPolicy;
use crate::verify::incremental::{
    verify_corpus_incremental_with_env_policy, IncrementalVerifyReport, InductiveReplayPolicy,
};
use crate::verify::kernel_verified_manifest::{KernelVerifiedManifest, StampEnvFingerprint};

/// Machine-readable summary emitted by `clean mathverse stamp-verified`.
#[derive(Debug, Serialize)]
struct StampVerifiedSummary {
    ok: bool,
    generated_by: &'static str,
    /// `.olean` inputs that converted into a shard.
    oleans_converted: usize,
    /// `.olean` inputs that failed to parse/convert (path + reason).
    oleans_failed: Vec<(String, String)>,
    /// Output directory holding the stamped shards.
    out_dir: String,
    /// KernelVerified headers the heuristic converter stored BEFORE the kernel
    /// re-verification (soundness floor — must be 0).
    heuristic_kernel_verified: u32,
    /// Total constants the corpus re-verification considered.
    total: usize,
    /// Constants the kernel genuinely proof-checked (the stamp source).
    kernel_verified: usize,
    /// `NO_VALUE` constants accepted as well-formed axioms (not proof-checked).
    axiom_accepted: usize,
    /// Value-bearing Lean `unsafe def`s accepted TYPE-ONLY in trusted context
    /// (Lean bars unsafe consts from proofs, so they can never be
    /// proof-checked). Excluded from `kernel_verified`; not failures.
    unsafe_accepted: usize,
    /// Value-bearing constants that fell back to an axiom (not proof-checked).
    axiom_fallback: usize,
    /// Cause breakdown of the message-bearing `axiom_fallback` subset (values the
    /// kernel rejected), so coverage work can target the largest class. Sums to
    /// the count of recorded fallback errors; diagnostic only.
    axiom_fallback_by_class: AxiomFallbackHistogram,
    /// Constants whose kernel type-check failed.
    failed: usize,
    /// Cause breakdown of ALL hard non-verifications (`report.failures`): the
    /// `failed` (KernelRejected) decls PLUS reconstruction failures and
    /// dependency-cycle skips. Sums to `report.failures.len()` (which is
    /// `failed + reconstruct_failed + cycle_skipped`), so it is a strictly larger
    /// view than `failed` alone. This is the breakdown the `failed` bucket never
    /// had — it tells coverage work whether the dominant non-verification cause is
    /// L2 inductive-fail-closed, reconstruction coverage, cycles, or kernel
    /// TypeMismatch. Diagnostic only.
    failed_by_class: FailedHistogram,
    /// Shards rewritten with at least one raised header.
    shards_rewritten: usize,
    /// Headers raised to KernelVerified by the on-disk stamp.
    constants_stamped: usize,
    /// KernelVerified headers re-read from the shard bytes AFTER stamping.
    stored_kernel_verified: usize,
    /// Optional manifest path written.
    manifest: Option<String>,
    /// Path to the emitted MathverseManifest (`<out_dir>/manifest.json`) that
    /// makes the output dir loadable via `MATHVERSE_LIBRARY_PATH`. Distinct from
    /// `manifest` above (the optional KernelVerified-verdict sidecar).
    library_manifest: String,
    /// `--closure-root` mode: the dependency-closure context loaded BEFORE
    /// re-verifying the target module(s). `None` for the legacy prelude-only
    /// run. The closure constants are TRUSTED imports (never stamped); only the
    /// target module's decls earn `KernelVerified`.
    #[serde(skip_serializing_if = "Option::is_none")]
    closure: Option<ClosureSummary>,
    /// PARAGON `--parallel` only: wall-clock seconds for Phase A (sequential
    /// shared-base build). `None` for the sequential paths. Diagnostic.
    #[serde(skip_serializing_if = "Option::is_none")]
    phase_a_secs: Option<f64>,
    /// PARAGON `--parallel` only: wall-clock seconds for Phase B (the parallel
    /// convert+verify fan-out — the figure that scales with `--jobs`). `None`
    /// for the sequential paths.
    #[serde(skip_serializing_if = "Option::is_none")]
    phase_b_secs: Option<f64>,
    /// PARAGON `--parallel --incremental` only: modules whose verdict was
    /// replayed from the content-addressed cache (convert + verify skipped).
    /// `None` unless incremental caching was active.
    #[serde(skip_serializing_if = "Option::is_none")]
    cache_hits: Option<usize>,
    /// PARAGON `--parallel --incremental` only: modules freshly converted +
    /// re-verified this run (cache miss). `None` unless caching was active.
    #[serde(skip_serializing_if = "Option::is_none")]
    cache_misses: Option<usize>,
    /// PARAGON `--parallel` two-tier heartbeat escalation only: constants that
    /// failed the Tier-1 (`CLEAN_KERNEL_HEARTBEAT`) cap SPECIFICALLY on
    /// `HeartbeatExceeded` and then PASSED the escalated Tier-2
    /// (`CLEAN_KERNEL_HEARTBEAT_ESCALATE`) cap — the count of genuine
    /// KernelVerified recovered by escalation (a subset of `kernel_verified`).
    /// `None` when escalation was disabled or on the sequential paths.
    #[serde(skip_serializing_if = "Option::is_none")]
    heartbeat_escalated_recovered: Option<usize>,
}

/// Dependency-closure context summary for `--closure-root` runs.
#[derive(Debug, Serialize)]
struct ClosureSummary {
    /// Search root the target imports were resolved beneath.
    closure_root: String,
    /// First target module name (relative to the root).
    target_module: String,
    /// Distinct modules loaded into the closure env (the closure size),
    /// excluding the target module itself.
    modules_loaded: usize,
    /// Constants added to the env across the whole closure (trusted context).
    closure_constants: usize,
    /// Whether the shared cumulative env was reused across multiple targets
    /// (true when more than one target was given).
    shared_env: bool,
    /// Per-target incremental load breakdown — demonstrates the closure cache:
    /// the first target loads the bulk shared closure; later targets that share
    /// it load only their unique delta (often 0 new modules).
    per_target: Vec<PerTargetSummary>,
    /// Bounded-memory closure loading (WS3): the proof-value elision applied to
    /// the trusted closure env to cap resident memory.
    proof_elision: ProofElisionSummary,
}

/// Bounded-memory closure-loading result (WS3).
#[derive(Debug, Serialize)]
struct ProofElisionSummary {
    /// Elision policy applied: `none`, `opaque`, or `opaque-and-theorem`.
    policy: &'static str,
    /// `Opaque`-kind proof values dropped from the trusted closure env.
    opaque_elided: usize,
    /// `Theorem`-kind proof values dropped (0 unless policy includes theorems).
    theorem_elided: usize,
    /// Total never-unfolded proof values dropped.
    total_elided: usize,
}

/// One target's incremental slice of the shared-env closure load.
#[derive(Debug, Serialize)]
struct PerTargetSummary {
    /// Target module name (relative to the root).
    target_module: String,
    /// Distinct dependency modules this target added to the cumulative env that
    /// no earlier target had already loaded (0 = full closure-reuse hit).
    new_modules_loaded: usize,
    /// Constants this target's unique modules contributed to the trusted env.
    new_closure_constants: usize,
    /// Wall time spent loading this target's incremental closure slice (ms).
    load_millis: u128,
}

/// Cause-of-failure class for a value-bearing constant whose proof the kernel
/// rejected before it fell back to an axiom. Diagnostic only (it never affects a
/// verdict): it buckets the `axiom_fallback` residual so coverage work can target
/// the largest class first (e.g. raising the heartbeat budget recovers the
/// `Heartbeat` bucket, which the kernel COULD verify with more ticks).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FallbackClass {
    /// The kernel ran out of budget (heartbeat / memory / recursion / interrupt)
    /// — the proof is likely checkable with a larger `CLEAN_KERNEL_HEARTBEAT`.
    Heartbeat,
    /// A type/sort mismatch during reconstruction (incl. theorem-not-Prop).
    TypeMismatch,
    /// A referenced constant/inductive (a dependency) was not in the env.
    UnknownConst,
    /// A universe-level-parameter count/name disagreement.
    LevelMismatch,
    /// A structural inductive/structure/field error.
    Inductive,
    /// The declaration carried free variables or metavariables.
    Malformed,
    /// A value-bearing shard row with no stored value (opaque/meta gadget
    /// elided at olean→shard conversion) — an import-design trust boundary,
    /// not a rejected proof.
    NoValue,
    /// Anything not matched above.
    Other,
}

/// Classify a kernel `EnvError`/`TypeError` *Display string* (as stored in
/// `IncrementalVerifyReport::axiom_fallback_names`) into a [`FallbackClass`].
///
/// We match the kernel's stable `#[error(...)]` phrasing (clean-kernel
/// `env/types.rs` `EnvError` + `tc/type_error.rs` `TypeError`). Matching the
/// rendered message rather than the typed variant keeps this purely additive in
/// the CLI layer (no change to the verify core); a kernel message reword would
/// degrade a bucket to `Other` (visibly, never silently wrong) and is pinned by
/// `classify_*` unit tests. Order matters: more-specific causes are tested first.
fn classify_fallback_message(msg: &str) -> FallbackClass {
    let m = msg.to_ascii_lowercase();
    if m.contains("no value in shard for") {
        FallbackClass::NoValue
    } else if m.contains("heartbeat limit exceeded")
        || m.contains("excessive memory")
        || m.contains("deep recursion")
        || m.contains("type checking interrupted")
        || m.contains("pi-nesting depth")
    // SortDepthExceeded: a recoverable depth give-up
    {
        FallbackClass::Heartbeat
    } else if m.contains("unknown constant")
        || m.contains("unknown inductive")
        || m.contains("requires declaration")
    {
        FallbackClass::UnknownConst
    } else if m.contains("level count mismatch")
        || m.contains("universe level parameter")
        || m.contains("undefined level parameter")
    {
        FallbackClass::LevelMismatch
    } else if m.contains("type mismatch")
        || m.contains("must be a prop")
        || m.contains("expected sort")
        || m.contains("expected function type")
    {
        FallbackClass::TypeMismatch
    } else if m.contains("not a structure")
        || m.contains("number of fields")
        || m.contains("field name")
        || m.contains("codomain is not a sort")
        || m.contains("invalid projection") // all 4 projection variants are structural
        || m.contains("inductive")
    {
        FallbackClass::Inductive
    } else if m.contains("free variable")    // singular catches UnknownFVar + plural ContainsFreeVar
        || m.contains("unbound variable")
        || m.contains("metavariables")
    {
        FallbackClass::Malformed
    } else {
        // Note: CrossValidationFailure ("Cross-validation failure: ...") also lands
        // here. It is a kernel/micro-checker disagreement that should never reach
        // the axiom-fallback path; if `other` is ever nonzero, inspect the raw
        // `axiom_fallback_names` to rule it out.
        FallbackClass::Other
    }
}

/// Per-cause histogram of the message-bearing `axiom_fallback` subset (the
/// constants whose value the kernel rejected). Sums to
/// `axiom_fallback_names.len()`. Value-less fallbacks and the separately-counted
/// `failed`/reconstruct paths are NOT included. Diagnostic only.
#[derive(Debug, Default, Serialize)]
struct AxiomFallbackHistogram {
    heartbeat: usize,
    type_mismatch: usize,
    unknown_const: usize,
    level_mismatch: usize,
    inductive: usize,
    malformed: usize,
    no_value: usize,
    other: usize,
}

impl AxiomFallbackHistogram {
    fn tally(&mut self, class: FallbackClass) {
        match class {
            FallbackClass::Heartbeat => self.heartbeat += 1,
            FallbackClass::TypeMismatch => self.type_mismatch += 1,
            FallbackClass::UnknownConst => self.unknown_const += 1,
            FallbackClass::LevelMismatch => self.level_mismatch += 1,
            FallbackClass::Inductive => self.inductive += 1,
            FallbackClass::Malformed => self.malformed += 1,
            FallbackClass::NoValue => self.no_value += 1,
            FallbackClass::Other => self.other += 1,
        }
    }

    /// Build a histogram from the `axiom_fallback_names` error messages.
    fn from_messages<'a>(messages: impl Iterator<Item = &'a str>) -> Self {
        let mut hist = Self::default();
        for msg in messages {
            hist.tally(classify_fallback_message(msg));
        }
        hist
    }
}

/// Cause-of-failure class for an entry in `IncrementalVerifyReport::failures` —
/// the constants that did NOT verify and did NOT mask-fall-back to an axiom (i.e.
/// `KernelRejected` + `ReconstructFailed` + dependency cycles). Unlike
/// `axiom_fallback` (a value the kernel rejected that was re-added as an axiom),
/// these are hard non-verifications, and today they carry NO class breakdown
/// anywhere — the single biggest blind spot. This buckets them so coverage work
/// can rank the structural causes (L2 inductive-fail-closed vs reconstruction
/// coverage vs cycles) against the defeq cause (kernel TypeMismatch). Diagnostic
/// only; it never affects a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FailedClass {
    /// Inductive-family skeleton fail-closed: the replay metadata was missing or
    /// incompatible so the family was refused (the L2 path-(a) target). Matches
    /// the `inductive-family skeleton requires ...` messages from the verify core.
    InductiveFailClosed,
    /// FlatExpr reconstruction failed: the value was beyond the reconstructable
    /// prefix / the shard could not rebuild the term (`ReconstructFailed`).
    ReconstructFailed,
    /// The constant was skipped because it sits in a dependency cycle.
    DependencyCycle,
    /// A kernel `TypeMismatch` (or related defeq rejection) on the type itself —
    /// the same completeness gap as the `type_mismatch` fallback bucket, but here
    /// even the axiom-typed re-add failed (the *type* did not typecheck).
    KernelTypeMismatch,
    /// A referenced constant/inductive (a dependency) was not in the env.
    UnknownConst,
    /// A universe-level-parameter count/name disagreement.
    LevelMismatch,
    /// The kernel ran out of budget (heartbeat / memory / recursion).
    Heartbeat,
    /// Anything not matched above.
    Other,
}

/// Classify a `failures` entry error string into a [`FailedClass`].
///
/// Order matters: the structural `failed` causes (inductive fail-closed,
/// reconstruction, cycle) are detected first by their stable, in-tree phrasing
/// (verify-core `inductive-family skeleton requires ...` at
/// `verify/incremental/mod.rs:992`; the literal `"dependency cycle"` at
/// `:1218`/`:1384`; `"beyond reconstructable prefix"` from
/// `shard_reconstruct.rs`), then the kernel `TypeError`/`EnvError` causes are
/// reused from [`classify_fallback_message`] so the defeq/level/unknown-const
/// breakdown is consistent with the `axiom_fallback` histogram. Purely additive
/// in the CLI layer (no verify-core change); a phrasing reword degrades a bucket
/// to `Other` (visibly, never silently wrong) and is pinned by unit tests.
fn classify_failure_message(msg: &str) -> FailedClass {
    let m = msg.to_ascii_lowercase();
    if m.contains("inductive-family skeleton") || m.contains("add_inductive replay") {
        FailedClass::InductiveFailClosed
    } else if m.contains("dependency cycle") {
        FailedClass::DependencyCycle
    } else if m.contains("beyond reconstructable prefix")
        || m.contains("reconstruct")
        || m.contains("unsupported expression tag")
        || m.contains("index out of bounds")
    {
        FailedClass::ReconstructFailed
    } else {
        // Reuse the fallback classifier for the kernel TypeError/EnvError tail so
        // the defeq/level/unknown-const/heartbeat split matches the fallback
        // histogram exactly. `type_mismatch` here means the TYPE failed to check.
        match classify_fallback_message(msg) {
            FallbackClass::TypeMismatch => FailedClass::KernelTypeMismatch,
            FallbackClass::UnknownConst => FailedClass::UnknownConst,
            FallbackClass::LevelMismatch => FailedClass::LevelMismatch,
            FallbackClass::Heartbeat => FailedClass::Heartbeat,
            // Structural inductive errors from the kernel (not the fail-closed
            // skeleton message) still belong to the inductive bucket.
            FallbackClass::Inductive => FailedClass::InductiveFailClosed,
            FallbackClass::Malformed | FallbackClass::NoValue | FallbackClass::Other => {
                FailedClass::Other
            }
        }
    }
}

/// Per-cause histogram of the `failures` (the hard non-verifications). Sums to
/// `failures.len()` = `failed` (KernelRejected) + `reconstruct_failed` +
/// `cycle_skipped`. This is the breakdown the `failed` count never had before:
/// it separates the L2 inductive-fail-closed target, reconstruction-coverage
/// gaps, and dependency cycles from the kernel TypeMismatch (defeq) tail.
/// Diagnostic only.
#[derive(Debug, Default, Serialize)]
struct FailedHistogram {
    inductive_fail_closed: usize,
    reconstruct_failed: usize,
    dependency_cycle: usize,
    kernel_type_mismatch: usize,
    unknown_const: usize,
    level_mismatch: usize,
    heartbeat: usize,
    other: usize,
}

impl FailedHistogram {
    fn tally(&mut self, class: FailedClass) {
        match class {
            FailedClass::InductiveFailClosed => self.inductive_fail_closed += 1,
            FailedClass::ReconstructFailed => self.reconstruct_failed += 1,
            FailedClass::DependencyCycle => self.dependency_cycle += 1,
            FailedClass::KernelTypeMismatch => self.kernel_type_mismatch += 1,
            FailedClass::UnknownConst => self.unknown_const += 1,
            FailedClass::LevelMismatch => self.level_mismatch += 1,
            FailedClass::Heartbeat => self.heartbeat += 1,
            FailedClass::Other => self.other += 1,
        }
    }

    /// Build a histogram from the `failures` error messages.
    fn from_messages<'a>(messages: impl Iterator<Item = &'a str>) -> Self {
        let mut hist = Self::default();
        for msg in messages {
            hist.tally(classify_failure_message(msg));
        }
        hist
    }
}

/// Resolved lazy-vs-eager closure-serving decision for one `stamp-verified
/// --closure-root` run. `Lazy(dir)` ATTEMPTS to serve the closure from the v3
/// fail-closed shards in `dir`; a coverage/validity miss at load time still
/// hard-falls-back to the eager `.olean` closure (the hard invariant — see
/// [`cmd_stamp_verified`]). `Eager` skips lazy serving outright.
#[derive(Debug, PartialEq, Eq)]
enum ClosureServe {
    /// Serve lazily from this v3 closure-shard cache directory (load-time gate
    /// is the backstop).
    Lazy(PathBuf),
    /// Build the cache once into this directory, then serve lazily. Only ever
    /// returned by the PURE [`decide_closure_serve`]; [`resolve_closure_serve`]
    /// performs the build and collapses this to a terminal `Lazy`/`Eager`.
    BuildThenLazy(PathBuf),
    /// Reconstruct the closure eagerly from the trusted `.olean` import set.
    Eager,
}

/// The env-/flag-derived inputs to the closure-serve precedence decision.
/// Extracted so the precedence logic ([`decide_closure_serve`]) is a PURE,
/// env-free, side-effect-free function the tests exercise directly (no env-var
/// races, no `unsafe` `set_var`). `cmd_stamp_verified` builds this from
/// [`StampVerifiedArgs`] + env.
struct ClosureServeInputs {
    /// `--no-lazy-closure` or `CLEAN_LAZY_CLOSURE=0`.
    force_eager: bool,
    /// `--closure-shards <dir>` or non-empty `CLEAN_CLOSURE_SHARDS`.
    explicit: Option<PathBuf>,
    /// Co-located default cache dir (`<out-dir>/../.clean-closure-shards`).
    default_dir: PathBuf,
    /// `--build-closure-cache` or `CLEAN_BUILD_CLOSURE_CACHE=1`.
    build_opt_in: bool,
}

impl ClosureServeInputs {
    /// Read flags from `args` and the (deprecated, now-optional) env vars.
    fn from_args_and_env(args: &StampVerifiedArgs) -> Self {
        let force_eager = args.no_lazy_closure
            || std::env::var("CLEAN_LAZY_CLOSURE").ok().as_deref() == Some("0");
        let explicit = args.closure_shards.clone().or_else(|| {
            std::env::var("CLEAN_CLOSURE_SHARDS")
                .ok()
                .filter(|s| !s.is_empty())
                .map(PathBuf::from)
        });
        let build_opt_in = args.build_closure_cache
            || std::env::var("CLEAN_BUILD_CLOSURE_CACHE").ok().as_deref() == Some("1");
        Self {
            force_eager,
            explicit,
            default_dir: default_closure_cache_dir(&args.out_dir),
            build_opt_in,
        }
    }
}

/// PURE closure-serve precedence decision (no env reads, no filesystem writes).
/// Reads directory contents via [`cache_dir_is_populated`] only. Precedence:
///
/// 1. FORCE EAGER — `--no-lazy-closure` / `CLEAN_LAZY_CLOSURE=0`. Highest
///    precedence so a user can always opt out of the default-on ergonomics —
///    even when a populated cache exists.
/// 2. EXPLICIT OVERRIDE — `--closure-shards <dir>` / `CLEAN_CLOSURE_SHARDS`
///    (the gate + power-user path). A populated dir serves lazily; a
///    missing/empty one falls back to eager.
/// 3. AUTO-DISCOVER — the co-located default cache. If it exists and is
///    non-empty, serve lazily with NO env vars.
/// 4. OPT-IN BUILD — no cache found, but `--build-closure-cache` (or
///    `CLEAN_BUILD_CLOSURE_CACHE=1`): defer a one-time build into the default
///    dir, then serve lazily (the re-import workflow). A one-off run WITHOUT
///    this flag defaults to eager and never pays the build cost.
/// 5. EAGER — no cache, no opt-in build.
///
/// Legacy `CLEAN_LAZY_CLOSURE=1` still works: combined with
/// `CLEAN_CLOSURE_SHARDS` it hits case (2); with no override dir it simply lets
/// auto-discovery (case 3) proceed.
///
/// SOUNDNESS: every branch that cannot point at a populated cache returns
/// `ClosureServe::Eager`, and even a returned `Lazy`/`BuildThenLazy` only
/// ATTEMPTS lazy serving — the load-time digest/arena/coverage gate forces the
/// trusted eager fallback on any stale/foreign/corrupt/incomplete cache. Thus
/// auto-discovery can never serve a wrong verdict.
fn decide_closure_serve(inputs: &ClosureServeInputs) -> ClosureServe {
    // (1) Force eager wins over everything (even a populated explicit cache).
    if inputs.force_eager {
        return ClosureServe::Eager;
    }
    // (2) Explicit override.
    if let Some(dir) = &inputs.explicit {
        return if cache_dir_is_populated(dir) {
            ClosureServe::Lazy(dir.clone())
        } else {
            ClosureServe::Eager
        };
    }
    // (3) Auto-discover the co-located default cache.
    if cache_dir_is_populated(&inputs.default_dir) {
        return ClosureServe::Lazy(inputs.default_dir.clone());
    }
    // (4) Opt-in one-time build into the default dir.
    if inputs.build_opt_in {
        return ClosureServe::BuildThenLazy(inputs.default_dir.clone());
    }
    // (5) One-off run: eager (never pays the shard-build cost).
    ClosureServe::Eager
}

/// Resolve the closure-serve decision for this run, performing the opt-in build
/// side effect (and the diagnostics) the pure [`decide_closure_serve`] defers.
/// Returns a terminal `Lazy(dir)` / `Eager` the caller acts on. The build is
/// best-effort: an empty/failed build downgrades to eager (never breaks).
fn resolve_closure_serve(
    args: &StampVerifiedArgs,
    oleans: &[PathBuf],
    root: &Path,
) -> ClosureServe {
    let inputs = ClosureServeInputs::from_args_and_env(args);
    match decide_closure_serve(&inputs) {
        ClosureServe::Eager => {
            if inputs.force_eager {
                eprintln!("stamp-verified: lazy closure disabled (--no-lazy-closure / CLEAN_LAZY_CLOSURE=0) — using eager .olean closure");
            } else if let Some(dir) = &inputs.explicit {
                eprintln!(
                    "stamp-verified: explicit closure-shards `{}` is missing or empty — using eager .olean closure",
                    dir.display()
                );
            } else {
                eprintln!("stamp-verified: no closure cache found — using eager .olean closure (pass --build-closure-cache to build one for fast re-import)");
            }
            ClosureServe::Eager
        }
        ClosureServe::Lazy(dir) => {
            let how = if inputs.explicit.as_deref() == Some(dir.as_path()) {
                "explicit --closure-shards"
            } else {
                "auto-discovered"
            };
            eprintln!(
                "stamp-verified: cache found ({how} `{}`) — serving lazily",
                dir.display()
            );
            ClosureServe::Lazy(dir)
        }
        ClosureServe::BuildThenLazy(dir) => {
            eprintln!(
                "stamp-verified: no cache found — building closure cache into `{}` (--build-closure-cache)",
                dir.display()
            );
            build_closure_cache_for_targets(oleans, root, &dir);
            if cache_dir_is_populated(&dir) {
                eprintln!(
                    "stamp-verified: cache built at `{}` — serving lazily",
                    dir.display()
                );
                ClosureServe::Lazy(dir)
            } else {
                eprintln!(
                    "stamp-verified: closure cache build produced no shards — using eager .olean closure"
                );
                ClosureServe::Eager
            }
        }
    }
}

/// Best-effort build of the v3 fail-closed closure cache for every target olean
/// into `cache_dir` (the opt-in `--build-closure-cache` path). Per-target
/// failures are reported but never abort: a partial or empty cache simply forces
/// the eager fallback at load time, so this can never break the run.
fn build_closure_cache_for_targets(oleans: &[PathBuf], root: &Path, cache_dir: &Path) {
    for olean in oleans {
        match build_closure_shards_for_target(olean, root, cache_dir) {
            Ok((converted, skipped)) => eprintln!(
                "stamp-verified: closure cache for `{}`: {converted} converted, {skipped} skipped",
                olean.display()
            ),
            Err(e) => eprintln!(
                "stamp-verified: closure cache build for `{}` failed ({e}) — continuing (eager fallback will cover it)",
                olean.display()
            ),
        }
    }
}

/// `clean mathverse stamp-verified` entry point.
pub(crate) fn cmd_stamp_verified(args: StampVerifiedArgs) -> Result<(), MathverseCliError> {
    let oleans = collect_olean_files(&args.inputs);
    if oleans.is_empty() {
        let joined = args
            .inputs
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        return Err(MathverseCliError::StampNoInput(joined));
    }

    std::fs::create_dir_all(&args.out_dir)?;

    // PARAGON PARALLEL PATH (takes precedence): build ONE shared immutable base
    // env (every module + its dep closure, proof values elided) ONCE, then
    // re-verify every value-bearing target constant CONCURRENTLY against it. The
    // base supersedes the serial closure-load + env-threading of `--single-pass`.
    // Requires `--closure-root` (it resolves modules + computes module names
    // beneath the root). It produces the SAME convert→verify→stamp artifacts and
    // soundness floor as the sequential path; only the verification fan-out
    // differs.
    if args.parallel {
        return cmd_stamp_verified_parallel(args, &oleans);
    }

    // (1) Load the re-verification environment FIRST — it needs only `oleans`, so
    // streaming single-pass can convert each target JUST-IN-TIME against it,
    // bounding peak RSS to (closure + env + one module). The legacy merged path
    // converts all targets upfront (see `stamp_merged_convert_and_verify`). The
    // soundness floor + empty-input check now run after the convert+verify branch
    // (still BEFORE any stamping).
    //
    // In `--closure-root` mode the env is seeded
    // with the target module(s)' transitive import closure (trusted imported
    // context) on top of the prelude, so real Mathlib proof terms resolve their
    // referenced constants and can genuinely re-check. Otherwise it is the bare
    // prelude (legacy WS5b behavior), which only suffices for modules that carry
    // all their dependencies internally (e.g. foundational stdlib modules).
    let (mut initial_env, closure_summary) = match &args.closure_root {
        Some(root) => {
            // Phase-1 zero-copy HYBRID closure ("lazy default-on" ergonomics):
            // `resolve_closure_serve` decides (override → auto-discover → eager /
            // opt-in-build) WHERE the lazy closure-shard cache lives, killing the
            // old CLEAN_LAZY_CLOSURE + CLEAN_CLOSURE_SHARDS two-env-var dance. When
            // it returns `Lazy(dir)` the definitional kinds are served lazily from
            // mmap'd `.mathverse` shards (inductive families stay eager).
            //
            // SOUNDNESS (the hard invariant — eager hard-fallback ALWAYS preserved):
            // a `Lazy` decision only ATTEMPTS lazy serving. The v3 load-time
            // digest/arena binding rejects any stale/foreign/corrupt shard (it stays
            // unverified), and a coverage MISS returns `Ok(None)` here, which
            // hard-falls-back to the trusted eager `.olean` loader — so no run ever
            // loses a verdict or serves a wrong one. A bad explicit shard dir is the
            // only hard error (a configuration mistake, surfaced not silently
            // degraded); auto-discovery/opt-in-build can only ever choose eager.
            let closure = match resolve_closure_serve(&args, &oleans, root) {
                ClosureServe::Lazy(shards) => {
                    match load_targets_closure_mmap(
                        &oleans,
                        root,
                        args.closure_elide.to_kernel(),
                        &shards,
                    )? {
                        Some(lazy) => {
                            eprintln!(
                                "stamp-verified: serving closure defs lazily from {} (inductive families eager)",
                                shards.display()
                            );
                            lazy
                        }
                        None => {
                            // SOUNDNESS: cache found but verification failed (digest
                            // mismatch / arena recon fail / coverage miss) → eager
                            // fallback. This is the "never serve wrong" backstop.
                            eprintln!(
                                "stamp-verified: cache found but verification failed (coverage/validity miss) — eager .olean closure fallback"
                            );
                            load_targets_closure(&oleans, root, args.closure_elide.to_kernel())?
                        }
                    }
                }
                // SOUNDNESS: no usable lazy cache → trusted eager closure. Default
                // for a one-off run; never breaks. `resolve_closure_serve` never
                // returns `BuildThenLazy` (it performs the build and collapses to
                // `Lazy`/`Eager`); the arm exists only for match exhaustiveness and
                // is itself a safe eager fallback.
                ClosureServe::Eager | ClosureServe::BuildThenLazy(_) => {
                    load_targets_closure(&oleans, root, args.closure_elide.to_kernel())?
                }
            };
            let per_target = closure
                .per_target
                .iter()
                .map(|t| PerTargetSummary {
                    target_module: t.target_module.clone(),
                    new_modules_loaded: t.new_modules_loaded,
                    new_closure_constants: t.new_closure_constants,
                    load_millis: t.load_millis,
                })
                .collect();
            let proof_elision = ProofElisionSummary {
                policy: match closure.elision_policy {
                    clean_kernel::env::ProofValueElision::None => "none",
                    clean_kernel::env::ProofValueElision::OpaqueOnly => "opaque",
                    clean_kernel::env::ProofValueElision::OpaqueAndTheorem => "opaque-and-theorem",
                    _ => "unknown",
                },
                opaque_elided: closure.proof_elision.opaque_elided,
                theorem_elided: closure.proof_elision.theorem_elided,
                total_elided: closure.proof_elision.total_elided(),
            };
            let summary = ClosureSummary {
                closure_root: root.display().to_string(),
                target_module: closure.target_module,
                modules_loaded: closure.modules_loaded,
                closure_constants: closure.closure_constants,
                shared_env: oleans.len() > 1,
                per_target,
                proof_elision,
            };
            (closure.env, Some(summary))
        }
        None => {
            // WS17: import-verification prelude (lossy `extends`-structure stubs
            // suppressed) — see `load_targets_closure`.
            let prelude = clean_kernel::Environment::try_with_prelude_for_import()
                .map_err(|e| MathverseCliError::StampPrelude(e.to_string()))?;
            (prelude, None)
        }
    };
    // P0 (kernel completeness, KERNEL_COMPLETENESS_ROADMAP.md): allow raising or
    // removing the per-declaration heartbeat budget for the verification path via
    // CLEAN_KERNEL_HEARTBEAT ("0" = unlimited, matching the Lean 4 kernel, which
    // has no kernel-side heartbeat). The 2M default rejects valid-but-expensive
    // proofs on deep modules ("rejected for budget, not for being wrong"), the
    // single largest driver of non-verification. SOUNDNESS-NEUTRAL: a larger or
    // absent budget only lets MORE valid proofs finish; it never accepts an
    // invalid term. Per-decl wall-clock is bounded by the driver watchdog.
    if let Ok(hb) = std::env::var("CLEAN_KERNEL_HEARTBEAT") {
        if hb.parse::<u32>().is_ok() {
            initial_env.set_option("maxHeartbeats".to_string(), Some(hb));
        }
    }
    // DIAGNOSTIC (TCB-neutral): `CLEAN_PROFILE_HEARTBEATS=1` enables the kernel
    // heartbeat profiler so `HeartbeatExceeded` errors carry a per-category tick
    // snapshot (IsDefEq/InferType/Whnf/...) — mirrors the same hook in
    // `parallel_verify.rs`; used to attribute where over-budget proofs burn.
    if std::env::var("CLEAN_PROFILE_HEARTBEATS").is_ok_and(|v| v == "1" || v == "true") {
        initial_env.set_option("profileHeartbeats".to_string(), Some("true".to_string()));
    }
    // (2) Convert + verify. STREAMING single-pass converts each target JUST-IN-TIME
    // in import-topological order against the persistent closure env, writing its
    // shard and freeing it before the next — ONE closure load for the whole corpus,
    // peak RSS bounded by (closure + env + one module), never the all-shards-upfront
    // peak that OOMs a fixed-RAM box. The legacy merged path converts all upfront.
    //
    // Both paths replay inductive families Lean-faithfully
    // (`InductiveReplayPolicy::LeanFaithful` == `add_inductive_core`): install only
    // the kernel certificate and let the shard's own Lean-spelled convenience
    // definitions (`noConfusion`/`casesOn`/…) carry through the checked `add_decl`
    // path, rather than shadowing them with Clean's generated twins (the dominant
    // axiom_fallback `type_mismatch` tail). Soundness-neutral: every constant is
    // still installed through the fully-checked kernel path and re-checked
    // individually; STREAMING changes only the TIMING of conversion, not the
    // verification semantics (same per-module loop, topo order, and roll-elision).
    let StreamVerifyOutput {
        report,
        converted,
        failed,
        heuristic_kernel_verified,
    } = if args.single_pass {
        // Run streaming verification on a worker thread with a LARGE stack.
        // Full-corpus verification in import-topological order recurses deeply on
        // foundational terms and the large accumulated env — enough to overflow the
        // 8 MB main-thread stack (and even a 64 MB `ulimit -s`). A 1 GiB thread
        // stack is virtual (only touched pages commit) and gives ample headroom;
        // it changes neither the verification semantics nor what is stamped.
        let oleans_t = oleans.clone();
        let out_t = args.out_dir.clone();
        let closure_root_t = args.closure_root.clone();
        let elide_t = args.closure_elide.to_kernel();
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || {
                single_pass_verify_streaming(
                    initial_env,
                    &oleans_t,
                    &out_t,
                    closure_root_t.as_deref(),
                    elide_t,
                )
            })
            .expect("spawn streaming-verify worker thread")
            .join()
            .expect("streaming-verify worker thread panicked")?
    } else {
        stamp_merged_convert_and_verify(initial_env, &oleans, &args.out_dir)?
    };

    if converted == 0 {
        // Everything failed to convert: surface the first failure reason.
        let reason = failed
            .first()
            .map(|(p, e)| format!("{p}: {e}"))
            .unwrap_or_else(|| "no readable .olean modules".to_owned());
        return Err(MathverseCliError::StampNoInput(reason));
    }

    // SOUNDNESS FLOOR (self-enforcing): the heuristic converter must NEVER mint
    // KernelVerified — only Clean's kernel re-verification may. The counter sums
    // every conversion's `kernel_verified_from_tc` (raised in olean_bridge.rs ONLY
    // if a constant was marked KernelVerified without the kernel checking it). It
    // must be 0; a nonzero value means the floor was breached upstream, so fail
    // closed BEFORE anything is stamped (stamping is step 3, below).
    if heuristic_kernel_verified != 0 {
        return Err(MathverseCliError::StampHeuristicMintedKernelVerified(
            heuristic_kernel_verified,
        ));
    }

    // Env-gated per-decl faildump (WS13 triage hook). When CLEAN_WS13_FAILDUMP
    // names a file, write every masked / rejected decl with its error so the
    // residual completeness gaps can be ranked. Diagnostic-only: it does not
    // influence what gets stamped (only `kernel_verified_names` is stamped).
    if let Ok(dump_path) = std::env::var("CLEAN_WS13_FAILDUMP") {
        let mut buf = String::new();
        buf.push_str("# kind\tname\terror\n");
        for (name, err) in &report.axiom_fallback_names {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("masked-fallback\t{name}\t{one_line}\n"));
        }
        for (name, err) in &report.family_standins {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("family-standin\t{name}\t{one_line}\n"));
        }
        for (name, err) in &report.failures {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("failed\t{name}\t{one_line}\n"));
        }
        match std::fs::write(&dump_path, &buf) {
            Ok(()) => eprintln!(
                "WS13 faildump: wrote {} masked + {} failed to {dump_path}",
                report.axiom_fallback_names.len(),
                report.failures.len(),
            ),
            Err(e) => eprintln!("WS13 faildump: could not write {dump_path}: {e}"),
        }
    }

    // (3) Stamp the kernel's verdict into the shard bytes on disk. Only names
    // in report.kernel_verified_names are stamped — never heuristic confidence.
    let manifest = KernelVerifiedManifest::from_report(
        &args.out_dir.display().to_string(),
        converted,
        &report,
    )
    .with_env_fingerprint(StampEnvFingerprint {
        kernel_version: clean_kernel::VERSION.to_string(),
        // Captured at build time by build.rs
        // (`cargo:rustc-env=CLEAN_MATHVERSE_TOOLCHAIN_VERSION`),
        // so a toolchain bump re-keys the incremental cache; "unknown" only if
        // the build-time query failed.
        toolchain: option_env!("CLEAN_MATHVERSE_TOOLCHAIN_VERSION")
            .unwrap_or("unknown")
            .to_string(),
        heartbeat: std::env::var("CLEAN_KERNEL_HEARTBEAT")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "default".to_string()),
        elision_policy: match args.closure_elide.to_kernel() {
            clean_kernel::env::ProofValueElision::None => "none",
            clean_kernel::env::ProofValueElision::OpaqueOnly => "opaque",
            clean_kernel::env::ProofValueElision::OpaqueAndTheorem => "opaque-and-theorem",
            _ => "unknown",
        }
        .to_string(),
        max_closure_modules: crate::cli::closure_load::max_closure_modules(),
        prelude_variant: if args.closure_root.is_some() {
            "closure-root"
        } else {
            "prelude-only"
        }
        .to_string(),
    });
    let stamp = stamp_shard_dir_kernel_verified(&args.out_dir, &manifest)?;

    if let Some(manifest_path) = &args.manifest {
        if let Some(parent) = manifest_path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)?;
            }
        }
        manifest.write_to_file(manifest_path)?;
    }

    // (4) Re-read the stored KernelVerified count from the shard bytes on disk.
    let (stored_kernel_verified, unreadable) = count_stored_kernel_verified(&args.out_dir)?;

    // (5) Package: emit <out_dir>/manifest.json describing the already-stamped
    //     flat shards IN PLACE so `MATHVERSE_LIBRARY_PATH=<out_dir>` resolves via
    //     `load_built_library`. Packaging-only — shards are already final (the
    //     in-place stamp at step 3 ran before this), so it cannot change a verdict.
    let library_manifest = write_flat_manifest(&args.out_dir)?;

    let summary = StampVerifiedSummary {
        ok: unreadable.is_empty(),
        generated_by: "clean mathverse stamp-verified",
        oleans_converted: converted,
        oleans_failed: failed,
        out_dir: args.out_dir.display().to_string(),
        heuristic_kernel_verified,
        total: report.total,
        kernel_verified: report.kernel_verified,
        axiom_accepted: report.axiom_accepted,
        unsafe_accepted: report.unsafe_accepted,
        axiom_fallback: report.axiom_fallback,
        axiom_fallback_by_class: AxiomFallbackHistogram::from_messages(
            report.axiom_fallback_names.iter().map(|(_, e)| e.as_str()),
        ),
        failed: report.failed,
        failed_by_class: FailedHistogram::from_messages(
            report.failures.iter().map(|(_, e)| e.as_str()),
        ),
        shards_rewritten: stamp.shards_rewritten,
        constants_stamped: stamp.constants_stamped,
        stored_kernel_verified,
        manifest: args.manifest.as_ref().map(|p| p.display().to_string()),
        library_manifest: library_manifest.display().to_string(),
        closure: closure_summary,
        phase_a_secs: None,
        phase_b_secs: None,
        cache_hits: None,
        cache_misses: None,
        // Two-tier heartbeat escalation is a PARAGON `--parallel`-only feature.
        heartbeat_escalated_recovered: None,
    };

    // CLEAN_REDUCTION_STATS=<top-N>: dump the kernel's per-name reduction
    // statistics (whnf_miss_by_head / unfold_by_name / iota_by_rec / def-eq
    // head pairs) to stderr after the run — same diagnostic hook as
    // per_constant_load.rs. Report is empty unless clean-kernel was built with
    // the `reduction-stats` feature; counters never influence verdicts.
    if let Some(top) = std::env::var("CLEAN_REDUCTION_STATS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok().or(Some(30)))
    {
        eprintln!("{}", clean_kernel::reduction_stats_report(top));
    }

    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        eprintln!(
            "stamp-verified: {} olean(s) -> {} shard(s) in {}; \
             kernel_verified={} stored_kernel_verified={} (heuristic floor={})",
            summary.oleans_converted,
            summary.shards_rewritten,
            summary.out_dir,
            summary.kernel_verified,
            summary.stored_kernel_verified,
            summary.heuristic_kernel_verified,
        );
        let fc = &summary.failed_by_class;
        eprintln!(
            "  failed_by_class: inductive_fail_closed={} reconstruct_failed={} dependency_cycle={} kernel_type_mismatch={} unknown_const={} level_mismatch={} heartbeat={} other={}",
            fc.inductive_fail_closed,
            fc.reconstruct_failed,
            fc.dependency_cycle,
            fc.kernel_type_mismatch,
            fc.unknown_const,
            fc.level_mismatch,
            fc.heartbeat,
            fc.other,
        );
        if let Some(closure) = &summary.closure {
            eprintln!(
                "  closure: target={} modules_loaded={} closure_constants={} shared_env={} (trusted imports, not stamped)",
                closure.target_module,
                closure.modules_loaded,
                closure.closure_constants,
                closure.shared_env,
            );
            eprintln!(
                "  closure bounded-memory (WS3): elision={} dropped {} proof value(s) (opaque={}, theorem={})",
                closure.proof_elision.policy,
                closure.proof_elision.total_elided,
                closure.proof_elision.opaque_elided,
                closure.proof_elision.theorem_elided,
            );
            if closure.shared_env {
                for t in &closure.per_target {
                    eprintln!(
                        "    target {}: +{} new modules, +{} constants, {} ms (shared-env reuse)",
                        t.target_module,
                        t.new_modules_loaded,
                        t.new_closure_constants,
                        t.load_millis,
                    );
                }
            }
        }
        if !summary.oleans_failed.is_empty() {
            for (path, reason) in &summary.oleans_failed {
                eprintln!("  skipped {path}: {reason}");
            }
        }
    }

    maybe_emit_stamp_receipt(&args);
    Ok(())
}

/// TURNKEY `--receipt`: after stamping, mint a trust receipt over the
/// KernelVerified constants now in `--out-dir` — the same read
/// `trust-receipt from-shards` does, folded into the stamp command so `stamp →
/// certify` is one invocation. No-op unless `--receipt` is set. A receipt failure
/// is surfaced but does NOT fail the stamp (the shards are already written).
fn maybe_emit_stamp_receipt(args: &StampVerifiedArgs) {
    let Some(receipt_path) = args.receipt.as_deref() else {
        return;
    };
    match crate::cli::trust_receipt_cmd::build_receipt_from_shard_dir(
        &args.out_dir,
        args.source_id.clone(),
        Some(receipt_path),
        args.receipt_leaves.as_deref(),
        args.receipt_provenance.as_deref(),
    ) {
        Ok(s) => eprintln!(
            "stamp-verified: receipt minted — shard_constants={} kernel_verified={} root={} leaves={} within_tcb={}",
            s.shard_constants,
            s.kernel_verified,
            s.merkle_root,
            s.leaf_count,
            s.tcb_label(),
        ),
        Err(e) => eprintln!("stamp-verified: WARNING receipt not minted: {e}"),
    }
}

/// PARAGON parallel `clean mathverse stamp-verified --parallel` entry point.
///
/// Builds the shared immutable base (Phase A), re-verifies every target module's
/// value-bearing constants in parallel against it (Phase B), then runs the SAME
/// soundness-floor check, on-disk stamp, manifest emission, and JSON summary as
/// the sequential path (Phase C). `--closure-root` is required: the base loader
/// resolves modules and computes module names beneath the root.
fn cmd_stamp_verified_parallel(
    args: StampVerifiedArgs,
    oleans: &[PathBuf],
) -> Result<(), MathverseCliError> {
    let Some(root) = args.closure_root.clone() else {
        return Err(MathverseCliError::StampClosure {
            module: "<parallel>".to_string(),
            reason: "--parallel requires --closure-root (the .olean search root)".to_string(),
        });
    };
    // Track B2: an explicit `--jobs N` is honored verbatim; otherwise the
    // default is RAM-clamped (peak = base + jobs * per-module, so a small
    // RAM/12 cap is what keeps the heavy subtrees from jetsam-killing the run).
    let jobs = match args.jobs.filter(|&j| j > 0) {
        Some(explicit) => explicit,
        None => crate::cli::ram_budget::ram_aware_default_jobs(),
    };
    let elide = args.closure_elide.to_kernel();

    eprintln!(
        "stamp-verified --parallel: PARAGON over {} module(s), {jobs} job(s), elision={}",
        oleans.len(),
        match elide {
            clean_kernel::env::ProofValueElision::None => "none",
            clean_kernel::env::ProofValueElision::OpaqueOnly => "opaque",
            clean_kernel::env::ProofValueElision::OpaqueAndTheorem => "opaque-and-theorem",
            _ => "unknown",
        },
    );

    // FEATURE-UNION COHERENCE (PARAGON `--parallel` × lazy closure-shards): the two
    // features are orthogonal in PURPOSE — `--parallel` is verify PARALLELISM,
    // `--closure-shards`/`--build-closure-cache`/`--no-lazy-closure` are closure
    // SOURCING — but they are NOT yet composed in code. The lazy closure-shard
    // serving (`load_targets_closure_mmap`) is built for the SEQUENTIAL model,
    // which EXCLUDES the targets and serves only their dependency closure; the
    // PARAGON base (`build_base_env`) instead loads targets AND deps EAGERLY so it
    // can re-check every target constant read-only against them, and the lazy
    // shard cache deliberately omits the targets. Wiring lazy-served deps into the
    // parallel base is a genuine new feature (its own coverage gate over the
    // include-targets base), not a mechanical merge reconciliation, so the
    // documented precedence holds: `--parallel` uses the eager base. Make that
    // VISIBLE rather than silently no-opping the closure-serve flags (matching the
    // codebase's "downgrade is observable, never silent" discipline). SOUNDNESS is
    // untouched either way — the eager base is the trusted path, and lazy serving
    // is a completeness/RAM optimization that can only ever fall back TO eager.
    if args.closure_shards.is_some()
        || args.build_closure_cache
        || args.no_lazy_closure
        || std::env::var("CLEAN_CLOSURE_SHARDS")
            .ok()
            .is_some_and(|s| !s.is_empty())
        || std::env::var("CLEAN_BUILD_CLOSURE_CACHE").ok().as_deref() == Some("1")
        || std::env::var("CLEAN_LAZY_CLOSURE").ok().as_deref() == Some("0")
    {
        eprintln!(
            "stamp-verified --parallel: NOTE — lazy closure-shard serving \
             (--closure-shards / --build-closure-cache / --no-lazy-closure) applies to the \
             SEQUENTIAL path; --parallel always loads its shared base eagerly from .olean. \
             These closure-serve flags have no effect under --parallel (drop --parallel to \
             use lazy closure shards)."
        );
    }

    // Build the env fingerprint up front: it is BOTH the incremental-cache key
    // prefix (folded into every module's closure hash) AND the manifest's
    // reproducibility record — one source of truth, so a re-import after a
    // kernel change re-keys every module and honestly re-verifies.
    let fingerprint = StampEnvFingerprint {
        kernel_version: clean_kernel::VERSION.to_string(),
        // Captured at build time by build.rs so a toolchain bump re-keys the
        // incremental cache (folded into every module's closure hash via
        // `cache_key`); "unknown" only if the build-time query failed.
        toolchain: option_env!("CLEAN_MATHVERSE_TOOLCHAIN_VERSION")
            .unwrap_or("unknown")
            .to_string(),
        heartbeat: std::env::var("CLEAN_KERNEL_HEARTBEAT")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "default".to_string()),
        elision_policy: match elide {
            clean_kernel::env::ProofValueElision::None => "none",
            clean_kernel::env::ProofValueElision::OpaqueOnly => "opaque",
            clean_kernel::env::ProofValueElision::OpaqueAndTheorem => "opaque-and-theorem",
            _ => "unknown",
        }
        .to_string(),
        max_closure_modules: crate::cli::closure_load::max_closure_modules(),
        prelude_variant: "closure-root-parallel".to_string(),
    };
    let cache_key = fingerprint.cache_key();
    let cache_path = args.out_dir.join(".import_cache.json");
    let incremental = if args.incremental {
        eprintln!(
            "stamp-verified --parallel: incremental cache at {}",
            cache_path.display()
        );
        Some(crate::cli::parallel_verify::IncrementalCache {
            cache_path: &cache_path,
            fingerprint: &cache_key,
        })
    } else {
        None
    };

    let crate::cli::parallel_verify::ParallelVerifyOutput {
        report,
        converted,
        failed,
        heuristic_kernel_verified,
        base_modules_loaded,
        base_constants,
        base_proof_values_elided,
        phase_a_secs,
        phase_b_secs,
        cache_hits,
        cache_misses,
    } = crate::cli::parallel_verify::parallel_convert_and_verify(
        oleans,
        &args.out_dir,
        &root,
        elide,
        jobs,
        incremental,
    )?;

    if args.incremental {
        eprintln!(
            "stamp-verified --parallel: incremental cache — {cache_hits} hit(s) (skipped convert+verify), {cache_misses} miss(es)"
        );
    }

    if converted == 0 {
        let reason = failed
            .first()
            .map(|(p, e)| format!("{p}: {e}"))
            .unwrap_or_else(|| "no readable .olean modules".to_owned());
        return Err(MathverseCliError::StampNoInput(reason));
    }

    // SOUNDNESS FLOOR: the heuristic converter must NEVER mint KernelVerified.
    if heuristic_kernel_verified != 0 {
        return Err(MathverseCliError::StampHeuristicMintedKernelVerified(
            heuristic_kernel_verified,
        ));
    }

    // Env-gated per-decl faildump (WS13 triage hook), mirroring the non-parallel
    // path above. Diagnostic-only: does not influence what gets stamped.
    if let Ok(dump_path) = std::env::var("CLEAN_WS13_FAILDUMP") {
        let mut buf = String::new();
        buf.push_str("# kind\tname\terror\n");
        for (name, err) in &report.axiom_fallback_names {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("masked-fallback\t{name}\t{one_line}\n"));
        }
        for (name, err) in &report.family_standins {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("family-standin\t{name}\t{one_line}\n"));
        }
        for (name, err) in &report.failures {
            let one_line = err.replace('\n', " / ");
            buf.push_str(&format!("failed\t{name}\t{one_line}\n"));
        }
        match std::fs::write(&dump_path, &buf) {
            Ok(()) => eprintln!(
                "WS13 faildump: wrote {} masked + {} failed to {dump_path}",
                report.axiom_fallback_names.len(),
                report.failures.len(),
            ),
            Err(e) => eprintln!("WS13 faildump: could not write {dump_path}: {e}"),
        }
    }

    // Stamp the kernel's verdict into the shard bytes on disk. Only names in
    // report.kernel_verified_names are stamped — exactly the constants whose
    // value `check_decl_readonly` accepted.
    let manifest = KernelVerifiedManifest::from_report(
        &args.out_dir.display().to_string(),
        converted,
        &report,
    )
    .with_env_fingerprint(fingerprint);
    let stamp = stamp_shard_dir_kernel_verified(&args.out_dir, &manifest)?;

    if let Some(manifest_path) = &args.manifest {
        if let Some(parent) = manifest_path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)?;
            }
        }
        manifest.write_to_file(manifest_path)?;
    }

    let (stored_kernel_verified, unreadable) = count_stored_kernel_verified(&args.out_dir)?;
    let library_manifest = write_flat_manifest(&args.out_dir)?;

    let closure_summary = ClosureSummary {
        closure_root: root.display().to_string(),
        target_module: oleans
            .first()
            .map(|p| module_name_for_summary(p, &root))
            .unwrap_or_default(),
        modules_loaded: base_modules_loaded,
        closure_constants: base_constants,
        shared_env: true,
        per_target: Vec::new(),
        proof_elision: ProofElisionSummary {
            policy: match elide {
                clean_kernel::env::ProofValueElision::None => "none",
                clean_kernel::env::ProofValueElision::OpaqueOnly => "opaque",
                clean_kernel::env::ProofValueElision::OpaqueAndTheorem => "opaque-and-theorem",
                _ => "unknown",
            },
            // The base loader reports the TOTAL elided; theorem vs opaque split is
            // not tracked separately on the parallel path (diagnostic only).
            opaque_elided: 0,
            theorem_elided: 0,
            total_elided: base_proof_values_elided,
        },
    };

    let summary = StampVerifiedSummary {
        ok: unreadable.is_empty(),
        generated_by: "clean mathverse stamp-verified --parallel",
        oleans_converted: converted,
        oleans_failed: failed,
        out_dir: args.out_dir.display().to_string(),
        heuristic_kernel_verified,
        total: report.total,
        kernel_verified: report.kernel_verified,
        axiom_accepted: report.axiom_accepted,
        unsafe_accepted: report.unsafe_accepted,
        axiom_fallback: report.axiom_fallback,
        axiom_fallback_by_class: AxiomFallbackHistogram::from_messages(
            report.axiom_fallback_names.iter().map(|(_, e)| e.as_str()),
        ),
        failed: report.failed,
        failed_by_class: FailedHistogram::from_messages(
            report.failures.iter().map(|(_, e)| e.as_str()),
        ),
        shards_rewritten: stamp.shards_rewritten,
        constants_stamped: stamp.constants_stamped,
        stored_kernel_verified,
        manifest: args.manifest.as_ref().map(|p| p.display().to_string()),
        library_manifest: library_manifest.display().to_string(),
        closure: Some(closure_summary),
        phase_a_secs: Some(phase_a_secs),
        phase_b_secs: Some(phase_b_secs),
        cache_hits: args.incremental.then_some(cache_hits),
        cache_misses: args.incremental.then_some(cache_misses),
        // Report the escalation's effect whenever it recovered at least one
        // constant. 0 (disabled, or enabled-but-nothing-to-recover) is omitted.
        heartbeat_escalated_recovered: (report.heartbeat_escalated_recovered > 0)
            .then_some(report.heartbeat_escalated_recovered),
    };

    if args.json {
        let stdout = io::stdout();
        let mut out = stdout.lock();
        writeln!(out, "{}", serde_json::to_string_pretty(&summary)?)?;
    } else {
        eprintln!(
            "stamp-verified --parallel: {} olean(s) -> {} shard(s) in {}; \
             kernel_verified={} stored_kernel_verified={} (heuristic floor={}); \
             base: {} modules, {} constants, {} proof values elided; \
             phaseA={:.2}s phaseB={:.2}s ({jobs} jobs)",
            summary.oleans_converted,
            summary.shards_rewritten,
            summary.out_dir,
            summary.kernel_verified,
            summary.stored_kernel_verified,
            summary.heuristic_kernel_verified,
            base_modules_loaded,
            base_constants,
            base_proof_values_elided,
            phase_a_secs,
            phase_b_secs,
        );
        if let Some(recovered) = summary.heartbeat_escalated_recovered {
            eprintln!(
                "  two-tier heartbeat escalation recovered {recovered} constant(s) to KernelVerified (Tier-1 HeartbeatExceeded -> Tier-2 pass)"
            );
        }
        if !summary.oleans_failed.is_empty() {
            for (path, reason) in &summary.oleans_failed {
                eprintln!("  skipped {path}: {reason}");
            }
        }
    }

    maybe_emit_stamp_receipt(&args);
    Ok(())
}

/// Module name for a target olean relative to the closure root (summary only).
fn module_name_for_summary(olean: &Path, root: &Path) -> String {
    clean_olean::verify_batch::module_name_from_path(olean, root)
}

/// Emit `<out_dir>/manifest.json` describing the flat, already-stamped shards IN
/// PLACE, so `load_built_library(out_dir)` / `MATHVERSE_LIBRARY_PATH=<out_dir>`
/// resolves. Packaging-only: it reads each shard's bytes/header and writes one
/// JSON file; it never moves a shard, calls the kernel, or alters a verdict.
///
/// Only TOP-LEVEL `<out_dir>/*.mathverse` files are indexed (matching the flat
/// shards this command emits), so every `ShardEntry.path` is a bare, `/`-free
/// filename. `LibraryLoader` resolves it via `root.join(path)` (no `base/`/
/// `delta/` dirs needed), AND the non-recursive `cli::dispatch` loader sees the
/// exact same set — the two loaders cannot diverge. To avoid silent data loss,
/// it refuses (`StampManifestClobber`) to overwrite a pre-existing delta-bearing
/// (real built/release) manifest; a flat base-only re-run regenerates cleanly.
/// Returns the manifest path.
fn write_flat_manifest(out_dir: &Path) -> Result<PathBuf, MathverseCliError> {
    let manifest_path = out_dir.join("manifest.json");

    // Idempotent flat re-runs (our own output is base-only, no delta) regenerate
    // cleanly, but refuse to silently clobber a pre-existing delta-bearing
    // (real built/release) library manifest this command did not produce.
    if manifest_path.exists() {
        if let Ok(existing) = MathverseManifest::from_file(&manifest_path) {
            if !existing.delta_shards.is_empty() {
                return Err(MathverseCliError::StampManifestClobber(
                    out_dir.display().to_string(),
                ));
            }
        }
    }

    // stamp-verified writes FLAT <out_dir>/<stem>.mathverse. Enumerate the
    // TOP LEVEL only (NOT recursively) so every ShardEntry.path is a bare
    // filename: load_built_library (root.join) and the non-recursive
    // cli::dispatch loader then resolve the SAME shard set, and a foreign
    // nested base/delta layout is never swept into a flat manifest.
    let mut shard_files: Vec<PathBuf> = std::fs::read_dir(out_dir)?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|ext| ext == "mathverse"))
        .collect();
    shard_files.sort();

    let mut manifest = MathverseManifest::new();
    for path in &shard_files {
        let bytes = std::fs::read(path)?;
        let reader = ShardReader::from_bytes(&bytes)?;
        // Top-level file name = the bare, flat, '/'-free relative path.
        let name = path
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "shard.mathverse".to_owned());
        let stem = path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "module".to_owned());
        manifest.add_base_shard(ShardEntry {
            path: name,
            content_hash: blake3::hash(&bytes).to_hex().to_string(),
            constant_count: reader.header.constant_count,
            expr_count: reader.header.expr_count,
            source: stem,
        });
    }
    manifest.save(&manifest_path)?;
    Ok(manifest_path)
}

/// Output of the convert+verify step, returned by both the streaming single-pass
/// path and the legacy merged path so the caller treats them uniformly.
struct StreamVerifyOutput {
    /// Accumulated kernel verdict over every verified module.
    report: IncrementalVerifyReport,
    /// Count of `.olean`s that converted to a shard (== shards written to out_dir).
    converted: usize,
    /// `(path, reason)` for `.olean`s that failed to convert.
    failed: Vec<(String, String)>,
    /// Sum of the heuristic converter's `kernel_verified_from_tc` — MUST be 0
    /// (soundness floor enforced by the caller before any stamping).
    heuristic_kernel_verified: u32,
}

/// STREAMING single-pass: convert each target `.olean` to its shard JUST BEFORE
/// verifying it (in import-topological order), write the shard to `out_dir`,
/// verify it against the persistent closure `env`, roll-elide, then FREE it before
/// the next module. The whole corpus is verified against ONE closure load with
/// peak RSS bounded by (closure + accumulating env + one module) — never the
/// all-shards-upfront footprint, and never the per-batch closure RELOADS the bash
/// driver incurred.
///
/// SOUNDNESS: semantics are IDENTICAL to the prior pre-converted single-pass —
/// the same per-module [`verify_corpus_incremental_with_env_policy`]
/// (`InductiveReplayPolicy::LeanFaithful`) replay, the same
/// [`build_dependency_order`] topo order, the same rolling
/// [`Environment::elide_proof_values`]. ONLY the timing of conversion moves
/// (just-in-time vs upfront); nothing is stamped that the kernel did not check.
fn single_pass_verify_streaming(
    mut env: clean_kernel::Environment,
    oleans: &[PathBuf],
    out_dir: &Path,
    closure_root: Option<&Path>,
    elide: clean_kernel::env::ProofValueElision,
) -> Result<StreamVerifyOutput, MathverseCliError> {
    // Import-topological order over the TARGET oleans (deps before dependents),
    // from import headers only — no conversion is needed to compute the order.
    let ordered: Vec<PathBuf> = match closure_root {
        Some(root) => clean_olean::verify_batch::build_dependency_order(oleans, root)
            .0
            .into_iter()
            .map(|m| m.path)
            .collect(),
        None => oleans.to_vec(),
    };
    // Attempt EVERY input: append any olean missing from the ordered list (e.g. an
    // import-parse failure dropped it from the dependency graph) at the end, so
    // streaming never silently skips a target the upfront path would have tried.
    let ordered_set: HashSet<&Path> = ordered.iter().map(|p| p.as_path()).collect();
    let mut order: Vec<&Path> = ordered.iter().map(|p| p.as_path()).collect();
    for o in oleans {
        if !ordered_set.contains(o.as_path()) {
            order.push(o.as_path());
        }
    }

    let mut acc = empty_incremental_report();
    let mut converted = 0usize;
    let mut failed: Vec<(String, String)> = Vec::new();
    let mut heuristic_kernel_verified = 0u32;
    let mut used_stems: BTreeSet<String> = BTreeSet::new();

    for path in order {
        // Convert THIS module now; write its (heuristic) shard to out_dir.
        let (buf, convert) = match convert_olean_to_mathverse(path) {
            Ok(x) => x,
            Err(e) => {
                failed.push((path.display().to_string(), e.to_string()));
                continue;
            }
        };
        heuristic_kernel_verified += convert.kernel_verified_from_tc;
        let shard_path = unique_shard_path(out_dir, path, &mut used_stems);
        std::fs::write(&shard_path, &buf)?;
        let reader = ShardReader::from_bytes(&buf)?;
        let mut one = MathverseLibrary::new(TrustPolicy::permissive());
        one.load_shard(&reader)?;
        let (next_env, rep) = verify_corpus_incremental_with_env_policy(
            &one,
            env,
            InductiveReplayPolicy::LeanFaithful,
        );
        env = next_env;
        // Roll-elide the just-verified module's proof values before the next one,
        // bounding peak RSS. Idempotent: only newly-added values are dropped.
        env.elide_proof_values(elide);
        merge_incremental_report(&mut acc, rep);
        converted += 1;
        // `buf`, `reader`, `one` drop here — freed before the next module.
    }
    Ok(StreamVerifyOutput {
        report: acc,
        converted,
        failed,
        heuristic_kernel_verified,
    })
}

/// Legacy merged path: convert ALL targets upfront, write their shards, load them
/// into one library, and re-verify the merged corpus in one pass. Higher peak RSS
/// (holds every shard resident) but verifies all constants in a single global
/// constant-level topological order. Kept for `--single-pass`-off callers/tests.
fn stamp_merged_convert_and_verify(
    initial_env: clean_kernel::Environment,
    oleans: &[PathBuf],
    out_dir: &Path,
) -> Result<StreamVerifyOutput, MathverseCliError> {
    let mut shards: Vec<ShardReader> = Vec::with_capacity(oleans.len());
    let mut converted = 0usize;
    let mut failed: Vec<(String, String)> = Vec::new();
    let mut heuristic_kernel_verified = 0u32;
    let mut used_stems: BTreeSet<String> = BTreeSet::new();

    for olean in oleans {
        match convert_olean_to_mathverse(olean) {
            Ok((buf, convert)) => {
                heuristic_kernel_verified += convert.kernel_verified_from_tc;
                let shard_path = unique_shard_path(out_dir, olean, &mut used_stems);
                std::fs::write(&shard_path, &buf)?;
                shards.push(ShardReader::from_bytes(&buf)?);
                converted += 1;
            }
            Err(e) => failed.push((olean.display().to_string(), e.to_string())),
        }
    }

    // No shards converted: hand back zero so the caller emits the no-input error.
    if shards.is_empty() {
        return Ok(StreamVerifyOutput {
            report: empty_incremental_report(),
            converted,
            failed,
            heuristic_kernel_verified,
        });
    }

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    for shard in &shards {
        lib.load_shard(shard)?;
    }
    let report = verify_corpus_incremental_with_env_policy(
        &lib,
        initial_env,
        InductiveReplayPolicy::LeanFaithful,
    )
    .1;
    Ok(StreamVerifyOutput {
        report,
        converted,
        failed,
        heuristic_kernel_verified,
    })
}

/// A zeroed [`IncrementalVerifyReport`] to accumulate per-module results into.
fn empty_incremental_report() -> IncrementalVerifyReport {
    IncrementalVerifyReport {
        total: 0,
        kernel_verified: 0,
        axiom_accepted: 0,
        unsafe_accepted: 0,
        axiom_fallback: 0,
        axiom_fallback_names: Vec::new(),
        family_standins: Vec::new(),
        standin_blocked_fallbacks: Vec::new(),
        failed: 0,
        cycle_skipped: 0,
        reconstruct_failed: 0,
        inductive_registered: 0,
        seeded_checked: 0,
        seeded_unchecked: 0,
        failures: Vec::new(),
        kernel_verified_names: Vec::new(),
        discharged_axiom_names: Vec::new(),
        elapsed_secs: 0.0,
        heartbeat_escalated_recovered: 0,
    }
}

/// Fold a per-module report into the single-pass accumulator.
fn merge_incremental_report(acc: &mut IncrementalVerifyReport, r: IncrementalVerifyReport) {
    acc.total += r.total;
    acc.kernel_verified += r.kernel_verified;
    acc.axiom_accepted += r.axiom_accepted;
    acc.unsafe_accepted += r.unsafe_accepted;
    acc.axiom_fallback += r.axiom_fallback;
    acc.axiom_fallback_names.extend(r.axiom_fallback_names);
    acc.family_standins.extend(r.family_standins);
    acc.standin_blocked_fallbacks
        .extend(r.standin_blocked_fallbacks);
    acc.failed += r.failed;
    acc.cycle_skipped += r.cycle_skipped;
    acc.reconstruct_failed += r.reconstruct_failed;
    acc.inductive_registered += r.inductive_registered;
    acc.seeded_checked += r.seeded_checked;
    acc.seeded_unchecked += r.seeded_unchecked;
    acc.failures.extend(r.failures);
    acc.kernel_verified_names.extend(r.kernel_verified_names);
    acc.discharged_axiom_names.extend(r.discharged_axiom_names);
    acc.elapsed_secs += r.elapsed_secs;
}

/// Expand the user-supplied inputs into a deduplicated, sorted list of
/// `.olean` files. Directory inputs are walked recursively.
fn collect_olean_files(inputs: &[PathBuf]) -> Vec<PathBuf> {
    let mut found: BTreeSet<PathBuf> = BTreeSet::new();
    for input in inputs {
        if input.is_dir() {
            collect_oleans_in_dir(input, &mut found);
        } else if is_olean(input) {
            found.insert(input.clone());
        }
    }
    found.into_iter().collect()
}

/// Recursively collect `.olean` files under `dir`.
fn collect_oleans_in_dir(dir: &Path, out: &mut BTreeSet<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_oleans_in_dir(&path, out);
        } else if is_olean(&path) {
            out.insert(path);
        }
    }
}

fn is_olean(path: &Path) -> bool {
    path.extension().and_then(|e| e.to_str()) == Some("olean")
}

/// Build a collision-free `<stem>.mathverse` path under `out_dir`. Two input
/// modules can share a file stem (e.g. `Init/Data/Nat.olean` and
/// `Init/Nat.olean`); we suffix duplicates so neither shard is overwritten.
fn unique_shard_path(out_dir: &Path, olean: &Path, used: &mut BTreeSet<String>) -> PathBuf {
    let stem = olean
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "module".to_owned());
    let mut candidate = stem.clone();
    let mut counter = 1usize;
    while used.contains(&candidate) {
        candidate = format!("{stem}-{counter}");
        counter += 1;
    }
    used.insert(candidate.clone());
    out_dir.join(format!("{candidate}.mathverse"))
}

#[cfg(test)]
mod soundness_floor_tests {
    use super::*;

    // The floor check compares the accumulated heuristic counter against 0 and
    // returns the dedicated typed error. This test documents the exact mapping
    // from a nonzero counter to the fail-closed variant so a future refactor
    // cannot silently downgrade it (e.g. to a warning or an ignored value).
    #[test]
    fn test_stamp_heuristic_minted_kernel_verified_is_fail_closed_variant() {
        let n: u32 = 3;
        let err = MathverseCliError::StampHeuristicMintedKernelVerified(n);
        let msg = err.to_string();
        assert!(
            msg.contains("SOUNDNESS FLOOR VIOLATION"),
            "floor violation must be self-describing, got: {msg}"
        );
        assert!(
            msg.contains("must be 0"),
            "message must state the invariant, got: {msg}"
        );
        assert!(
            matches!(
                err,
                MathverseCliError::StampHeuristicMintedKernelVerified(c) if c == n
            ),
            "variant must carry the offending count"
        );
    }
}

#[cfg(test)]
mod axiom_fallback_histogram_tests {
    use super::*;

    // These inputs mirror the rendered `#[error(...)]` text of clean-kernel's
    // EnvError (env/types.rs) and TypeError (tc/type_error.rs). If a kernel
    // message is reworded, the matching case here breaks — that is the intended
    // coupling: the classifier degrades to `Other` (visible, never silently
    // wrong) and this test catches the drift so the substrings can be re-synced.
    #[test]
    fn test_classify_fallback_message_buckets_each_cause() {
        use FallbackClass::*;
        let cases = [
            // TypeError, wrapped by EnvError::TypeCheckFailed ("... : {source}").
            ("Type check error in declaration Foo.bar: (deterministic) heartbeat limit exceeded, current limit: 200000 (use `set_option maxHeartbeats <num>` to increase)", Heartbeat),
            ("Type check error in declaration Foo.bar: excessive memory consumption detected", Heartbeat),
            ("Type check error in declaration Foo.bar: deep recursion detected during type checking", Heartbeat),
            ("Type check error in declaration Foo.bar: Type mismatch: expected A, got B (heads: a vs b)", TypeMismatch),
            ("Type check error in declaration Foo.bar: Unknown constant: Nat.missing", UnknownConst),
            ("Type check error in declaration Foo.bar: Level count mismatch for Foo: declared 1 level params, got 2", LevelMismatch),
            // EnvError direct variants.
            ("Unknown inductive: Foo", UnknownConst),
            ("init requires declaration Bar", UnknownConst),
            ("Undefined universe level parameter 'u' in declaration Foo", LevelMismatch),
            ("Theorem Foo: type must be a Prop, but inferred sort is Sort 1", TypeMismatch),
            ("Inductive type error: positivity violated", Inductive),
            ("Not a structure (expected exactly one constructor): Foo", Inductive),
            ("Inductive type Foo: codomain is not a Sort after stripping 2 params", Inductive),
            ("Declaration Foo contains free variables", Malformed),
            ("Declaration Foo contains metavariables", Malformed),
            ("Unknown free variable: ?x.3", Malformed),
            ("Unbound variable index: 7", Malformed),
            // All four projection variants are structural -> Inductive.
            ("Invalid projection: index 5 out of bounds for structure with 3 fields", Inductive),
            ("Invalid projection: Prop-typed structure cannot project non-Prop field at index 0", Inductive),
            ("Invalid projection: struct type has 2 type arguments, expected 1 (1 params + 0 indices)", Inductive),
            // A recoverable depth give-up belongs with the resource/Heartbeat family.
            ("Sort inference exceeded maximum Pi-nesting depth (256)", Heartbeat),
            ("Duplicate declaration: Foo", Other),
            ("MASQUERADE proof for Foo: lint findings", Other),
            ("something the classifier has never seen", Other),
        ];
        for (msg, expected) in cases {
            assert_eq!(
                classify_fallback_message(msg),
                expected,
                "misclassified: {msg}"
            );
        }
    }

    #[test]
    fn test_unknown_inductive_outranks_inductive_bucket() {
        // "Unknown inductive" is a missing-dependency (UnknownConst), not a
        // structural inductive error — the unknown-* checks must run first.
        assert_eq!(
            classify_fallback_message("Unknown inductive type: Foo"),
            FallbackClass::UnknownConst
        );
    }

    #[test]
    fn test_histogram_from_messages_aggregates_and_sums() {
        let msgs = [
            "Type check error in declaration A: (deterministic) heartbeat limit exceeded, current limit: 1",
            "Type check error in declaration B: (deterministic) heartbeat limit exceeded, current limit: 1",
            "Type check error in declaration C: Unknown constant: X",
            "Declaration D contains free variables",
            "totally unrecognized",
        ];
        let h = AxiomFallbackHistogram::from_messages(msgs.iter().copied());
        assert_eq!(h.heartbeat, 2);
        assert_eq!(h.unknown_const, 1);
        assert_eq!(h.malformed, 1);
        assert_eq!(h.other, 1);
        assert_eq!(h.type_mismatch, 0);
        let total = h.heartbeat
            + h.type_mismatch
            + h.unknown_const
            + h.level_mismatch
            + h.inductive
            + h.malformed
            + h.other;
        assert_eq!(total, msgs.len(), "histogram must sum to input count");
    }

    #[test]
    fn test_classify_failure_message_buckets_each_cause() {
        use FailedClass::*;
        let cases = [
            // Inductive fail-closed: the verify-core skeleton message (mod.rs:992).
            (
                "inductive-family skeleton requires checked add_inductive replay; missing or incompatible metadata remains: Foo.rec",
                InductiveFailClosed,
            ),
            (
                "inductive-family skeleton requires KernelVerified confidence, got Heuristic",
                InductiveFailClosed,
            ),
            // A kernel-side structural inductive error still buckets as inductive.
            ("Inductive type error: positivity violated", InductiveFailClosed),
            // Dependency cycle — the literal pushed at mod.rs:1218/:1384.
            ("dependency cycle", DependencyCycle),
            // Reconstruction coverage gap (shard_reconstruct.rs).
            ("value beyond reconstructable prefix at expr index 42", ReconstructFailed),
            ("seed reconstruct failed: unsupported expression tag 99", ReconstructFailed),
            ("expr index out of bounds: 7 >= 5", ReconstructFailed),
            // Kernel TypeMismatch on the type itself (the defeq completeness gap).
            (
                "Type check error in declaration Foo.bar: Type mismatch: expected A, got B",
                KernelTypeMismatch,
            ),
            ("Theorem Foo: type must be a Prop, but inferred sort is Sort 1", KernelTypeMismatch),
            // Missing dependency / level / heartbeat reuse the fallback split.
            ("Unknown constant: Nat.missing", UnknownConst),
            ("Undefined universe level parameter 'u' in declaration Foo", LevelMismatch),
            (
                "Type check error in declaration Foo: (deterministic) heartbeat limit exceeded, current limit: 1",
                Heartbeat,
            ),
            ("Declaration Foo contains free variables", Other),
            ("something the classifier has never seen", Other),
        ];
        for (msg, expected) in cases {
            assert_eq!(
                classify_failure_message(msg),
                expected,
                "misclassified: {msg}"
            );
        }
    }

    #[test]
    fn test_failed_histogram_from_messages_aggregates_and_sums() {
        let msgs = [
            "inductive-family skeleton requires checked add_inductive replay; missing or incompatible metadata remains: A.rec",
            "inductive-family skeleton requires axiom-free metadata, got axiom_profile=0x1",
            "dependency cycle",
            "value beyond reconstructable prefix at expr index 9",
            "Type check error in declaration C: Type mismatch: expected X, got Y",
            "Unknown constant: Z",
            "totally unrecognized failure",
        ];
        let h = FailedHistogram::from_messages(msgs.iter().copied());
        assert_eq!(h.inductive_fail_closed, 2);
        assert_eq!(h.dependency_cycle, 1);
        assert_eq!(h.reconstruct_failed, 1);
        assert_eq!(h.kernel_type_mismatch, 1);
        assert_eq!(h.unknown_const, 1);
        assert_eq!(h.other, 1);
        let total = h.inductive_fail_closed
            + h.reconstruct_failed
            + h.dependency_cycle
            + h.kernel_type_mismatch
            + h.unknown_const
            + h.level_mismatch
            + h.heartbeat
            + h.other;
        assert_eq!(
            total,
            msgs.len(),
            "failed histogram must sum to input count"
        );
    }
}

#[cfg(test)]
mod manifest_packaging_tests {
    use super::*;
    use crate::shard::ShardWriter;
    use crate::types::{
        AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader,
        SourceSystem, NO_VALUE,
    };
    use clean_kernel::flat::{FlatExpr, FlatLevel};

    fn write_one_constant_shard(path: &Path, name: &str) {
        let mut w = ShardWriter::new();
        let l0 = w.add_level(FlatLevel::zero());
        let e0 = w.add_expr(FlatExpr::sort(l0));
        let s = w.add_string(name);
        w.add_constant(MathverseConstantHeader {
            name_idx: s,
            type_idx: e0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Axiom as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
        w.write_to_file(path).unwrap();
    }

    // CHANGE #3: stamp-verified emits a MathverseManifest over its flat shards so
    // the output dir is loadable via load_built_library / MATHVERSE_LIBRARY_PATH.
    #[test]
    fn test_stamp_verified_flat_output_loads_via_manifest() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path();
        write_one_constant_shard(&out.join("Alpha.mathverse"), "Alpha");
        write_one_constant_shard(&out.join("Beta.mathverse"), "Beta");

        let manifest_path = write_flat_manifest(out).expect("manifest emission");
        assert!(manifest_path.exists(), "manifest.json must be written");

        // Manifest shape: 2 base shards, FLAT (no `base/` prefix), no delta.
        let manifest = MathverseManifest::from_file(&manifest_path).expect("parse manifest");
        assert_eq!(manifest.base_shards.len(), 2);
        assert!(manifest.delta_shards.is_empty());
        for entry in &manifest.base_shards {
            assert!(
                !entry.path.contains('/'),
                "flat layout expected, got nested path: {}",
                entry.path
            );
            // content_hash must match the on-disk bytes (guards the release stamp
            // gate / verify_manifest_integrity).
            let bytes = std::fs::read(out.join(&entry.path)).unwrap();
            assert_eq!(
                entry.content_hash,
                blake3::hash(&bytes).to_hex().to_string(),
                "content_hash must match shard bytes"
            );
        }

        // KEY: the directory now loads through the same loader MATHVERSE_LIBRARY_PATH
        // uses — previously this failed because no manifest.json existed.
        let lib = crate::build_library::load_built_library(out).expect("flat library must load");
        assert_eq!(
            lib.constant_count(),
            2,
            "both constants must resolve through the manifest"
        );

        // Backward-compat: the non-recursive flat shard enumeration is undisturbed
        // (manifest.json is JSON, not a .mathverse file).
        assert_eq!(crate::shard_verify::discover_mathverse_files(out).len(), 2);
    }

    // Top-level-only indexing: a shard in a SUBDIR is NOT swept into the flat
    // manifest, so load_built_library and the non-recursive cli::dispatch loader
    // resolve the identical (flat) set and cannot diverge.
    #[test]
    fn test_write_flat_manifest_indexes_top_level_only() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path();
        write_one_constant_shard(&out.join("Top.mathverse"), "Top");
        std::fs::create_dir_all(out.join("nested")).unwrap();
        write_one_constant_shard(&out.join("nested").join("Deep.mathverse"), "Deep");

        let manifest_path = write_flat_manifest(out).expect("manifest emission");
        let manifest = MathverseManifest::from_file(&manifest_path).expect("parse manifest");
        assert_eq!(
            manifest.base_shards.len(),
            1,
            "only the top-level shard is indexed"
        );
        assert_eq!(manifest.base_shards[0].path, "Top.mathverse");
    }

    // Refuse to clobber a pre-existing delta-bearing (real built) manifest.
    #[test]
    fn test_write_flat_manifest_refuses_to_clobber_delta_library() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path();
        write_one_constant_shard(&out.join("Alpha.mathverse"), "Alpha");

        // Seed a delta-bearing manifest as if this were an existing built library.
        let mut existing = MathverseManifest::new();
        existing.delta_shards.push(ShardEntry {
            path: "delta/prior.mathverse".to_owned(),
            content_hash: "deadbeef".to_owned(),
            constant_count: 1,
            expr_count: 1,
            source: "prior".to_owned(),
        });
        existing.save(&out.join("manifest.json")).unwrap();

        let err = write_flat_manifest(out).expect_err("must refuse to clobber delta manifest");
        assert!(
            matches!(err, MathverseCliError::StampManifestClobber(_)),
            "expected StampManifestClobber, got: {err}"
        );
    }
}

// Closure-serve auto-discovery precedence tests live in a sibling file (pulled
// in via `#[path]`) so this already-large dispatch module is not inflated past
// its current size. `super::*` resolves to this module's private items
// (`decide_closure_serve`, `ClosureServe`, `ClosureServeInputs`).
#[cfg(test)]
#[path = "stamp_verified_closure_serve_tests.rs"]
mod closure_serve_tests;

#[cfg(test)]
mod no_value_class_tests {
    use super::*;

    /// The value-less shard-row fallback (opaque/meta gadgets elided at
    /// olean→shard conversion) must classify into its own `no_value` bucket —
    /// previously it was a bare counter increment with no name, making
    /// `axiom_fallback` disagree with the faildump/histogram (25 vs 13 on
    /// Mathlib/Data) and read as a masked verification gap.
    #[test]
    fn test_classifier_no_value_shard_row_gets_own_bucket() {
        let msg = "no value in shard for Opaque row (opaque/meta value \
                   elided at olean->shard conversion; stamped Axiomatized)";
        assert!(matches!(
            classify_fallback_message(msg),
            FallbackClass::NoValue
        ));
        let h = AxiomFallbackHistogram::from_messages([msg].into_iter());
        assert_eq!(h.no_value, 1);
        assert_eq!(h.type_mismatch, 0);
        assert_eq!(h.other, 0, "must not leak into `other`");
    }
}
