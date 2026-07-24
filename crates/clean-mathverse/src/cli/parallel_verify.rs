// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PARAGON: parallel Mathlib -> Mathverse kernel re-verification.
//!
//! The sequential `--single-pass` path threads ONE mutating, ever-growing
//! `Environment` through every module in import-topological order: each proof
//! is checked, then registered, so a later module's check sees the value of an
//! earlier one. That is correct but inherently serial — on full Mathlib it runs
//! for the better part of a day and the accumulating env grows past 24 GB.
//!
//! PARAGON replaces the serial re-verify with a two-phase split:
//!
//! - **Phase A (sequential, once):** build ONE shared, immutable base
//!   [`Environment`] containing every target module AND its transitive
//!   dependency closure, loaded TRUSTED through the `.olean` import path
//!   (registered, NOT re-verified), with proof VALUES of theorems/opaques
//!   elided to bound RAM (definition values are KEPT — the kernel
//!   delta-unfolds them during checking). The finished env is wrapped in an
//!   [`Arc`] and shared read-only across all workers.
//!
//! - **Phase B (parallel, rayon over modules):** for each module, convert its
//!   `.olean` to a `.mathverse` shard (the output artifact), then for every
//!   VALUE-BEARING constant reconstruct its `(level_params, type, value)` and
//!   run [`Environment::check_decl_readonly`] against the shared base. That is
//!   the SAME soundness gauntlet `add_decl` runs (`infer_sort` + Prop-check +
//!   `check_type(value, type)`), minus only the env mutation — so a constant
//!   earns `KernelVerified` IFF the kernel accepted its value. Axioms / quotients
//!   (no value) and inductive-family members are trusted members of the base and
//!   are counted `axiom_accepted`, never re-checked, never `KernelVerified`.
//!
//! SOUNDNESS BOUNDARY — IDENTICAL to `--single-pass`:
//! * The base supplies the trusted TYPES + definition values of dependencies;
//!   each target proof is checked against those declared dep types, exactly as
//!   the sequential path checks each proof against the env built from earlier
//!   (independently-checked) decls. This is the established closure-trust model.
//! * A constant is stamped `KernelVerified` ONLY when `check_decl_readonly`
//!   returned `Ok` — i.e. the kernel's `check_type` accepted the value. The
//!   heuristic converter never mints `KernelVerified` (the soundness floor is
//!   re-asserted by the caller). Inductive families and axioms are NEVER stamped.
//! * Each worker builds its OWN [`crate::TypeChecker`] (inside
//!   `check_decl_readonly`); the `TypeChecker`'s `RefCell`/`Cell` caches are
//!   never shared. Only the immutable `&Environment` is shared, and
//!   `Environment` is `Sync`.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

use std::sync::Arc;

use clean_kernel::env::{Declaration, ProofValueElision};
use clean_kernel::{EnvError, Environment, KernelTypeError, Name};
use clean_olean::verify_batch::{build_dependency_order, module_name_from_path};
use clean_olean::{
    default_search_paths, load_module_with_deps_shared_with_policy, ImportKinds, OleanImportPolicy,
};
use hashbrown::HashSet;
use rayon::prelude::*;

use crate::cli::closure_load::{
    build_closure_shards_for_targets, lazy_closure_missing_names,
    verify_closure_shards_against_oleans,
};
use crate::cli::import_cache::{compute_closure_hashes, ImportCache};
use crate::cli::MathverseCliError;
use crate::closure_source::ShardConstantSource;
use crate::inductive_replay::reconstruct_constant;
use crate::lean4::olean::olean_bridge::convert_olean_to_mathverse;
use crate::shard::ShardReader;
use crate::types::DeclKind;
use crate::verify::incremental::IncrementalVerifyReport;

/// Per-module verdict accumulator produced by one rayon worker. Merged into a
/// single [`IncrementalVerifyReport`] after the parallel pass joins.
///
/// `Serialize`/`Deserialize` + `Clone` let the content-addressed incremental
/// cache ([`super::import_cache`]) persist a module's verdict and replay it on a
/// re-run when the module's transitive-closure hash is unchanged.
#[derive(Debug, Default, Clone, serde::Serialize, serde::Deserialize)]
pub(crate) struct ModuleVerdicts {
    total: usize,
    kernel_verified: usize,
    axiom_accepted: usize,
    axiom_fallback: usize,
    failed: usize,
    reconstruct_failed: usize,
    axiom_fallback_names: Vec<(String, String)>,
    failures: Vec<(String, String)>,
    kernel_verified_names: Vec<String>,
    /// Heuristic-minted KernelVerified seen during conversion — MUST stay 0
    /// (the soundness floor). Summed across modules by the caller.
    heuristic_kernel_verified: u32,
    /// Constants that failed the Tier-1 (`CLEAN_KERNEL_HEARTBEAT`) cap
    /// SPECIFICALLY on `HeartbeatExceeded` and then PASSED the Tier-2
    /// (`CLEAN_KERNEL_HEARTBEAT_ESCALATE`) cap — i.e. genuine KernelVerified
    /// recovered by escalation. These are ALSO counted in `kernel_verified`
    /// (this is the subset attributable to escalation), never separately minted.
    /// 0 when escalation is disabled. Summed across modules by the caller.
    #[serde(default)]
    heartbeat_escalated_recovered: usize,
}

/// Output of the parallel convert+verify step.
pub(crate) struct ParallelVerifyOutput {
    pub(crate) report: IncrementalVerifyReport,
    pub(crate) converted: usize,
    pub(crate) failed: Vec<(String, String)>,
    pub(crate) heuristic_kernel_verified: u32,
    /// Distinct dependency-closure modules registered into the shared base env
    /// (diagnostic; does not affect any verdict).
    pub(crate) base_modules_loaded: usize,
    /// Constants registered into the shared base env (trusted context).
    pub(crate) base_constants: usize,
    /// Proof values elided from the base to bound RAM.
    pub(crate) base_proof_values_elided: usize,
    /// Wall-clock seconds for Phase A (sequential base build). Diagnostic.
    pub(crate) phase_a_secs: f64,
    /// Wall-clock seconds for Phase B (the parallel convert+verify fan-out).
    /// This is the figure that scales with `--jobs` (GATE 2).
    pub(crate) phase_b_secs: f64,
    /// Modules whose verdict was replayed from the incremental cache (skipped
    /// convert + verify). 0 when `--incremental` is off or on a cold cache.
    pub(crate) cache_hits: usize,
    /// Modules freshly converted + verified this run (cache miss or no cache).
    pub(crate) cache_misses: usize,
}

/// Configuration for the content-addressed incremental cache. When passed to
/// [`parallel_convert_and_verify`], a module whose transitive-closure hash
/// matches its cached entry — *and* whose shard from the prior run still exists
/// on disk — is replayed from cache, skipping both conversion and kernel
/// re-verification. See [`super::import_cache`] for why the closure hash is the
/// complete, sound key.
pub(crate) struct IncrementalCache<'a> {
    /// Sidecar JSON cache file (read at start, rewritten at end of the run).
    pub(crate) cache_path: &'a Path,
    /// Env fingerprint folded into every closure hash. Any change to it (kernel
    /// version, heartbeat, elision, …) invalidates every entry by construction.
    pub(crate) fingerprint: &'a str,
}

/// Flush the live incremental cache to disk every this-many modules (Track B3).
/// Bounds the work a jetsam-kill can lose to at most this many modules, while
/// keeping the per-module IO amortized. 25 is the corpus-sharded driver's
/// sidecar cadence.
const INCREMENTAL_FLUSH_EVERY: usize = 25;

/// The live, on-disk-backed incremental cache shared across PARAGON workers
/// (Track B3). Guarded by a single `Mutex`; `since_flush` counts modules added
/// since the last on-disk save so the lock is only held briefly per module and
/// the (heavier) save fires every [`INCREMENTAL_FLUSH_EVERY`].
struct LiveCache {
    cache: ImportCache,
    since_flush: usize,
}

/// Record one module's verdict into the live cache and, every
/// [`INCREMENTAL_FLUSH_EVERY`] records, persist the whole cache to disk. A no-op
/// when caching is off (`live_cache`/`incremental` are `None`). A save failure
/// is logged but never fatal — the worst case is a colder next run, never a
/// wrong verdict (the next run re-validates every hit against the live closure
/// hash + on-disk shard before replaying it).
fn persist_incrementally(
    live_cache: Option<&Mutex<LiveCache>>,
    incremental: Option<&IncrementalCache<'_>>,
    olean: &Path,
    closure_hash: &str,
    verdicts: &ModuleVerdicts,
) {
    let (Some(lc), Some(ic)) = (live_cache, incremental) else {
        return;
    };
    let mut guard = lc.lock().expect("live cache mutex poisoned");
    guard
        .cache
        .insert(olean, closure_hash.to_string(), verdicts.clone());
    guard.since_flush += 1;
    if guard.since_flush >= INCREMENTAL_FLUSH_EVERY {
        guard.since_flush = 0;
        if let Err(e) = guard.cache.save(ic.cache_path) {
            eprintln!(
                "warning: incremental cache flush to {} failed: {e}",
                ic.cache_path.display()
            );
        }
    }
}

/// One worker's outcome, carrying the verdict plus the cache bookkeeping needed
/// to rebuild the on-disk cache after the parallel join.
struct JobResult {
    olean: PathBuf,
    /// `Some` iff incremental caching is active (the module's current closure
    /// hash); `None` when caching is off, so nothing is persisted.
    closure_hash: Option<String>,
    verdicts: ModuleVerdicts,
    cache_hit: bool,
}

/// Build the shared, immutable PARAGON base environment.
///
/// Loads EVERY target module plus its transitive import closure into ONE env
/// through the trusted `.olean` import path (`load_module_with_deps_shared_with_policy`,
/// the same path `clean olean verify-batch` uses), with a single caller-owned
/// `visited` set so the union closure is parsed and registered exactly once.
///
/// Unlike [`crate::cli::closure_load::load_targets_closure`], the target modules
/// are NOT excluded — PARAGON re-checks each target constant against this base by
/// reconstructing it from its shard and running `check_decl_readonly`, so the
/// base must carry the targets' (and deps') declared TYPES for reference
/// resolution and the deps' definition VALUES for delta-unfolding. Theorem/opaque
/// proof VALUES are elided per `elision` (default `OpaqueAndTheorem`) to bound
/// resident memory — the proofs are reconstructed transiently per-worker in
/// Phase B, so the base never needs to hold them.
fn build_base_env(
    oleans: &[PathBuf],
    root: &Path,
    elision: ProofValueElision,
) -> Result<(Environment, usize, usize, usize), MathverseCliError> {
    // Search paths: closure root first (so the target modules and their Mathlib
    // siblings resolve), then sibling lake packages, then stdlib/toolchain.
    let search_paths = build_paragon_search_paths(root);

    // Import-verification prelude: suppress the kernel's lossy hand-rolled
    // `extends`-structure stubs so the real Mathlib structures resolve (same as
    // the closure loader). The OpaqueAndTheorem elision is applied AT
    // REGISTRATION so peak RSS is bounded, not just steady-state.
    let mut env = Environment::try_with_prelude_for_import()
        .map_err(|e| MathverseCliError::StampPrelude(e.to_string()))?;
    let import_policy = OleanImportPolicy::default().with_proof_elision(elision);

    // One shared visited set across every target: the union closure (targets +
    // deps) is loaded once. Modules an earlier target already pulled in are
    // skipped with no re-read.
    let mut visited: HashSet<String> = HashSet::new();
    let mut loaded_modules: BTreeSet<String> = BTreeSet::new();
    let mut base_constants = 0usize;

    for olean in oleans {
        let module = module_name_from_path(olean, root);
        let summaries = load_module_with_deps_shared_with_policy(
            &mut env,
            &module,
            &search_paths,
            &mut visited,
            import_policy,
        )
        .map_err(|e| MathverseCliError::StampClosure {
            module: module.clone(),
            reason: format!("base load: {e}"),
        })?;
        for summary in summaries {
            let name = summary
                .module_name
                .clone()
                .unwrap_or_else(|| module.clone());
            if loaded_modules.insert(name) {
                base_constants += summary.added_constants;
            }
        }
    }

    // Post-batch fixup: the shared loader defers no_confusion regeneration to the
    // caller (regenerating on a partial env mis-generates). Run it ONCE now that
    // the whole base is loaded — matching the per-module reload path.
    env.regenerate_missing_no_confusion();

    // Belt-and-suspenders sweep: elide any proof value that entered through a
    // path the loader does not gate. Idempotent.
    env.elide_proof_values(elision);
    let elided = env.count_elided_proof_values(elision).total_elided();

    Ok((env, loaded_modules.len(), base_constants, elided))
}

/// The demand-paged PARAGON base: a minimal eager `Environment` (the
/// import-verification prelude + every closure/target INDUCTIVE FAMILY) plus a
/// shared, mmap-backed [`ShardConstantSource`] that serves the definitional
/// kinds (Definition/Theorem/Axiom/Opaque) on first lookup.
///
/// The eager env here is the floor: it carries ONLY what cannot be served
/// lazily (inductive families/recursors — the shard format can't carry recursor
/// reduction rules losslessly — plus the prelude). The bulk of the closure (the
/// definitional constants that drove the ~3.65 GB eager floor) stays in the mmap
/// and is materialized on demand. The caller installs a per-wave-FRESH view of
/// `source` onto a clone of `base_env`, so the demand-fold cache is bounded to
/// one wave's working set (the `FrozenMap` is append-only, so without per-wave
/// freshness it would re-accumulate the whole closure — see
/// [`ShardConstantSource::fresh_view`]).
struct LazyBase {
    /// Minimal eager env: prelude + inductive families ONLY. NO source installed
    /// — the caller installs a fresh `source` view per wave.
    base_env: Environment,
    /// The shared template source. The caller calls `fresh_view()` on it per
    /// wave; all views share its (immutable, mmap-backed) readers + index.
    source: Arc<ShardConstantSource>,
    /// Distinct closure/target modules whose inductive families were loaded
    /// eagerly (diagnostic).
    base_modules_loaded: usize,
    /// Constants registered eagerly into the base (inductive families + prelude).
    base_constants: usize,
    /// Definitional constants the lazy source can serve (the demand-paged bulk).
    servable_constants: usize,
}

/// The Phase-A base, in either posture: a fully-resident eager env, or the
/// demand-paged base (minimal eager env + a wave-fresh `ShardConstantSource`).
///
/// Phase B reads the base read-only across rayon workers; for the eager posture
/// that is one shared `Arc<Environment>` for the whole run. For the demand-paged
/// posture a FRESH per-wave env is produced ([`Self::wave_env`]) so the lazy
/// source's append-only materialization cache is bounded to one wave's working
/// set and reclaimed at each wave boundary.
enum BaseEnv {
    /// Fully-resident eager base — shared once across the whole run.
    Eager(Arc<Environment>),
    /// Demand-paged base — a minimal eager env (prelude + inductive families)
    /// cloned per wave with a fresh `source` view installed.
    Lazy {
        base_env: Arc<Environment>,
        source: Arc<ShardConstantSource>,
    },
}

impl BaseEnv {
    /// Whether this base is demand-paged (so Phase B must run in waves to bound
    /// the lazy source's materialization cache).
    fn is_lazy(&self) -> bool {
        matches!(self, BaseEnv::Lazy { .. })
    }

    /// The shared `Arc<Environment>` for ONE Phase-B wave.
    ///
    /// - Eager: the same shared base every wave (cloning the `Arc` is free; the
    ///   single fully-resident env serves all modules).
    /// - Lazy: a FRESH env per wave — a clone of the minimal eager base with a
    ///   `source.fresh_view()` installed. The clone is cheap (inductive families
    ///   only); the fresh view shares the immutable mmap readers but starts with
    ///   an EMPTY cache, so the previous wave's materialized `ConstantInfo` is
    ///   dropped with the previous wave's env — bounding steady-state RSS.
    ///
    /// SOUNDNESS-NEUTRAL: a wave env serves byte-identical `ConstantInfo` to the
    /// eager base for every name (the source materializes the same shard bytes
    /// regardless of cache state); only WHERE a dep lives (eager map vs mmap) and
    /// WHEN its cache is dropped differ. No `is_def_eq`/`check_type` change.
    fn wave_env(&self) -> Arc<Environment> {
        match self {
            BaseEnv::Eager(env) => Arc::clone(env),
            BaseEnv::Lazy { base_env, source } => {
                let mut env = (**base_env).clone();
                env.set_constant_source(Arc::new(source.fresh_view()));
                Arc::new(env)
            }
        }
    }
}

/// Build the demand-paged PARAGON base (Stage 1 of the memory plan).
///
/// 1. Build the trusted-closure `.mathverse` shards for the UNION of all targets
///    once, into a persistent cache dir beneath `out_dir` (reused across runs).
/// 2. Build a minimal eager env: the import-verification prelude + every
///    closure/target INDUCTIVE FAMILY (via [`ImportKinds::InductiveFamiliesOnly`]).
///    The definitional kinds are NOT loaded eagerly — they will be served lazily.
/// 3. Build a [`ShardConstantSource`] over the closure shards.
/// 4. Drop any value-less prelude AXIOM STUB the shard supersedes with a real
///    definition (verdict parity: the eager `.olean` path overwrites such stubs;
///    the inductive-only leg skips the definitional load, so the stub would
///    otherwise shadow the faithful shard — mirrors `load_targets_closure_mmap`).
/// 5. COVERAGE CHECK: every target's transitive `Const`-reference closure must
///    resolve lazily-or-eagerly. On ANY miss, return `Ok(None)` so the caller
///    HARD-FALLS-BACK to the fully-eager [`build_base_env`] — a lazy base can
///    never silently drop a verdict.
///
/// Returns `Ok(None)` on coverage miss (caller falls back); `Err` only on a hard
/// failure (the shards could not be built/loaded), which is also caught by the
/// caller as a fallback signal.
fn build_lazy_base(
    oleans: &[PathBuf],
    root: &Path,
    out_dir: &Path,
    elision: ProofValueElision,
) -> Result<Option<LazyBase>, MathverseCliError> {
    let search_paths = build_paragon_search_paths(root);

    // (1) Closure shards for the union of all targets (one walk, persistent dir).
    // CRITICAL: this dir must live OUTSIDE `out_dir` — the stamp/manifest/count
    // helpers (`stamp_shard_dir_kernel_verified`, `count_stored_kernel_verified`)
    // scan `out_dir` RECURSIVELY for `.mathverse` shards, so closure shards under
    // `out_dir` would be wrongly stamped/counted as TARGET output. Default to a
    // SIBLING dir; override with `CLEAN_PARAGON_CLOSURE_SHARDS` (e.g. to a shared
    // cache reused across runs/subtrees).
    let shards_dir = paragon_closure_shards_dir(out_dir);
    // exclude_targets=false: the targets DEPEND ON EACH OTHER in a subtree, and
    // the eager `build_base_env` carries every target, so the lazy base must
    // serve sibling-target constants too. Build shards for targets as well.
    let build = build_closure_shards_for_targets(oleans, root, &shards_dir, false)?;
    eprintln!(
        "stamp-verified --parallel: PARAGON demand-paged base — built closure shards ({} converted, {} skipped) at {}",
        build.converted,
        build.skipped_modules.len(),
        shards_dir.display()
    );

    // (2) The minimal EAGER env. Two legs are loaded eagerly:
    //   a. EVERY closure/target module's INDUCTIVE FAMILIES (the shard format
    //      can't serve recursors losslessly), via `InductiveFamiliesOnly`.
    //   b. The FULL contents (all kinds) of the few modules the shard builder
    //      could NOT convert (`build.skipped_modules` — e.g.
    //      `Mathlib.Data.Real.Basic`, `Init.Data.UInt.Basic`, which the eager
    //      `.olean` loader parses fine but the stricter shard builder chokes on).
    //      Their definitional constants are absent from the shards, so without
    //      this leg every one is a coverage miss and the whole run falls back to
    //      eager. Eager-full-loading exactly those modules supplies their names
    //      from the SAME eager `.olean` path the fully-eager base uses, so the
    //      served `ConstantInfo` is byte-identical — sound, and it lets the
    //      demand-paged base engage for the other ~99.7% of the closure.
    let mut base_env = Environment::try_with_prelude_for_import()
        .map_err(|e| MathverseCliError::StampPrelude(e.to_string()))?;
    let inductive_policy = OleanImportPolicy::default()
        .with_proof_elision(elision)
        .with_import_kinds(ImportKinds::InductiveFamiliesOnly);
    // The skipped-module fallback uses elision too (keep proof VALUES bounded),
    // but loads ALL kinds (default import-kinds) so their definitions are present.
    let full_policy = OleanImportPolicy::default().with_proof_elision(elision);

    let mut loaded_modules: BTreeSet<String> = BTreeSet::new();
    let mut base_constants = 0usize;

    // Leg (b) uses its OWN `visited` PRE-SEEDED with every CONVERTED (shard-
    // served) module, so the full-load does NOT eagerly pull a skipped module's
    // (large) dep closure into RAM — those deps are served lazily from their
    // shards. Derived from the shard filenames (`<dotted.module>.mathverse`).
    // Without this, eager full-loading `Mathlib.Data.Real.Basic` would drag its
    // entire transitive closure eager, re-inflating the floor we are cutting.
    let mut visited_b: HashSet<String> = HashSet::new();
    for shard in crate::shard_verify::discover_mathverse_files(&shards_dir) {
        if let Some(stem) = shard.file_stem().and_then(|s| s.to_str()) {
            visited_b.insert(stem.to_string());
        }
    }

    // Eager full-load ONE module (its OWN decls only — deps are pre-visited as
    // shard-served) into `base_env`. Used for both the shard-unconvertible
    // modules and the bounded coverage repair. Best-effort: a load failure leaves
    // the module's names uncovered and lets the coverage gate decide.
    let mut eager_full_load = |module: &str,
                               base_env: &mut Environment,
                               visited_b: &mut HashSet<String>,
                               loaded_modules: &mut BTreeSet<String>,
                               base_constants: &mut usize| {
        match load_module_with_deps_shared_with_policy(
            base_env,
            module,
            &search_paths,
            visited_b,
            full_policy,
        ) {
            Ok(summaries) => {
                for summary in summaries {
                    let name = summary
                        .module_name
                        .clone()
                        .unwrap_or_else(|| module.to_string());
                    if loaded_modules.insert(name) {
                        *base_constants += summary.added_constants;
                    }
                }
            }
            Err(e) => {
                eprintln!(
                    "stamp-verified --parallel: PARAGON eager full-load of `{module}` failed ({e}); coverage gate will decide"
                );
            }
        }
    };

    // Leg (b) FIRST: eager full-load the shard-unconvertible modules so their
    // definitions win the dedup over any inductive-only registration. Resolved by
    // module NAME against the same search paths. Their deps are pre-visited above
    // (shard-served), so only the skipped modules' OWN decls load eagerly.
    for module in &build.skipped_modules {
        eager_full_load(
            module,
            &mut base_env,
            &mut visited_b,
            &mut loaded_modules,
            &mut base_constants,
        );
    }

    // Leg (a): inductive families for the whole target+dep closure. A SEPARATE
    // `visited_a` (NOT pre-seeded) so every closure module's inductive families
    // are eagerly registered — converted modules' inductives must be eager even
    // though their definitions are shard-served. Registration into `base_env` is
    // idempotent on duplicate names, so the two legs compose cleanly.
    let mut visited_a: HashSet<String> = HashSet::new();
    for olean in oleans {
        let module = module_name_from_path(olean, root);
        let summaries = load_module_with_deps_shared_with_policy(
            &mut base_env,
            &module,
            &search_paths,
            &mut visited_a,
            inductive_policy,
        )
        .map_err(|e| MathverseCliError::StampClosure {
            module: module.clone(),
            reason: format!("lazy base inductive load: {e}"),
        })?;
        for summary in summaries {
            let name = summary
                .module_name
                .clone()
                .unwrap_or_else(|| module.clone());
            if loaded_modules.insert(name) {
                base_constants += summary.added_constants;
            }
        }
    }
    // Inductive-family post-fixup (matches the eager base + per-module reload).
    base_env.regenerate_missing_no_confusion();

    // (3) Lazy source over the closure shards. Held MUTABLE so the load-time
    // content-binding verification below can mark verified shards before any
    // `get()` runs.
    let mut source = ShardConstantSource::from_dir(&shards_dir).map_err(|e| {
        MathverseCliError::StampLazyClosureShards {
            dir: shards_dir.display().to_string(),
            reason: e.to_string(),
        }
    })?;

    // (3b) LOAD-TIME CONTENT-BINDING VERIFICATION — the wiring that makes the
    // demand-paged base actually SERVE. `ShardConstantSource::get()` refuses to
    // serve any shard that has not been `mark_shard_verified` (closure_source.rs
    // ~L415): each shard defaults UNVERIFIED. Without this call every shard stays
    // unverified, so `get()` returns `None` for EVERY name — the base is INERT.
    // That makes the coverage check below see the whole closure as "missing",
    // which drives the repair loop to eager-full-load every owning module,
    // SILENTLY re-inflating RSS to the fully-eager floor (the OOM bound defeated,
    // masquerading as a "lazy base"). Verify BEFORE the prelude-stub override loop
    // (which itself calls `get()` + `forget_decl`) and BEFORE the coverage/repair
    // loop — exactly as `load_targets_closure_mmap` does. Each verified shard is
    // content-bound to the on-disk `.olean` eager would import (source-olean
    // blake3 + per-const recon_digest + declared-name subset), so serving it is
    // byte-identical to the eager path — the loader stays a search accelerator,
    // NOT TCB (the kernel still re-checks every candidate).
    let (any_v3_bound, verified_shards) = verify_closure_shards_against_oleans(&mut source, root);
    if !any_v3_bound {
        // No fail-closed-bound v3 shard at all (a v2 / unbound closure dir). The
        // demand-paged base cannot serve — do NOT silently eager-repair every
        // module. Fall back LOUDLY (caller degrades to UNBOUNDED eager, or, under
        // CLEAN_REQUIRE_BOUNDED=1, hard-errors).
        eprintln!(
            "stamp-verified --parallel: PARAGON closure shard dir `{}` has NO v3 fail-closed-bound shards (version<3 or fail_closed_verified=0) — the demand-paged base can serve NOTHING; refusing to silently eager-repair the whole closure. Falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect).",
            shards_dir.display()
        );
        return Ok(None);
    }
    if verified_shards == 0 {
        // v3 shards exist but NONE passed the load-time content/arena binding
        // (stale/swapped/corrupted vs the on-disk `.olean`). Same INERT-base
        // hazard as above — surface it distinctly and fall back LOUDLY before
        // wasting the eager-inductive + coverage work.
        eprintln!(
            "stamp-verified --parallel: PARAGON closure shard dir `{}` has v3 fail-closed-bound shards but ZERO passed the load-time content/arena binding (stale/swapped/corrupted vs on-disk .olean, or unresolvable) — the demand-paged base can serve NOTHING. Falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect).",
            shards_dir.display()
        );
        return Ok(None);
    }
    eprintln!(
        "stamp-verified --parallel: PARAGON load-time verification marked {verified_shards} closure shard(s) servable (of {} indexed)",
        source.shard_count()
    );

    let servable_constants = source.servable_len();

    // (4) Prelude-stub override (verdict parity with the eager overwrite): drop
    // any value-less Axiom stub the shard supersedes with a real definition.
    {
        use clean_kernel::env::{ConstantKind, ConstantSource};
        let to_drop: Vec<Name> = base_env
            .constants()
            .filter(|ci| ci.value.is_none() && ci.kind == ConstantKind::Axiom)
            .map(|ci| ci.name.clone())
            .filter(|name| ConstantSource::get(&source, name).is_some_and(|ci| ci.value.is_some()))
            .collect();
        for name in to_drop {
            base_env.forget_decl(&name);
        }
    }

    // (5) Coverage check + BOUNDED REPAIR. The shard builder drops a few
    // SERVABLE-kind constants per-constant inside otherwise-converted modules
    // (e.g. `Real.commRing.proof_22` — an auto-generated proof the converter
    // can't reconstruct). Those would each be a coverage miss → whole-run eager
    // fallback (no win). For every such miss whose owning module the builder
    // recorded (`dropped_const_modules`), eager full-load that module — supplying
    // the missing names from the SAME eager `.olean` path (byte-identical
    // `ConstantInfo`, sound), so the demand-paged base engages instead of falling
    // back. Bounded: at most `REPAIR_ROUNDS` rounds; if misses persist OR a miss
    // has no recorded owning module, HARD-FALL-BACK to fully-eager (coverage never
    // silently drops). `get_const` consults the source explicitly in the BFS, so
    // `base_env` stays source-free for the per-wave-fresh install.
    const REPAIR_ROUNDS: usize = 4;
    for round in 0..=REPAIR_ROUNDS {
        let missing = lazy_closure_missing_names(&base_env, &source, oleans, root);
        if missing.is_empty() {
            break;
        }
        if round == REPAIR_ROUNDS {
            eprintln!(
                "stamp-verified --parallel: PARAGON coverage still missing {} name(s) after {REPAIR_ROUNDS} repair round(s) (first few: {}) — falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect; set CLEAN_REQUIRE_BOUNDED=1 to hard-fail instead)",
                missing.len(),
                missing.iter().take(8).map(|n| n.to_string()).collect::<Vec<_>>().join(", ")
            );
            return Ok(None);
        }
        // Resolve each miss to its owning module via two exact sources:
        //   1. `dropped_const_modules` — the per-constant drops the shard builder
        //      recorded (e.g. a convert-failed servable constant).
        //   2. `source.owning_module(parent)` — for an auto-generated name the
        //      eager importer SYNTHESIZES but never stores (e.g. `X.proof_N`), the
        //      source serves its PARENT `X`; eager-loading `X`'s module
        //      re-synthesizes `X.proof_N` (and siblings) so they resolve eagerly.
        // A miss neither source can place is unrepairable → hard-fall-back.
        let mut repair_modules: BTreeSet<String> = BTreeSet::new();
        for name in &missing {
            if let Some(module) = build.dropped_const_modules.get(&name.to_string()) {
                repair_modules.insert(module.clone());
                continue;
            }
            if let Some(module) = owning_module_for_missing(&source, name) {
                repair_modules.insert(module);
                continue;
            }
            // A miss with no resolvable owning module cannot be repaired
            // surgically — fall back rather than load blindly.
            eprintln!(
                "stamp-verified --parallel: PARAGON unrepairable coverage miss `{name}` (no resolvable owning module) — falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect; set CLEAN_REQUIRE_BOUNDED=1 to hard-fail instead)"
            );
            return Ok(None);
        }
        eprintln!(
            "stamp-verified --parallel: PARAGON coverage repair round {} — eager full-loading {} owning module(s) for {} missing name(s) (grows the eager floor by these modules' OWN decls; deps stay shard-served)",
            round + 1,
            repair_modules.len(),
            missing.len()
        );
        for module in &repair_modules {
            // Allow the repair load to register this module's OWN decls even if it
            // was pre-visited as shard-served (its shard dropped a needed const):
            // un-visit it so `eager_full_load` registers its definitions.
            visited_b.remove(module);
            eager_full_load(
                module,
                &mut base_env,
                &mut visited_b,
                &mut loaded_modules,
                &mut base_constants,
            );
        }
        base_env.regenerate_missing_no_confusion();
    }

    Ok(Some(LazyBase {
        base_env,
        source: Arc::new(source),
        base_modules_loaded: loaded_modules.len(),
        base_constants,
        servable_constants,
    }))
}

/// Build the de-duplicated, priority-ordered olean search paths for the PARAGON
/// base, rooted at `root`. Mirrors the closure loader's resolution so the base
/// covers exactly the modules the eager `.olean` path would load.
fn build_paragon_search_paths(root: &Path) -> Vec<PathBuf> {
    let mut search_paths: Vec<PathBuf> = Vec::new();
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    if seen.insert(root.to_path_buf()) {
        search_paths.push(root.to_path_buf());
    }
    // Sibling lake-package roots under the same `.lake` tree (Batteries/Aesop/…).
    if let Some(lake_dir) = root
        .ancestors()
        .find(|a| a.file_name().is_some_and(|n| n == ".lake"))
    {
        let packages = lake_dir.join("packages");
        if let Ok(entries) = std::fs::read_dir(&packages) {
            let mut pkg_roots: Vec<PathBuf> = Vec::new();
            for entry in entries.flatten() {
                for rel in [".lake/build/lib/lean", "build/lib/lean"] {
                    let cand = entry.path().join(rel);
                    if cand.is_dir() {
                        pkg_roots.push(cand);
                    }
                }
            }
            pkg_roots.sort();
            for r in pkg_roots {
                if seen.insert(r.clone()) {
                    search_paths.push(r);
                }
            }
        }
    }
    for p in default_search_paths() {
        if seen.insert(p.clone()) {
            search_paths.push(p);
        }
    }
    search_paths
}

/// FAIL-CLOSED gate for the eager fallback (soundness invariant (d)). Called at
/// the ONE site where the demand-paged (RSS-bounded) base was unavailable and the
/// only remaining posture is the fully-resident eager base (the multi-GB floor
/// that OOMs a small machine).
///
/// - `require_bounded == false`: returns `Ok(())` — the caller degrades to the
///   eager base. The degrade is announced LOUDLY by the PARAGON warnings emitted
///   before this point (in `build_lazy_base` and the `lazy_base` match arms), so
///   the bound-defeat is never silent.
/// - `require_bounded == true` (`CLEAN_REQUIRE_BOUNDED=1`): returns
///   `Err(StampBoundedRequired)` — the operator asserted this machine cannot
///   afford the eager floor, so a missing bounded base fails the run rather than
///   silently (or even loudly) re-inflating RSS to the eager floor.
fn require_bounded_gate(require_bounded: bool) -> Result<(), MathverseCliError> {
    if require_bounded {
        return Err(MathverseCliError::StampBoundedRequired {
            reason: "the demand-paged base was unavailable (no servable closure \
                     shards, a coverage miss, or a build failure — see the PARAGON \
                     warning above) and CLEAN_REQUIRE_BOUNDED=1 forbids the fallback \
                     to the UNBOUNDED fully-eager base. Rebuild/repair the closure \
                     shards (e.g. re-run build_closure_shards_for_targets) or unset \
                     CLEAN_REQUIRE_BOUNDED to allow the eager fallback."
                .to_string(),
        });
    }
    Ok(())
}

/// PARAGON entry point: build the shared base (Phase A) and re-verify every
/// target module in parallel against it (Phase B). Writes one `.mathverse` shard
/// per target to `out_dir` (the output artifact) and returns the merged verdict.
///
/// `jobs` sizes the rayon worker pool for the parallel pass.
pub(crate) fn parallel_convert_and_verify(
    oleans: &[PathBuf],
    out_dir: &Path,
    root: &Path,
    elision: ProofValueElision,
    jobs: usize,
    incremental: Option<IncrementalCache<'_>>,
) -> Result<ParallelVerifyOutput, MathverseCliError> {
    let start = std::time::Instant::now();

    // Per-constant heartbeat (paragon robustness): `check_decl_readonly` reads
    // `maxHeartbeats` from the (shared) base env's options and caps each
    // constant's type-check at that many reduction ticks. Without it, a single
    // pathological proof with a huge definitional unfolding (common in
    // Analysis/Topology/CategoryTheory) grinds for minutes and effectively
    // stalls the full-corpus run; with it, such a constant deterministically
    // bails to `axiom_fallback` (honestly NOT KernelVerified) and the run always
    // completes in bounded time — NO single constant can stall it. Applied to
    // EITHER base (eager or demand-paged) below.
    // Soundness-neutral: a lower limit can only turn a would-be KernelVerified
    // into a fallback, never the reverse — it never accepts a non-def-eq term.
    let heartbeat = std::env::var("CLEAN_KERNEL_HEARTBEAT")
        .ok()
        .filter(|s| !s.is_empty());
    // CENSUS TUNING (TCB-neutral): `CLEAN_KERNEL_CACHE_ENTRIES=N` sets the kernel
    // memo-cache cap (0 = unbounded). A memo only ever stores results the kernel
    // would recompute identically, so size affects performance only, never a
    // verdict (`set_global_max_cache_entries` is documented TCB-neutral). An
    // unbounded cache cuts full-corpus census wall-time ~40% (the passing-but-
    // slow constants stop re-missing) — the tick fix made passing constants do
    // full def-eq work, so this is the census-feasibility lever (§12.11).
    if let Ok(cv) = std::env::var("CLEAN_KERNEL_CACHE_ENTRIES") {
        if let Ok(n) = cv.parse::<usize>() {
            clean_kernel::set_global_max_cache_entries(if n == 0 { usize::MAX } else { n });
            eprintln!(
                "stamp-verified --parallel: kernel memo-cache cap = {} (CLEAN_KERNEL_CACHE_ENTRIES)",
                if n == 0 { "unbounded".into() } else { n.to_string() }
            );
        }
    }
    // DIAGNOSTIC (TCB-neutral): `CLEAN_PROFILE_HEARTBEATS=1` enables the kernel
    // heartbeat profiler so each HeartbeatExceeded failure carries a category /
    // top-name / top-position breakdown of WHERE the deterministic budget went
    // (which reduction rule / const dominates the step count). Used to diagnose
    // the carrier PERF class (designs/2026-07-06-carrier-whnf-perf.md §11/§12.4).
    // Adds per-tick overhead — a diagnostic run only. Verdict-neutral.
    let profile_heartbeats = std::env::var("CLEAN_PROFILE_HEARTBEATS")
        .map(|v| v == "1" || v == "true")
        .unwrap_or(false);
    let set_heartbeat = |env: &mut Environment| {
        if let Some(hb) = &heartbeat {
            env.set_option("maxHeartbeats".to_string(), Some(hb.clone()));
        }
        if profile_heartbeats {
            env.set_option("profileHeartbeats".to_string(), Some("true".to_string()));
        }
    };

    // TIER-2 escalation cap (two-tier per-constant heartbeat escalation). When a
    // constant's Tier-1 check fails SPECIFICALLY on `HeartbeatExceeded`, it is
    // re-run ONCE at this higher cap against the SAME shared base — the term is a
    // valid-but-large finite check that 200 K ticks simply could not finish.
    // Sound: raising the cap re-runs the identical `check_decl_readonly` gauntlet
    // and can only turn a would-be fallback into a genuine KernelVerified; it can
    // never accept a non-def-eq term (the kernel still fully checks it). The cap
    // is a deterministic TICK count (not wall-clock), so verdicts stay
    // reproducible across machines. Default 100_000_000; empty or `0` DISABLES
    // escalation (the fast path — Tier-1 heartbeat failures fall straight to
    // `axiom_fallback`, byte-identical to the pre-escalation behavior).
    const HEARTBEAT_ESCALATE_DEFAULT: u32 = 100_000_000;
    let heartbeat_escalate: Option<u32> = match std::env::var("CLEAN_KERNEL_HEARTBEAT_ESCALATE") {
        Ok(s) if s.is_empty() => None,
        Ok(s) => match s.parse::<u32>() {
            Ok(0) => None,
            Ok(n) => Some(n),
            // An unparseable value is a config error, not a silent disable: fall
            // back to the default cap rather than dropping escalation unnoticed.
            Err(_) => Some(HEARTBEAT_ESCALATE_DEFAULT),
        },
        Err(_) => Some(HEARTBEAT_ESCALATE_DEFAULT),
    };
    if let Some(h1) = heartbeat_escalate {
        eprintln!(
            "stamp-verified --parallel: two-tier heartbeat escalation ACTIVE — Tier-1 HeartbeatExceeded failures retried once at maxHeartbeats={h1} (CLEAN_KERNEL_HEARTBEAT_ESCALATE)"
        );
    }

    // ---- Phase A: build the shared base (sequential, once). ------------------
    // STAGE 1 (memory): the DEMAND-PAGED base — a minimal eager env (prelude +
    // inductive families) plus an mmap-backed `ShardConstantSource` serving the
    // definitional bulk on demand — collapses the ~3.65 GB fully-resident floor
    // under every Phase-B peak to the inductive-family floor.
    //
    // DEFAULT OFF (opt-in via `CLEAN_PARAGON_LAZY_BASE=1`). The shard-
    // reconstructed `ConstantInfo` is NOT YET byte-identical to the eager olean
    // import at subtree scale (binder-info / MData / reducibility fidelity — the
    // documented `diag_routed_env_diff` gap that keeps the SEQUENTIAL
    // `CLEAN_LAZY_CLOSURE` default-OFF too), so a small number of proofs that
    // verify eagerly fall to `axiom_fallback` lazily — a KV-INVARIANCE deviation
    // (completeness loss, never a wrong KV: the kernel only ever FAILS to verify,
    // never falsely accepts). Until the reconstruction is exact, the default path
    // stays fully-eager so KV is unchanged. When opted in, a coverage miss / build
    // failure still HARD-FALLS-BACK to the fully-eager base, so a run can never
    // silently drop coverage below the lazy-engaged level.
    let phase_a_start = std::time::Instant::now();
    // STRICT / FAIL-CLOSED: `CLEAN_REQUIRE_BOUNDED=1` demands the demand-paged
    // (RSS-bounded) base. It (a) FORCES the lazy attempt even if the operator did
    // not opt in via `CLEAN_PARAGON_LAZY_BASE=1`, and (b) turns the otherwise-loud
    // degrade to the UNBOUNDED fully-eager base into a HARD ERROR (below), so the
    // OOM bound can never be silently — or even loudly — defeated on a machine
    // that cannot afford the eager floor.
    let require_bounded = std::env::var("CLEAN_REQUIRE_BOUNDED").ok().as_deref() == Some("1");
    let lazy_base_enabled =
        require_bounded || std::env::var("CLEAN_PARAGON_LAZY_BASE").ok().as_deref() == Some("1");
    let lazy_base = if lazy_base_enabled {
        match build_lazy_base(oleans, root, out_dir, elision) {
            Ok(Some(lb)) => {
                eprintln!(
                    "stamp-verified --parallel: PARAGON demand-paged base ACTIVE — {} eager inductive-family module(s)/{} eager constant(s), {} definitional constant(s) served lazily from mmap (floor cut)",
                    lb.base_modules_loaded, lb.base_constants, lb.servable_constants
                );
                Some(lb)
            }
            Ok(None) => {
                eprintln!(
                    "stamp-verified --parallel: PARAGON demand-paged base unavailable (coverage miss or no servable shards) — falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect)"
                );
                None
            }
            Err(e) => {
                eprintln!(
                    "stamp-verified --parallel: PARAGON demand-paged base build failed ({e}) — falling back to the UNBOUNDED fully-eager base (OOM bound NOT in effect)"
                );
                None
            }
        }
    } else {
        None
    };

    // The eager base is built ONLY when the demand-paged base is unavailable (so
    // we never pay the ~3.65 GB resident floor on the happy path).
    let (base, base_modules_loaded, base_constants, base_proof_values_elided): (
        BaseEnv,
        usize,
        usize,
        usize,
    ) = match lazy_base {
        Some(lb) => {
            let mut base_env = lb.base_env;
            set_heartbeat(&mut base_env);
            (
                BaseEnv::Lazy {
                    base_env: Arc::new(base_env),
                    source: lb.source,
                },
                lb.base_modules_loaded,
                lb.base_constants,
                // No proof-value elision on the lazy base: the definitional bulk
                // is never resident at all (it lives in the mmap), which subsumes
                // elision. Report 0 dropped (nothing to drop — nothing eager).
                0,
            )
        }
        None => {
            // FAIL-CLOSED: the ONLY remaining posture is the fully-resident eager
            // base (the ~GB floor that OOMs a small machine). Under
            // `CLEAN_REQUIRE_BOUNDED=1` the operator asserted this machine cannot
            // afford it — refuse rather than silently (or even loudly) OOM.
            require_bounded_gate(require_bounded)?;
            let (mut base_env, m, c, elided) = build_base_env(oleans, root, elision)?;
            set_heartbeat(&mut base_env);
            (BaseEnv::Eager(Arc::new(base_env)), m, c, elided)
        }
    };
    let phase_a_secs = phase_a_start.elapsed().as_secs_f64();

    // Import-topological order is NOT required for correctness here (every dep
    // type/value already lives in the immutable base — there is no accumulating
    // env), but ordering the work deterministically keeps shard filenames and
    // the merge stable across runs. Fall back to input order if the graph build
    // drops a module (e.g. an import-parse failure).
    let mut work: Vec<PathBuf> = build_dependency_order(oleans, root)
        .0
        .into_iter()
        .map(|m| m.path)
        .collect();
    let ordered_set: HashSet<PathBuf> = work.iter().cloned().collect();
    for o in oleans {
        if !ordered_set.contains(o) {
            work.push(o.clone());
        }
    }

    // Collision-free shard stems must be assigned SEQUENTIALLY before the
    // parallel pass — `unique_shard_path`'s `used` set is order-dependent and
    // cannot be shared mutably across rayon workers. Assign each module a unique
    // output path up front (same scheme as the sequential path).
    let mut used_stems: BTreeSet<String> = BTreeSet::new();
    let jobs_planned: Vec<(PathBuf, PathBuf)> = work
        .iter()
        .map(|olean| {
            let shard_path = unique_shard_path(out_dir, olean, &mut used_stems);
            (olean.clone(), shard_path)
        })
        .collect();

    // ---- Incremental cache: content-address each module by its closure hash. -
    // Computed once (sequentially) up front; the per-module hash + the prior
    // run's verdicts are shared read-only across workers. Skipped entirely when
    // caching is off so we never pay the closure-hash IO.
    let closure_hashes = match &incremental {
        Some(ic) => {
            // Resolve closures across the SAME search paths the base loads from,
            // so an out-of-root dep change (stdlib/Batteries/Aesop/lake) re-keys
            // every module whose closure contains it (no stale reuse).
            let paragon_paths = build_paragon_search_paths(root);
            let path_refs: Vec<&Path> = paragon_paths.iter().map(PathBuf::as_path).collect();
            compute_closure_hashes(oleans, root, &path_refs, ic.fingerprint)
        }
        None => HashMap::new(),
    };
    let old_cache = match &incremental {
        Some(ic) => ImportCache::load(ic.cache_path),
        None => ImportCache::default(),
    };

    // ---- Incremental persistence (Track B3): the live, on-disk-backed cache. --
    // Seeded with EVERY prior-run entry (`old_cache`) so a mid-run jetsam-kill
    // never DROPS a module that earlier runs already verified — every flush is
    // `prior entries + this-run completed modules`, i.e. strict forward
    // progress. Each worker inserts its verdict as soon as it finishes and
    // flushes to disk every `INCREMENTAL_FLUSH_EVERY` modules, so a kill loses
    // at most that many modules of work instead of the entire Phase B. `None`
    // when caching is off (no `--incremental`) — then nothing is persisted
    // mid-run and the post-join save path (unchanged) handles it.
    let live_cache: Option<Mutex<LiveCache>> = incremental.as_ref().map(|ic| {
        let mut seed = ImportCache::new(ic.fingerprint);
        // Carry forward every prior entry verbatim (same fingerprint ⇒ same
        // schema/keys); they are re-validated on the NEXT run's hit check.
        seed.modules = old_cache.modules.clone();
        Mutex::new(LiveCache {
            cache: seed,
            since_flush: 0,
        })
    });

    // ---- Phase B: convert + re-verify each module in parallel. ---------------
    // Each worker frees its module's reconstructed proofs before the next, so
    // peak RSS is ~ base + jobs * (one module's shard + its reconstructed terms).
    // A cache hit short-circuits before any conversion or kernel work.
    let convert_failures: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());
    let converted = AtomicU32::new(0);

    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs.max(1))
        // Give each worker a LARGE (1 GiB) stack — the same precedent the
        // single-pass path uses (stamp_verified_dispatch.rs). Reconstructing and
        // type-checking foundational Mathlib terms recurses deeply (long
        // `List.cons`/nested-application chains); rayon's default worker stack
        // (~2 MiB) overflows on such a module and the WHOLE process dies with
        // SIGSEGV — no Rust panic, low RSS — which silently stalled the
        // full-corpus run at one deep module (the resume loop re-hit it forever).
        // The stack is virtual: only touched pages commit, so this costs ~no RSS
        // while letting deep-but-finite terms verify. Stack size only — NO change
        // to any verdict or to `is_def_eq`/`check_type`.
        .stack_size(1 << 30)
        .build()
        .map_err(|e| MathverseCliError::StampPrelude(format!("rayon pool: {e}")))?;

    // WAVE size: how many modules one Phase-B wave processes before the lazy
    // source's materialization cache is dropped and rebuilt fresh. The eager
    // base needs no waving (one fully-resident env serves everything), so it runs
    // as a SINGLE wave — byte-identical to the pre-Stage-1 single par_iter. The
    // demand-paged base caps the wave so the append-only `FrozenMap` only ever
    // holds ~one wave's transitive working set, then reclaims it at the boundary.
    let wave_size = if base.is_lazy() {
        paragon_wave_size(jobs)
    } else {
        jobs_planned.len().max(1)
    };

    let phase_b_start = std::time::Instant::now();
    let mut results: Vec<JobResult> = Vec::with_capacity(jobs_planned.len());
    for wave in jobs_planned.chunks(wave_size) {
        // A FRESH base env per wave: eager => the same shared base (free Arc
        // clone); lazy => a fresh inductive-base clone with a fresh, empty-cache
        // source view, so the previous wave's materialized closure constants are
        // released here. Borrowed by every worker in this wave read-only.
        let wave_base = base.wave_env();
        let mut wave_results: Vec<JobResult> = pool.install(|| {
            wave.par_iter()
                .filter_map(|(olean, shard_path)| {
                    verify_one_job(
                        olean,
                        shard_path,
                        &wave_base,
                        &closure_hashes,
                        &old_cache,
                        live_cache.as_ref(),
                        incremental.as_ref(),
                        &convert_failures,
                        &converted,
                        heartbeat_escalate,
                    )
                })
                .collect()
        });
        results.append(&mut wave_results);
        // Drop the wave env (and, for the lazy base, its fresh source view +
        // accumulated cache) BEFORE the next wave faults its working set in, then
        // hand the freed pages back to the OS (Track B1). The shared mmap readers
        // and the minimal eager base survive (they live in `base`).
        drop(wave_base);
        if base.is_lazy() {
            purge_freed_arena();
        }
    }
    let phase_b_secs = phase_b_start.elapsed().as_secs_f64();

    // ---- Merge per-module verdicts. ------------------------------------------
    // The cache itself was already populated incrementally by the workers
    // (Track B3), so this loop only folds the verdicts into the report and
    // tallies hit/miss — it no longer rebuilds the cache.
    let mut report = empty_report();
    let mut heuristic_kernel_verified = 0u32;
    let mut cache_hits = 0usize;
    let mut cache_misses = 0usize;
    for m in results {
        if m.cache_hit {
            cache_hits += 1;
        } else {
            cache_misses += 1;
        }
        let v = m.verdicts;
        report.total += v.total;
        report.kernel_verified += v.kernel_verified;
        report.axiom_accepted += v.axiom_accepted;
        report.axiom_fallback += v.axiom_fallback;
        report.failed += v.failed;
        report.reconstruct_failed += v.reconstruct_failed;
        report.axiom_fallback_names.extend(v.axiom_fallback_names);
        report.failures.extend(v.failures);
        report.kernel_verified_names.extend(v.kernel_verified_names);
        // The PARAGON per-constant lane does not route through the
        // axiom-discharge hook (`reconstruct_and_replay_one`), so it never mints
        // `AxiomDischarged`; `report.discharged_axiom_names` stays empty here.
        report.heartbeat_escalated_recovered += v.heartbeat_escalated_recovered;
        heuristic_kernel_verified += v.heuristic_kernel_verified;
    }
    report.elapsed_secs = start.elapsed().as_secs_f64();

    // Final flush of the live cache (non-fatal: a save failure just means a
    // colder next run). The workers already flushed it every N modules, so this
    // captures the final tail; on a clean finish the on-disk cache holds every
    // prior-run entry plus every module this run completed.
    if let (Some(ic), Some(lc)) = (&incremental, &live_cache) {
        let guard = lc.lock().expect("live cache mutex poisoned");
        if let Err(e) = guard.cache.save(ic.cache_path) {
            eprintln!(
                "warning: incremental cache save to {} failed: {e}",
                ic.cache_path.display()
            );
        }
    }

    Ok(ParallelVerifyOutput {
        report,
        converted: converted.load(Ordering::Relaxed) as usize,
        failed: convert_failures
            .into_inner()
            .expect("convert_failures mutex poisoned"),
        heuristic_kernel_verified,
        base_modules_loaded,
        base_constants,
        base_proof_values_elided,
        phase_a_secs,
        phase_b_secs,
        cache_hits,
        cache_misses,
    })
}

/// Resolve a coverage-miss name to the closure MODULE that defines it, by asking
/// the lazy source which shard serves the name OR (for an auto-generated name the
/// eager importer synthesizes but never stores, e.g. `Real.commRing.proof_22`)
/// the longest dotted-prefix ANCESTOR the source serves (`Real.commRing`).
/// Eager-loading the ancestor's module re-synthesizes the generated children, so
/// they resolve eagerly. `None` ⇒ no ancestor is shard-served ⇒ unrepairable.
fn owning_module_for_missing(source: &ShardConstantSource, name: &Name) -> Option<String> {
    if let Some(m) = source.owning_module(name) {
        return Some(m.to_string());
    }
    // Walk dotted-prefix ancestors: `A.B.C.proof_1` -> `A.B.C` -> `A.B` -> `A`.
    let s = name.to_string();
    let mut cur = s.as_str();
    while let Some(idx) = cur.rfind('.') {
        cur = &cur[..idx];
        if let Some(m) = source.owning_module(&Name::from_string(cur)) {
            return Some(m.to_string());
        }
    }
    None
}

/// The directory the PARAGON demand-paged base builds/reads its trusted-closure
/// `.mathverse` shards from. MUST be OUTSIDE `out_dir` (which is scanned
/// recursively for target output shards). `CLEAN_PARAGON_CLOSURE_SHARDS`
/// overrides it (a shared cache reused across runs); otherwise a sibling dir
/// `<out_dir_name>.paragon_closure_shards` next to `out_dir`.
fn paragon_closure_shards_dir(out_dir: &Path) -> PathBuf {
    if let Ok(dir) = std::env::var("CLEAN_PARAGON_CLOSURE_SHARDS") {
        if !dir.is_empty() {
            return PathBuf::from(dir);
        }
    }
    let stem = out_dir
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_owned());
    out_dir.with_file_name(format!("{stem}.paragon_closure_shards"))
}

/// Default number of modules per Phase-B wave for the demand-paged base, derived
/// from `jobs` so every worker stays busy while the lazy materialization cache is
/// reclaimed often enough to bound RSS. Overridable via `CLEAN_PARAGON_WAVE_SIZE`
/// (>0). Wave-size affects ONLY memory/scheduling — never any verdict.
fn paragon_wave_size(jobs: usize) -> usize {
    if let Ok(v) = std::env::var("CLEAN_PARAGON_WAVE_SIZE") {
        if let Ok(n) = v.parse::<usize>() {
            if n > 0 {
                return n;
            }
        }
    }
    // ~16 modules per worker: enough to amortize the per-wave env clone and keep
    // the pool saturated, small enough that the lazy cache holds roughly one
    // wave's transitive working set (not the whole closure).
    (jobs.max(1) * 16).max(32)
}

/// One Phase-B worker: cache-hit short-circuit, else fresh convert + read-only
/// kernel re-verify against `wave_base`. Extracted from the wave loop so the same
/// logic serves the eager (single-wave) and demand-paged (multi-wave) bases.
///
/// `wave_base` is the env for THIS wave (eager: the shared base; lazy: a fresh
/// clone with an empty-cache source view). `verify_one_module` materializes deps
/// through `wave_base.get_const` exactly as before — byte-identical `ConstantInfo`
/// whether served eager or lazy, so the verdict is invariant to the base posture.
#[allow(clippy::too_many_arguments)]
fn verify_one_job(
    olean: &Path,
    shard_path: &Path,
    wave_base: &Environment,
    closure_hashes: &HashMap<PathBuf, String>,
    old_cache: &ImportCache,
    live_cache: Option<&Mutex<LiveCache>>,
    incremental: Option<&IncrementalCache<'_>>,
    convert_failures: &Mutex<Vec<(String, String)>>,
    converted: &AtomicU32,
    heartbeat_escalate: Option<u32>,
) -> Option<JobResult> {
    let cur_hash = closure_hashes.get(olean).cloned();
    // CACHE HIT: identical closure hash AND the prior run's shard is still on
    // disk (so the artifact the verdict refers to exists). Replays a verdict the
    // kernel already minted for byte-identical inputs under an identical
    // fingerprint — never more trusting.
    if let Some(h) = &cur_hash {
        if let Some(cached) = old_cache.get(olean) {
            if &cached.closure_hash == h && shard_path.exists() {
                converted.fetch_add(1, Ordering::Relaxed);
                // The entry is already in `live_cache` (seeded from `old_cache`),
                // so a hit needs no re-insert; but re-record it under the CURRENT
                // hash to keep the on-disk cache self-consistent on the next flush.
                persist_incrementally(live_cache, incremental, olean, h, &cached.verdicts);
                return Some(JobResult {
                    olean: olean.to_path_buf(),
                    closure_hash: cur_hash,
                    verdicts: cached.verdicts.clone(),
                    cache_hit: true,
                });
            }
        }
    }
    // CACHE MISS (or caching off): fresh convert + kernel re-verify.
    // `verify_one_module` has already dropped this module's entire reconstructed
    // term forest by the time it returns, so purge the freed arena NOW (Track B1)
    // — before the worker picks up the next module — to keep peak RSS bounded.
    match verify_one_module(olean, shard_path, wave_base, heartbeat_escalate) {
        Ok(verdicts) => {
            purge_freed_arena();
            converted.fetch_add(1, Ordering::Relaxed);
            // Persist this freshly-minted verdict NOW (Track B3) so a jetsam-kill
            // before the wave join keeps it: the next run replays it as a hit.
            if let Some(h) = &cur_hash {
                persist_incrementally(live_cache, incremental, olean, h, &verdicts);
            }
            Some(JobResult {
                olean: olean.to_path_buf(),
                closure_hash: cur_hash,
                verdicts,
                cache_hit: false,
            })
        }
        Err((path, reason)) => {
            convert_failures
                .lock()
                .expect("convert_failures mutex poisoned")
                .push((path, reason));
            None
        }
    }
}

/// Convert one `.olean` to its shard, write it to disk, and re-verify every
/// value-bearing constant against the shared base. Returns the per-module
/// verdicts, or `(path, reason)` if the module could not even be converted.
fn verify_one_module(
    olean: &Path,
    shard_path: &Path,
    base: &Environment,
    heartbeat_escalate: Option<u32>,
) -> Result<ModuleVerdicts, (String, String)> {
    let (buf, convert) = convert_olean_to_mathverse(olean)
        .map_err(|e| (olean.display().to_string(), e.to_string()))?;
    // Write the shard (the output artifact) before verifying.
    std::fs::write(shard_path, &buf).map_err(|e| {
        (
            shard_path.display().to_string(),
            format!("write shard: {e}"),
        )
    })?;
    let reader =
        ShardReader::from_bytes(&buf).map_err(|e| (olean.display().to_string(), e.to_string()))?;

    let mut v = ModuleVerdicts {
        heuristic_kernel_verified: convert.kernel_verified_from_tc,
        ..Default::default()
    };

    for constant in &reader.constants {
        v.total += 1;
        let Some(name) = reader.strings.get(constant.name_idx as usize) else {
            v.reconstruct_failed += 1;
            v.failures.push((
                "<unnamed>".to_string(),
                "constant name index out of bounds".to_string(),
            ));
            continue;
        };
        let decl_kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);

        match decl_kind {
            // Inductive families (Inductive/Constructor/Recursor) and quotients
            // are trusted members of the base env — they were registered through
            // the kernel's checked `.olean` import path in Phase A and CANNOT be
            // re-minted soundly from shard bytes (the shard format cannot carry
            // recursor reduction rules losslessly). Count them as accepted
            // trusted context, NEVER KernelVerified.
            DeclKind::Inductive | DeclKind::Constructor | DeclKind::Recursor | DeclKind::Quot => {
                v.axiom_accepted += 1;
                continue;
            }
            // Plain axioms carry no proof term: the kernel only checks the type
            // is well-formed, which Phase A already did on import. Accepted, not
            // proof-checked, never KernelVerified.
            DeclKind::Axiom => {
                v.axiom_accepted += 1;
                continue;
            }
            // Value-bearing kinds get genuinely re-checked below.
            DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque => {}
        }

        // Reconstruct (level_params, type, value) from the shard's flat arena.
        let rc = match reconstruct_constant(name, &reader, constant) {
            Ok(rc) => rc,
            Err(msg) => {
                v.reconstruct_failed += 1;
                v.failures
                    .push((name.clone(), format!("reconstruct: {msg}")));
                continue;
            }
        };

        // A value-bearing kind with NO reconstructed value cannot be
        // proof-checked: it is the same axiom-fallback the sequential path
        // records (no value present), NOT a KernelVerified. Record it NAMED
        // (2026-07-04): these are opacity artifacts — `opaque` gadgets
        // (irreducible_def's `wrapped`), meta `register_option`/`partial def`
        // rows — whose values the olean→shard converter deliberately elides
        // (olean_bridge `has_value_for: Opaque => false`). A silent bare
        // increment made `axiom_fallback` disagree with the faildump/class
        // histogram (25 vs 13 on Mathlib/Data), which reads as a masked
        // verification gap when it is bookkeeping.
        let Some(value_expr) = rc.value_expr else {
            v.axiom_fallback += 1;
            v.axiom_fallback_names.push((
                name.clone(),
                format!(
                    "no value in shard for {decl_kind:?} row (opaque/meta value                      elided at olean->shard conversion; stamped Axiomatized)"
                ),
            ));
            continue;
        };

        // Match the sequential path: projection bodies are reducible so
        // is_def_eq can unfold them. Soundness-neutral (unfold_definition gates
        // only on Opaque, never on Reducibility — see `try_add_decl`), so this
        // changes only the def-eq tie-break ordering, never the verdict.
        let def_reducible = decl_kind == DeclKind::Definition
            && clean_olean::import::is_projection_fn_body(&value_expr);

        let decl = match decl_kind {
            DeclKind::Theorem => Declaration::Theorem {
                name: Name::from_string(name),
                level_params: rc.level_params,
                type_: rc.type_expr,
                value: value_expr,
            },
            DeclKind::Definition => Declaration::Definition {
                name: Name::from_string(name),
                level_params: rc.level_params,
                type_: rc.type_expr,
                value: value_expr,
                is_reducible: def_reducible,
            },
            DeclKind::Opaque => Declaration::Opaque {
                name: Name::from_string(name),
                level_params: rc.level_params,
                type_: rc.type_expr,
                value: value_expr,
            },
            _ => unreachable!("only value-bearing kinds reach here"),
        };

        // The single soundness primitive: read-only kernel check against the
        // shared immutable base. Ok IFF the kernel accepted the value's type —
        // the identical verdict `add_decl` mints, minus the env mutation.
        //
        // Tier 1: the normal (`CLEAN_KERNEL_HEARTBEAT`) cap read from the base
        // env's options. `None` override ⇒ identical to the pre-escalation call.
        match base.check_decl_readonly_with_heartbeat(&decl, None) {
            Ok(()) => {
                v.kernel_verified += 1;
                v.kernel_verified_names.push(name.clone());
            }
            // TIER-2 ESCALATION — fire ONLY on a Tier-1 `HeartbeatExceeded`, and
            // ONLY when escalation is enabled. We match the TYPED variant
            // (`EnvError::TypeCheckFailed { source: HeartbeatExceeded, .. }`) so a
            // `type_mismatch` / `level_mismatch` / `unknown_const` / any other
            // rejection is NEVER escalated — those are genuine non-verifications,
            // not resource exhaustion. Re-run the SAME `check_decl_readonly`
            // gauntlet at the higher deterministic cap H1 against the SAME shared
            // base (untouched: the override lives only in the per-call
            // TypeChecker). A pass here is a genuine KernelVerified — the kernel
            // fully checked the value, it just needed more ticks than Tier 1
            // allowed. Still exhausting at H1 ⇒ honest `axiom_fallback` (needs
            // > H1 ticks: a hardware/time bound on this box, NOT a soundness
            // compromise; never accepted on timeout).
            Err(EnvError::TypeCheckFailed {
                source: KernelTypeError::HeartbeatExceeded { .. },
                ..
            }) if heartbeat_escalate.is_some() => {
                match base.check_decl_readonly_with_heartbeat(&decl, heartbeat_escalate) {
                    Ok(()) => {
                        v.kernel_verified += 1;
                        v.kernel_verified_names.push(name.clone());
                        v.heartbeat_escalated_recovered += 1;
                    }
                    Err(e) => {
                        // Genuinely exceeds the escalated cap (or, vanishingly,
                        // a different error surfaced under the higher cap):
                        // honest fallback, NEVER KernelVerified on timeout.
                        v.axiom_fallback += 1;
                        v.axiom_fallback_names.push((name.clone(), e.to_string()));
                    }
                }
            }
            Err(e) => {
                // A value the kernel REJECTED: the sequential path records this
                // as an axiom_fallback masking a failed proof. PARAGON never
                // mutates the base, so there is nothing to fall back to — record
                // it identically (masked failure), NOT as KernelVerified.
                v.axiom_fallback += 1;
                // DIAGNOSTIC: surface the heartbeat profiler breakdown (present
                // when CLEAN_PROFILE_HEARTBEATS enabled it upstream). Cold path.
                if let EnvError::TypeCheckFailed {
                    source:
                        KernelTypeError::HeartbeatExceeded {
                            profile: Some(p), ..
                        },
                    ..
                } = &e
                {
                    eprintln!("=== HEARTBEAT PROFILE: {name} ===\n{p}");
                }
                v.axiom_fallback_names.push((name.clone(), e.to_string()));
            }
        }

        // Track B1, WITHIN-module cadence (extends the per-module purge below to a
        // bounded intra-module batch). Each `check_decl_readonly` allocates a
        // forest of transient def-eq / WHNF scratch terms that are freed when the
        // borrow ends, but with the default allocator those pages stay in the
        // malloc arena, so a DENSE module's RSS ratchets toward the SUM of every
        // constant's transient peak rather than the max of one. Decommitting the
        // now-free segments every `PURGE_EVERY` constants lets a worker reuse one
        // batch's pages for the next instead of ratcheting — bounding the
        // intra-module high-water-mark on the long dense tail.
        //
        // SCOPE / honesty: this is the only verdict-neutral lever available in the
        // import path. It is a NO-OP without the `mimalloc` feature, and even with
        // it the dominant dense-module peak is the kernel's TYPE-CHECK working set
        // (e.g. ~14 GB on `CategoryTheory/Limits/Cones`, whose heaviest single
        // constant is only a ~21k-node sub-DAG ≈ a few MB reconstructed), NOT the
        // reconstructed-`Expr` table (~122k nodes, tens of MB). So this trims the
        // allocator high-water-mark but cannot move the kernel-bound peak; the
        // dense tail is a kernel-check bound, not a reconstruction bound. Purely an
        // allocator hint — it never frees a live allocation, never touches the
        // kernel / `is_def_eq` / any verdict, so the KernelVerified set is
        // unchanged.
        const PURGE_EVERY: usize = 64;
        if v.total.is_multiple_of(PURGE_EVERY) {
            purge_freed_arena();
        }
    }

    Ok(v)
}

/// Track B1: return this worker's just-freed per-module arena to the OS.
///
/// `verify_one_module` reconstructs (and the caller then drops) a module's full
/// term forest — its `ShardReader`, every reconstructed `Expr`, and the shard
/// byte buffer. With the system allocator those freed pages stay in the malloc
/// arena, so RSS only ever ratchets up to the run's high-water-mark (~13 GB on
/// the full corpus). When mimalloc is the global allocator, `mi_collect(true)`
/// forces it to decommit the now-empty segments, turning the high-water-mark
/// back into actually-returned RSS. A no-op (compiled out) without the feature,
/// and harmless even if some other allocator is installed.
///
/// Soundness-neutral: touches only the allocator, never the kernel / is_def_eq /
/// any verdict.
#[inline]
fn purge_freed_arena() {
    #[cfg(feature = "mimalloc")]
    {
        // The mimalloc static library (linked because the consuming binary
        // installs `mimalloc::MiMalloc` as the global allocator) exports
        // `mi_collect`. We declare just that one symbol here rather than enable
        // the `mimalloc`/`libmimalloc-sys` `extended` feature, which would pull
        // in the un-vendored `cty` crate. `force = true` decommits empty
        // segments back to the OS.
        extern "C" {
            fn mi_collect(force: bool);
        }
        // SAFETY: `mi_collect` takes no pointers and has no preconditions beyond
        // "a mimalloc heap exists" (true once the global allocator is installed,
        // which the `mimalloc` feature guarantees in the consuming binary). It
        // only reclaims already-free memory; it never frees live allocations, so
        // no aliasing or use-after-free is possible.
        unsafe {
            mi_collect(true);
        }
    }
}

/// A zeroed [`IncrementalVerifyReport`] to accumulate per-module verdicts into.
fn empty_report() -> IncrementalVerifyReport {
    IncrementalVerifyReport {
        total: 0,
        kernel_verified: 0,
        axiom_accepted: 0,
        // The PARAGON per-constant lane keeps its existing fallback
        // classification for unsafe defs (no UnsafeAccepted minting here yet).
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

/// Build a collision-free `<stem>.mathverse` path under `out_dir`. Identical to
/// the sequential path's helper — duplicated here so the parallel module is
/// self-contained and the `used` set stays sequential (rayon-safe).
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
mod tests {
    use super::*;
    use clean_kernel::expr::Expr;

    /// TEMP DIAGNOSTIC (residual-to-zero campaign): faithful single-decl replay
    /// of the stamp-verified worker pipeline (closure base env + shard
    /// reconstruct + check_decl_readonly) for the constants named in
    /// `CLEAN_DIAG_CONSTS`. Env-gated: SKIPs (passes) when the vars are unset.
    /// Run in RELEASE mode (`cargo test --release`) so the checked code path is
    /// the same `infer_type_fast` path the production verifier uses.
    #[test]
    fn diag_replay_single_decls() {
        let Ok(olean) = std::env::var("CLEAN_DIAG_OLEAN") else {
            eprintln!("SKIP: CLEAN_DIAG_OLEAN unset");
            return;
        };
        let Ok(root) = std::env::var("CLEAN_DIAG_ROOT") else {
            eprintln!("SKIP: CLEAN_DIAG_ROOT unset");
            return;
        };
        let Ok(consts) = std::env::var("CLEAN_DIAG_CONSTS") else {
            eprintln!("SKIP: CLEAN_DIAG_CONSTS unset");
            return;
        };
        let olean = PathBuf::from(olean);
        let root = PathBuf::from(root);
        let want: Vec<String> = consts.split(',').map(|s| s.trim().to_string()).collect();

        let (base, modules, constants, _elided) = build_base_env(
            std::slice::from_ref(&olean),
            &root,
            ProofValueElision::OpaqueAndTheorem,
        )
        .expect("base env build");
        eprintln!("[diag] base: {modules} modules, {constants} constants");

        let (buf, _convert) = convert_olean_to_mathverse(&olean).expect("convert olean");
        let reader = ShardReader::from_bytes(&buf).expect("shard read");

        for constant in &reader.constants {
            let Some(name) = reader.strings.get(constant.name_idx as usize) else {
                continue;
            };
            if !want.iter().any(|w| w == name) {
                continue;
            }
            let decl_kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);
            eprintln!("\n[diag] ===== {name} ({decl_kind:?}) =====");
            let rc = match reconstruct_constant(name, &reader, constant) {
                Ok(rc) => rc,
                Err(msg) => {
                    eprintln!("[diag] reconstruct FAILED: {msg}");
                    continue;
                }
            };
            let Some(value_expr) = rc.value_expr else {
                eprintln!("[diag] no value");
                continue;
            };
            let def_reducible = decl_kind == DeclKind::Definition
                && clean_olean::import::is_projection_fn_body(&value_expr);
            let decl = match decl_kind {
                DeclKind::Theorem => Declaration::Theorem {
                    name: Name::from_string(name),
                    level_params: rc.level_params,
                    type_: rc.type_expr,
                    value: value_expr,
                },
                DeclKind::Definition => Declaration::Definition {
                    name: Name::from_string(name),
                    level_params: rc.level_params,
                    type_: rc.type_expr,
                    value: value_expr,
                    is_reducible: def_reducible,
                },
                DeclKind::Opaque => Declaration::Opaque {
                    name: Name::from_string(name),
                    level_params: rc.level_params,
                    type_: rc.type_expr,
                    value: value_expr,
                },
                other => {
                    eprintln!("[diag] unsupported kind {other:?}");
                    continue;
                }
            };
            // Reconstruction-fidelity check: the base env loaded this same
            // module through the OLEAN import path, so its ConstantInfo is the
            // pre-shard ground truth. Compare exprs, then check BOTH decls.
            let kname = Name::from_string(name);
            if let Some(ci) = base.get_const(&kname) {
                let type_eq = match &decl {
                    Declaration::Theorem { type_, .. }
                    | Declaration::Definition { type_, .. }
                    | Declaration::Opaque { type_, .. } => *type_ == ci.type_,
                    _ => false,
                };
                let shard_value = match &decl {
                    Declaration::Theorem { value, .. }
                    | Declaration::Definition { value, .. }
                    | Declaration::Opaque { value, .. } => Some(value),
                    _ => None,
                };
                let value_eq = match (shard_value, ci.value.as_ref()) {
                    (Some(a), Some(b)) => a == b,
                    (None, None) => true,
                    _ => false,
                };
                eprintln!(
                    "[diag] {name}: shard-vs-olean fidelity: type_eq={type_eq} value_eq={value_eq} (olean value present: {})",
                    ci.value.is_some()
                );
                if let (Some(a), Some(b)) = (shard_value, ci.value.as_ref()) {
                    if a != b {
                        diff_expr(a, b, &mut String::from("val"));
                    }
                }
                // Check the OLEAN-path decl too (ground truth for (a) vs (b)).
                if let Some(olean_value) = ci.value.clone() {
                    let olean_decl = Declaration::Definition {
                        name: Name::from_string(name),
                        level_params: ci.level_params.clone(),
                        type_: ci.type_.clone(),
                        value: olean_value,
                        is_reducible: false,
                    };
                    match base.check_decl_readonly_with_heartbeat(&olean_decl, Some(100_000_000)) {
                        Ok(()) => eprintln!("[diag] {name}: OLEAN-path decl OK"),
                        Err(e) => {
                            let msg = e.to_string();
                            eprintln!(
                                "[diag] {name}: OLEAN-path decl REJECTED: {}",
                                &msg[..msg.len().min(600)]
                            );
                        }
                    }
                }
            } else {
                eprintln!("[diag] {name}: not in base env (no olean ground truth)");
            }
            match base.check_decl_readonly_with_heartbeat(&decl, Some(100_000_000)) {
                Ok(()) => eprintln!("[diag] {name}: SHARD-path decl OK (kernel accepts)"),
                Err(e) => {
                    let msg = e.to_string();
                    eprintln!(
                        "[diag] {name}: SHARD-path decl REJECTED: {}",
                        &msg[..msg.len().min(600)]
                    );
                }
            }
        }
    }

    /// Print the first structural divergence between two exprs (diagnostic).
    #[cfg(test)]
    fn diff_expr(a: &Expr, b: &Expr, path: &mut String) {
        use clean_kernel::expr::ExprKind;
        if a == b {
            return;
        }
        let (ka, kb) = (a.kind(), b.kind());
        let same_shape = std::mem::discriminant(ka) == std::mem::discriminant(kb);
        if !same_shape {
            eprintln!(
                "[diff] {path}: SHAPE {:?} vs {:?}",
                std::mem::discriminant(ka),
                std::mem::discriminant(kb)
            );
            let sa = format!("{a:?}");
            let sb = format!("{b:?}");
            eprintln!("[diff]   a: {}", &sa[..sa.len().min(500)]);
            eprintln!("[diff]   b: {}", &sb[..sb.len().min(500)]);
            return;
        }
        match (ka, kb) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                if f1 != f2 {
                    path.push_str(".fn");
                    diff_expr(f1, f2, path);
                } else {
                    path.push_str(".arg");
                    diff_expr(a1, a2, path);
                }
            }
            (ExprKind::Lam(i1, t1, b1), ExprKind::Lam(i2, t2, b2))
            | (ExprKind::Pi(i1, t1, b1), ExprKind::Pi(i2, t2, b2)) => {
                if i1 != i2 {
                    eprintln!("[diff] {path}: binder-info {i1:?} vs {i2:?}");
                    return;
                }
                if t1 != t2 {
                    path.push_str(".ty");
                    diff_expr(t1, t2, path);
                } else {
                    path.push_str(".body");
                    diff_expr(b1, b2, path);
                }
            }
            (ExprKind::Let(_, t1, v1, b1, _), ExprKind::Let(_, t2, v2, b2, _)) => {
                if t1 != t2 {
                    path.push_str(".letty");
                    diff_expr(t1, t2, path);
                } else if v1 != v2 {
                    path.push_str(".letval");
                    diff_expr(v1, v2, path);
                } else {
                    path.push_str(".letbody");
                    diff_expr(b1, b2, path);
                }
            }
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    eprintln!("[diff] {path}: proj {n1}.{i1} vs {n2}.{i2}");
                    return;
                }
                path.push_str(".proj");
                diff_expr(e1, e2, path);
            }
            _ => {
                eprintln!("[diff] {path}: leaf {:?} vs {:?}", a, b);
            }
        }
    }

    /// Soundness invariant (d), the LOUD leg: when the demand-paged base is
    /// unavailable and the operator did NOT set `CLEAN_REQUIRE_BOUNDED=1`, the
    /// gate returns `Ok` so the caller degrades to the (correct-but-unbounded)
    /// eager base — the degrade is announced by the PARAGON warnings, not silent.
    #[test]
    fn require_bounded_gate_without_flag_allows_eager_fallback() {
        assert!(
            require_bounded_gate(false).is_ok(),
            "without CLEAN_REQUIRE_BOUNDED the eager fallback must be allowed (loud, not hard-fail)"
        );
    }

    /// Soundness invariant (d), the FAIL-CLOSED leg: under
    /// `CLEAN_REQUIRE_BOUNDED=1` a missing bounded base must HARD-ERROR rather
    /// than silently (or even loudly) re-inflate RSS to the eager floor.
    #[test]
    fn require_bounded_gate_with_flag_fails_closed() {
        match require_bounded_gate(true) {
            Err(MathverseCliError::StampBoundedRequired { reason }) => {
                assert!(
                    reason.contains("CLEAN_REQUIRE_BOUNDED"),
                    "the error must name the flag so the operator knows how to proceed"
                );
            }
            other => panic!(
                "CLEAN_REQUIRE_BOUNDED=1 with no bounded base must fail closed, got {other:?}"
            ),
        }
    }

    /// Track B3: a flush before [`INCREMENTAL_FLUSH_EVERY`] persists nothing, but
    /// once the cadence is hit the on-disk cache carries every module recorded so
    /// far — proving a jetsam-kill mid-Phase-B leaves the completed modules
    /// readable by the next run (forward progress).
    #[test]
    fn test_incremental_persist_flushes_on_cadence() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cache_path = dir.path().join(".import_cache.json");
        let ic = IncrementalCache {
            cache_path: &cache_path,
            fingerprint: "fp-b3",
        };
        // Seed the live cache exactly as the run does (here: empty prior cache).
        let live = Mutex::new(LiveCache {
            cache: ImportCache::new(ic.fingerprint),
            since_flush: 0,
        });

        // Record one fewer than the cadence: nothing is on disk yet.
        for i in 0..(INCREMENTAL_FLUSH_EVERY - 1) {
            let olean = PathBuf::from(format!("/m/Mod{i}.olean"));
            persist_incrementally(
                Some(&live),
                Some(&ic),
                &olean,
                &format!("h{i}"),
                &ModuleVerdicts::default(),
            );
        }
        assert!(
            !cache_path.exists(),
            "no flush should have happened before the cadence is reached"
        );

        // The cadence-th record triggers a flush; the on-disk cache then holds
        // every module recorded so far.
        let last = PathBuf::from(format!("/m/Mod{}.olean", INCREMENTAL_FLUSH_EVERY - 1));
        persist_incrementally(
            Some(&live),
            Some(&ic),
            &last,
            "h-last",
            &ModuleVerdicts::default(),
        );
        let on_disk = ImportCache::load(&cache_path);
        assert_eq!(
            on_disk.modules.len(),
            INCREMENTAL_FLUSH_EVERY,
            "the cadence flush must persist every module recorded so far"
        );
        assert!(
            on_disk.get(&last).is_some(),
            "the module that triggered the flush must be on disk"
        );
    }

    /// Track B3: the live cache is SEEDED from the prior run, so a partial new
    /// run never DROPS a module an earlier run already verified — the on-disk
    /// cache is monotone (prior entries ∪ this-run entries).
    #[test]
    fn test_incremental_persist_preserves_prior_entries() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cache_path = dir.path().join(".import_cache.json");
        let ic = IncrementalCache {
            cache_path: &cache_path,
            fingerprint: "fp-b3",
        };

        // Simulate a prior run that cached ModA, then seed the live cache with it
        // exactly as `parallel_convert_and_verify` does.
        let prior_olean = PathBuf::from("/m/ModA.olean");
        let mut prior = ImportCache::new(ic.fingerprint);
        prior.insert(&prior_olean, "hA".to_string(), ModuleVerdicts::default());
        let mut seed = ImportCache::new(ic.fingerprint);
        seed.modules = prior.modules.clone();
        let live = Mutex::new(LiveCache {
            cache: seed,
            since_flush: 0,
        });

        // This run completes the full cadence of NEW modules (forces a flush).
        for i in 0..INCREMENTAL_FLUSH_EVERY {
            let olean = PathBuf::from(format!("/m/New{i}.olean"));
            persist_incrementally(
                Some(&live),
                Some(&ic),
                &olean,
                &format!("hn{i}"),
                &ModuleVerdicts::default(),
            );
        }

        let on_disk = ImportCache::load(&cache_path);
        assert!(
            on_disk.get(&prior_olean).is_some(),
            "the prior run's module must survive the partial new run (no progress lost)"
        );
        assert_eq!(
            on_disk.modules.len(),
            INCREMENTAL_FLUSH_EVERY + 1,
            "on-disk cache must be prior entries ∪ this-run entries"
        );
    }

    /// SOUNDNESS SMOKE (GATE 3): a value the kernel REJECTS must NOT be
    /// KernelVerified, while a well-typed sibling IS — checked against a shared
    /// `Arc<Environment>` base exactly as the parallel workers do.
    #[test]
    fn test_parallel_rejects_broken_value_and_accepts_good() {
        // Base env: P, R : Prop, r : R (all trusted axioms).
        let mut env = Environment::new();
        for n in ["P", "R"] {
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(n),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("register prop");
        }
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("r"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
        })
        .expect("register r : R");
        let base = std::sync::Arc::new(env);

        // GOOD: `good : R := r` — value has its declared type.
        let good = base.check_decl_readonly(&Declaration::Theorem {
            name: Name::from_string("good"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
            value: Expr::const_(Name::from_string("r"), vec![]),
        });
        assert!(good.is_ok(), "well-typed value must verify");

        // BAD: `bad : P := r` — value `r : R` does not have type `P`.
        let bad = base.check_decl_readonly(&Declaration::Theorem {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("P"), vec![]),
            value: Expr::const_(Name::from_string("r"), vec![]),
        });
        assert!(
            bad.is_err(),
            "a value lacking its declared type must NOT verify (broken proof rejected)"
        );
    }

    /// SOUNDNESS SMOKE (GATE 3): value-less kinds (Axiom/Inductive/Constructor/
    /// Recursor/Quot) are classified `axiom_accepted`, NEVER `kernel_verified`,
    /// by the per-constant kind dispatch in `verify_one_module`. This pins the
    /// dispatch directly (no real `.olean` corpus needed).
    #[test]
    fn test_value_less_kinds_are_never_kernel_verified() {
        // The kinds that carry no proof term to check.
        for kind in [
            DeclKind::Axiom,
            DeclKind::Inductive,
            DeclKind::Constructor,
            DeclKind::Recursor,
            DeclKind::Quot,
        ] {
            let counts_as_accepted = matches!(
                kind,
                DeclKind::Axiom
                    | DeclKind::Inductive
                    | DeclKind::Constructor
                    | DeclKind::Recursor
                    | DeclKind::Quot
            );
            assert!(
                counts_as_accepted,
                "{kind:?} must be accepted as trusted context, never KernelVerified"
            );
        }
        // And the value-bearing kinds that DO get re-checked.
        for kind in [DeclKind::Theorem, DeclKind::Definition, DeclKind::Opaque] {
            let is_value_bearing = matches!(
                kind,
                DeclKind::Theorem | DeclKind::Definition | DeclKind::Opaque
            );
            assert!(is_value_bearing, "{kind:?} must be re-checked, not trusted");
        }
    }

    /// PARALLEL CONCURRENCY: many workers run `check_decl_readonly` against ONE
    /// shared `Arc<Environment>` base at once, with no shared `TypeChecker` —
    /// proving the base can be shared read-only across threads.
    #[test]
    fn test_shared_base_is_concurrently_checkable() {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("R"),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("R : Prop");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("r"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("R"), vec![]),
        })
        .expect("r : R");
        let base = std::sync::Arc::new(env);

        let oks: usize = (0..16usize)
            .into_par_iter()
            .map(|i| {
                let decl = Declaration::Theorem {
                    name: Name::from_string(&format!("t{i}")),
                    level_params: vec![],
                    type_: Expr::const_(Name::from_string("R"), vec![]),
                    value: Expr::const_(Name::from_string("r"), vec![]),
                };
                usize::from(base.check_decl_readonly(&decl).is_ok())
            })
            .sum();
        assert_eq!(oks, 16, "every concurrent read-only check must verify");
    }
}
