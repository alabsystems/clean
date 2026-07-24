// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dependency-closure loading for `clean mathverse stamp-verified --closure-root`.
//!
//! Real Mathlib modules cannot be kernel-re-verified against the bare prelude:
//! their proof terms reference constants defined in *imported* modules (e.g.
//! `Mathlib/Logic/Basic` references `Function.funext_iff`, `Iff.intro`, …). This
//! helper loads a target module's TRANSITIVE IMPORT CLOSURE into a kernel
//! [`Environment`] so that, when the target module's own declarations are
//! re-minted and proof-checked by
//! [`crate::verify::incremental::verify_corpus_incremental`], every referenced
//! constant resolves.
//!
//! SOUNDNESS BOUNDARY: the closure constants are loaded via clean-olean's
//! [`load_module_with_deps_bounded`], i.e. they are the TRUSTED IMPORTED CONTEXT
//! (registered through the kernel's `.olean` import path, exactly as `clean
//! olean verify-batch` does). They are NOT re-minted by the shard replay and
//! are NOT stamped `KernelVerified` by this command. Only the TARGET module's
//! declarations flow through `add_decl`'s `check_type` against this env, so only
//! they can earn a `KernelVerified` stamp. The target module itself is
//! deliberately excluded from the closure load so its names are fresh when the
//! shard replay re-mints them.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use std::sync::Arc;

use clean_kernel::env::{ConstantSource, ProofElisionStats, ProofValueElision};
use clean_kernel::{Environment, Name};
use clean_olean::verify_batch::module_name_from_path;
use clean_olean::{
    default_search_paths, load_module_with_deps_bounded_shared_with_policy, parse_imports_only,
    ImportError, ImportKinds, OleanImportPolicy,
};
use hashbrown::HashSet;

use crate::cli::MathverseCliError;
use crate::closure_source::ShardConstantSource;

/// Per-target slice of the shared-environment closure load: how much *new*
/// module/constant work each target contributed on top of the cumulative env
/// already built by earlier targets. The first target pays the bulk of the
/// shared closure; later targets that share dependencies add only their unique
/// modules — this is the cache win the shared env delivers.
#[derive(Debug, Clone)]
pub(crate) struct PerTargetLoad {
    /// Target module name (relative to `root`).
    pub(crate) target_module: String,
    /// Distinct modules this target added to the cumulative env that no earlier
    /// target had already loaded (0 means a full closure-reuse hit).
    pub(crate) new_modules_loaded: usize,
    /// Constants this target's *new* modules contributed to the trusted env.
    pub(crate) new_closure_constants: usize,
    /// Wall time spent loading this target's incremental closure slice.
    pub(crate) load_millis: u128,
}

/// Outcome of loading one target module's transitive import closure into a
/// kernel environment.
pub(crate) struct ClosureEnv {
    /// Prelude-seeded environment populated with the target module's transitive
    /// import closure (dependencies registered before dependents). Ready to be
    /// passed as the `initial_env` of `verify_corpus_incremental`.
    pub(crate) env: Environment,
    /// Distinct modules loaded into the closure (the closure size). Does NOT
    /// include the target module — it is intentionally excluded so its decls
    /// are re-minted by the shard replay rather than imported.
    pub(crate) modules_loaded: usize,
    /// Constants added to the env across the whole closure (trusted context).
    pub(crate) closure_constants: usize,
    /// The target module name (relative to `root`) whose imports were closed.
    pub(crate) target_module: String,
    /// Per-target incremental load breakdown (in input order). Demonstrates the
    /// shared-env reuse: the first target loads the bulk closure, subsequent
    /// targets that share it load only their unique delta.
    pub(crate) per_target: Vec<PerTargetLoad>,
    /// Bounded-memory pass result: how many never-unfolded proof VALUES were
    /// dropped from the trusted closure env to cap resident memory (WS3). The
    /// policy is chosen by the caller; `total_elided() == 0` means the legacy
    /// full-resident behavior (no elision).
    pub(crate) proof_elision: ProofElisionStats,
    /// The elision policy actually applied to the closure env.
    pub(crate) elision_policy: ProofValueElision,
}

/// Hard ceiling on the number of distinct modules a single target's import
/// closure may discover before the loader fails fast. Real Mathlib aggregate
/// modules pull in thousands of transitive imports (minutes of work, multiple
/// GB of RSS); this guard keeps `stamp-verified --closure-root` bounded and
/// steers the operator toward a more foundational target. Per-target, so it
/// caps the depth of any one closure rather than the union across targets.
/// Default per-target closure-module ceiling. Overridable via the
/// `CLEAN_MAX_CLOSURE_MODULES` env var so the operator can raise it for the
/// heaviest Mathlib aggregates (Analysis / CategoryTheory pull in thousands of
/// transitive imports) when there is RAM to spare — `--closure-elide opaque`
/// keeps the loaded closure's resident memory bounded regardless of count.
const DEFAULT_MAX_CLOSURE_MODULES: usize = 1500;

pub(crate) fn max_closure_modules() -> usize {
    std::env::var("CLEAN_MAX_CLOSURE_MODULES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_MAX_CLOSURE_MODULES)
}

/// Build a prelude-seeded environment containing the transitive import closure
/// of every target `.olean` in `targets`, resolved beneath `root` plus the
/// stdlib search paths and any sibling lake-package olean roots.
///
/// SHARED-ENV CACHING: every target's import closure is loaded into ONE
/// cumulative [`Environment`], and a single caller-owned `visited` module set is
/// threaded across all targets via [`load_module_with_deps_bounded_shared`]. A
/// module that any earlier target already pulled in is skipped without
/// re-reading or re-parsing its `.olean`. The total file I/O + parse cost is
/// therefore O(union of closures) instead of O(targets × closure) — the first
/// target loads the bulk shared closure; later targets that share it pay only
/// for their unique delta. The returned env holds the union of all targets'
/// dependency closures; the target modules themselves are NOT loaded here.
///
/// SOUNDNESS: every target module's own name is pre-seeded into `visited` BEFORE
/// any load, so no target module's decls can ever enter the trusted closure env
/// — not even when a sibling target transitively imports it. Each target's
/// decls stay fresh for the shard replay to re-mint and proof-check through
/// `add_decl`'s `check_type`. Sharing the env only deduplicates the trusted
/// imported context; it never changes which decls are trusted vs re-checked.
/// BOUNDED MEMORY (WS3): after the closure env is fully built, `elision`
/// selects which never-unfolded proof VALUES are dropped from the TRUSTED
/// imported constants to cap resident memory. [`ProofValueElision::OpaqueOnly`]
/// is verdict-preserving (the kernel never δ-unfolds an `Opaque` value); the
/// target module's own decls are added later through `add_decl` and keep their
/// values, so this never affects which decls earn a `KernelVerified` stamp.
pub(crate) fn load_targets_closure(
    targets: &[PathBuf],
    root: &Path,
    elision: ProofValueElision,
) -> Result<ClosureEnv, MathverseCliError> {
    // Eager (legacy) closure: every declaration kind is registered into the env.
    let import_policy = OleanImportPolicy::default().with_proof_elision(elision);
    load_targets_closure_with_policy(targets, root, elision, import_policy)
}

/// Build the de-duplicated, priority-ordered olean search paths for a closure
/// rooted at `root`: the closure root first, then sibling lake-package olean
/// roots, then the discovered stdlib/toolchain paths.
pub(crate) fn build_closure_search_paths(root: &Path) -> Vec<PathBuf> {
    let mut search_paths: Vec<PathBuf> = Vec::new();
    let mut seen_paths: BTreeSet<PathBuf> = BTreeSet::new();
    if seen_paths.insert(root.to_path_buf()) {
        search_paths.push(root.to_path_buf());
    }
    for pkg_root in discover_lake_package_olean_roots(root) {
        if seen_paths.insert(pkg_root.clone()) {
            search_paths.push(pkg_root);
        }
    }
    for path in default_search_paths() {
        if seen_paths.insert(path.clone()) {
            search_paths.push(path);
        }
    }
    search_paths
}

/// Core closure loader, parameterized by the [`OleanImportPolicy`]. The eager
/// path uses the default (all-kinds) policy; the zero-copy HYBRID path
/// ([`load_targets_closure_mmap`]) passes [`ImportKinds::InductiveFamiliesOnly`]
/// so only the inductive families are registered eagerly and the definitional
/// kinds are left to a lazily-installed [`ShardConstantSource`].
fn load_targets_closure_with_policy(
    targets: &[PathBuf],
    root: &Path,
    elision: ProofValueElision,
    import_policy: OleanImportPolicy,
) -> Result<ClosureEnv, MathverseCliError> {
    // Search paths, in priority order, de-duplicated:
    //   1. the user-supplied closure root (so Mathlib's own modules resolve),
    //   2. sibling lake-package olean roots under the same `.lake` tree (so
    //      Batteries/Aesop/Qq/… dependency modules resolve), and
    //   3. the discovered stdlib/toolchain paths (so Init/Std deps resolve).
    let search_paths = build_closure_search_paths(root);

    // WS17: import-verification prelude — suppresses the kernel's lossy
    // hand-rolled `extends`-structure stubs (`Preorder`/`Semigroup`/…).
    // Otherwise those field-dropping stubs shadow the real Mathlib structures
    // on `.olean` import (the loader dedups by name), and every instance that
    // applies a genuine trailing field is kernel-rejected and masked to an
    // axiom. See `Environment::try_with_prelude_for_import`.
    let mut env = Environment::try_with_prelude_for_import()
        .map_err(|e| MathverseCliError::StampPrelude(e.to_string()))?;

    // Every target module's name (relative path -> module name). Pre-seeding all
    // of them into the shared `visited` set guarantees that no target module is
    // ever loaded into the trusted closure env, even when a sibling target
    // imports it transitively — its decls must stay fresh for the shard replay.
    let target_modules: Vec<String> = targets
        .iter()
        .map(|t| module_name_from_path(t, root))
        .collect();

    // The shared, caller-owned visited set: threaded across every
    // `load_module_with_deps_bounded_shared` call so the union closure's modules
    // are parsed and registered exactly once. Seeded with the target module
    // names so they are skipped if encountered.
    let mut visited: HashSet<String> = HashSet::new();
    for target_module in &target_modules {
        visited.insert(target_module.clone());
    }

    // `loaded_modules` mirrors `visited` minus the pre-seeded targets so the
    // reported closure size counts only genuinely-loaded dependency modules.
    let mut loaded_modules: BTreeSet<String> = BTreeSet::new();
    let mut closure_constants = 0usize;
    let mut per_target: Vec<PerTargetLoad> = Vec::with_capacity(targets.len());

    for (target, target_module) in targets.iter().zip(&target_modules) {
        let target_start = Instant::now();
        let mut target_new_modules = 0usize;
        let mut target_new_constants = 0usize;

        let bytes = std::fs::read(target).map_err(|e| MathverseCliError::StampClosure {
            module: target_module.clone(),
            reason: format!("read {}: {e}", target.display()),
        })?;
        let imports = parse_imports_only(&bytes).map_err(|e| MathverseCliError::StampClosure {
            module: target_module.clone(),
            reason: format!("parse imports: {e}"),
        })?;

        for import in &imports {
            let import_name = import.module_name.trim();
            if import_name.is_empty() {
                continue;
            }
            // Shared `visited`: modules an earlier target already loaded are
            // skipped here with no re-read/re-parse — the closure cache hit.
            let summaries = load_module_with_deps_bounded_shared_with_policy(
                &mut env,
                import_name,
                &search_paths,
                max_closure_modules(),
                &mut visited,
                import_policy,
            )
            .map_err(|e| MathverseCliError::StampClosure {
                module: target_module.clone(),
                reason: closure_load_reason(import_name, &e),
            })?;
            for summary in summaries {
                let loaded_name = summary
                    .module_name
                    .clone()
                    .unwrap_or_else(|| import_name.to_owned());
                // A target module pre-seeded into `visited` is never returned as
                // a freshly-loaded module, so any name appearing here is a
                // genuine dependency. Count each distinct dependency once.
                if loaded_modules.insert(loaded_name) {
                    closure_constants += summary.added_constants;
                    target_new_modules += 1;
                    target_new_constants += summary.added_constants;
                }
            }
        }

        per_target.push(PerTargetLoad {
            target_module: target_module.clone(),
            new_modules_loaded: target_new_modules,
            new_closure_constants: target_new_constants,
            load_millis: target_start.elapsed().as_millis(),
        });
    }

    // BOUNDED MEMORY (WS3): the elision already happened AT REGISTRATION via
    // `import_policy` (so peak RSS is bounded, not just steady-state). Run the
    // post-load pass too as a belt-and-suspenders sweep over any value that
    // entered through a path the loader does not gate (e.g. clean-payload or
    // axiom-stub upgrades), then report the TOTAL dropped (load-time + sweep)
    // by counting elided-kind constants that now carry no value.
    env.elide_proof_values(elision);
    let proof_elision = env.count_elided_proof_values(elision);

    Ok(ClosureEnv {
        env,
        modules_loaded: loaded_modules.len(),
        closure_constants,
        target_module: target_modules.into_iter().next().unwrap_or_default(),
        per_target,
        proof_elision,
        elision_policy: elision,
    })
}

/// Phase-1 zero-copy HYBRID closure loader (`CLEAN_LAZY_CLOSURE=1`).
///
/// Builds the SAME trusted closure env as [`load_targets_closure`], but splits
/// HOW the closure constants are served:
/// - **Eager:** the closure's INDUCTIVE families (Inductive/Constructor/Recursor/
///   Quot) are loaded from `.olean` exactly as before, via
///   [`ImportKinds::InductiveFamiliesOnly`]. They cannot be served lazily (the
///   shard format can't losslessly carry recursor reduction rules — a confirmed
///   false-accept hole), so they MUST stay eager.
/// - **Lazy:** the definitional kinds (Definition/Theorem/Axiom/Opaque) are
///   served on demand from `closure_shards` (`.mathverse`) by a
///   [`ShardConstantSource`] installed with [`Environment::set_constant_source`].
///   These are the bulk of the OOM, so most of the memory win remains.
///
/// COVERAGE GUARANTEE: before returning the lazy env, every TARGET's transitive
/// `Const`-reference closure is enumerated and each name must resolve EITHER in
/// the lazy source OR as an eagerly-loaded inductive-family / prelude name OR as
/// a target name re-minted by the replay. On ANY miss this returns `Ok(None)`,
/// signaling the caller to HARD-FALL-BACK to the eager [`load_targets_closure`]
/// — a lazy run never silently drops coverage. Shard-load failures (bad/empty
/// `CLEAN_CLOSURE_SHARDS`) are a hard error (`Err`), not a coverage miss.
///
/// SOUNDNESS: the eager inductive families resolve their definitional deps
/// through [`Environment::get_const`]'s lazy fallback; a definitional constant's
/// `ConstantInfo` is byte-identical whether eager or lazy (the source
/// materializes the same bytes — proven by `lazy_closure_verdict_matches_eager`
/// and the corpus invariance gate). Only the TARGET decls earn a verdict, and
/// they are added through `add_decl`'s `check_type` exactly as in the eager path.
pub(crate) fn load_targets_closure_mmap(
    targets: &[PathBuf],
    root: &Path,
    elision: ProofValueElision,
    closure_shards: &Path,
) -> Result<Option<ClosureEnv>, MathverseCliError> {
    // Build the lazy source FIRST so a misconfigured shard dir fails fast before
    // any olean work. A load failure here is a hard error (configuration), not a
    // coverage fallback. Held MUTABLE so the load-time content-binding
    // verification below can mark verified shards before any `get()` runs.
    let mut source = ShardConstantSource::from_dir(closure_shards).map_err(|e| {
        MathverseCliError::StampLazyClosureShards {
            dir: closure_shards.display().to_string(),
            reason: e.to_string(),
        }
    })?;

    // LOAD-TIME CONTENT-BINDING VERIFICATION (Step 8) — runs BEFORE the
    // prelude-stub override loop (which calls `get()` and `forget_decl`s trusted
    // stubs) and BEFORE the coverage gate. For each disk-loaded reader that is a
    // fail-closed, module-bound closure shard, recompute its source-olean digest
    // against the on-disk olean for the shard's OWN declaring module and confirm
    // hash + len match AND every served name belongs to that module's namespace.
    // Only a full match marks the shard verified; an unverified shard's `get()`s
    // return None => coverage miss => HARD EAGER FALLBACK. The version diagnostic
    // (Step 9) reports a v2/unbound closure dir so an all-eager downgrade is
    // observable rather than misattributed.
    let (any_v3_bound, verified_shards) = verify_closure_shards_against_oleans(&mut source, root);
    if !any_v3_bound {
        eprintln!(
            "stamp-verified: closure shard dir `{}` has NO v3 fail-closed-bound shards \
             (version<3 or fail_closed_verified=0) — lazy serving is disabled; \
             falling back to eager .olean closure (this is sound but slow).",
            closure_shards.display()
        );
        return Ok(None);
    }

    // OBSERVABILITY (all-shards-failed downgrade is VISIBLE, not silent): at least
    // one shard is a v3 fail-closed-bound shard, but NONE passed the load-time
    // content+arena binding. Every served name would then miss its (unverified)
    // shard => coverage miss => eager anyway. Surface that distinctly and return
    // `Ok(None)` now rather than do the eager-inductive-families work + coverage
    // walk only to fall back. SOUNDNESS-neutral: the result (eager) is identical;
    // this just makes the all-failed case loud and avoids wasted work.
    if verified_shards == 0 {
        eprintln!(
            "stamp-verified: closure shard dir `{}` has v3 fail-closed-bound shards but \
             ZERO passed the load-time content/arena binding (stale/swapped/corrupted vs \
             on-disk .olean, or unresolvable) — lazy serving is disabled; falling back to \
             eager .olean closure (this is sound but slow).",
            closure_shards.display()
        );
        return Ok(None);
    }

    let source: Arc<ShardConstantSource> = Arc::new(source);

    // EAGER LEG: load the closure's inductive families only. The definitional
    // kinds are skipped (left to the lazy source) by the import-kinds filter.
    // Elision is irrelevant for inductive families (they have no proof VALUE the
    // elider drops), but pass it through for parity with the eager path.
    let import_policy = OleanImportPolicy::default()
        .with_proof_elision(elision)
        .with_import_kinds(ImportKinds::InductiveFamiliesOnly);
    let mut closure = load_targets_closure_with_policy(targets, root, elision, import_policy)?;

    // PRELUDE-STUB OVERRIDE (verdict parity): the import-verification prelude
    // registers AXIOM STUBS for some library names (e.g. `Membership.mem`:
    // set_theory.rs `init_set` → `Declaration::Axiom`). In the FULLY-EAGER closure
    // the real `.olean` DEFINITION OVERWRITES that stub; but the HYBRID leg
    // (`InductiveFamiliesOnly`) SKIPS the definitional `.olean` load, so the stub
    // survives in `self.constants` and — because `get_const` checks the eager map
    // FIRST — shadows the faithful shard. The stub has a different type AND no
    // value, so any target whose proof δ-reduces the real definition (the 7
    // `mem_ite`/`ite_mem`/… lemmas all hit `Membership.mem`) diverges eager-vs-lazy.
    //
    // Mirror the eager overwrite EXACTLY: for every name the shard can serve, if
    // the eager map currently holds a value-LESS Axiom stub while the shard serves
    // a value-BEARING constant of the same name, drop the eager stub so the shard
    // (which equals the eager `.olean` definition — proven by diag_diff) resolves.
    // Narrow by construction: only value-less Axiom entries that a real definition
    // supersedes are removed; genuine eager inductive members are value-less too
    // but are NOT shard-served (servable_kind excludes them), so they are untouched.
    {
        use clean_kernel::env::{ConstantKind, ConstantSource};
        let src: &ShardConstantSource = &source;
        // Iterate the EAGER map's value-less Axiom stubs (the prelude's), and drop
        // any whose name the shard serves with a value-bearing definition.
        let to_drop: Vec<Name> = closure
            .env
            .constants()
            .filter(|ci| ci.value.is_none() && ci.kind == ConstantKind::Axiom)
            .map(|ci| ci.name.clone())
            .filter(|name| ConstantSource::get(src, name).is_some_and(|ci| ci.value.is_some()))
            .collect();
        for name in to_drop {
            closure.env.forget_decl(&name);
        }
    }

    // COVERAGE CHECK: every target's transitive Const-reference closure must be
    // resolvable lazily-or-eagerly. If not, signal hard-fallback to eager.
    if !lazy_closure_covers_targets(&closure.env, &source, targets, root) {
        return Ok(None);
    }

    // Install the lazy source. From here `get_const` consults the eager map (the
    // inductive families + prelude) first, then the source on miss.
    closure.env.set_constant_source(source);
    Ok(Some(closure))
}

/// LOAD-TIME CONTENT-BINDING VERIFICATION (Step 8). For each disk-loaded reader
/// that is a fail-closed, module-bound v3 closure shard, recompute its
/// source-olean digest against the on-disk olean for the shard's OWN declaring
/// module (resolved by the SAME resolver/search-paths eager uses) and confirm
/// the recomputed `(hash, len)` equals the header's, every served name belongs
/// to that module's namespace, AND every served constant's arena reconstructs
/// (via the SAME `materialize` path the loader serves) to the build-time-verified
/// content — its `recon_digest` must equal the header's stamped per-constant
/// digest. On a full match the shard is marked verified (its `get()`s become
/// servable). Returns `(any_v3_bound, verified)`: `any_v3_bound` is `false` only
/// when NO reader is even a fail-closed-bound v3 shard (a v2 / unbound closure
/// dir), which the caller reports distinctly.
///
/// SOUNDNESS: synthetic readers (`from_merged_parts`, source hash all-zero) and
/// any reader missing the fail-closed marker / module name are SKIPPED — they
/// stay unverified and can never be lazily served. Hash/len mismatch, an
/// unresolvable olean, a subset violation, OR an arena recon_digest mismatch
/// (the load-time arena-binding check below) leave the shard unverified => eager
/// (eager needs the same oleans, so no NEW failure mode). The arena check is what
/// binds the SERVED FlatExpr arena (the lazy path skips the footer blake3) to the
/// build-time-verified content, closing the no-weaker gap for accidental
/// corruption / stale / swapped arenas (64-bit digest; the fully-malicious
/// bytes-controlling attacker stays out-of-scope — no signing key).
pub(crate) fn verify_closure_shards_against_oleans(
    source: &mut ShardConstantSource,
    root: &Path,
) -> (bool, usize) {
    let search_paths = build_closure_search_paths(root);
    let mut any_v3_bound = false;
    let mut verified = 0usize;

    for shard in 0..source.shard_count() {
        match verify_one_closure_shard(source, shard, &search_paths) {
            None => {}
            Some(true) => {
                any_v3_bound = true;
                verified += 1;
            }
            Some(false) => {
                any_v3_bound = true;
            }
        }
    }

    (any_v3_bound, verified)
}

/// Verify ONE closure shard's content binding against its on-disk olean —
/// the per-shard body of [`verify_closure_shards_against_oleans`], extracted so
/// the per-constant lazy lane can verify shards ON FIRST TOUCH (amortized to
/// the modules a run actually reaches; a whole-tree union cache at sweep scale
/// cannot afford whole-dir verification per process).
///
/// Returns:
/// * `None` — the reader is not a fail-closed-bound v3 shard (synthetic /
///   unbound / v2). It can NEVER be verified; its names stay eager.
/// * `Some(true)` — full match: source-olean digest + namespace subset + arena
///   recon_digest all bind. The shard is marked verified (its `get()`s serve).
/// * `Some(false)` — a v3-bound shard that FAILED a gate; left unverified
///   (its `get()`s refuse ⇒ per-name eager fallback). Never retried within a
///   process (the caller records the outcome), so a bad shard costs one check.
///
/// SOUNDNESS: identical gates, identical fail-closed outcome as the whole-dir
/// pass — extraction changes WHEN a shard is checked, never WHAT is checked,
/// and verification always completes BEFORE the first `get()` can serve
/// (the serve gate reads `shard_verified`, flipped only here on full match).
pub(crate) fn verify_one_closure_shard(
    source: &mut ShardConstantSource,
    shard: usize,
    search_paths: &[PathBuf],
) -> Option<bool> {
    // Collect every owned datum we need, then DROP the immutable reader
    // borrow before any `mark_shard_verified` (mutable) call.
    let (is_v3_bound, candidate) = {
        let reader = source.reader(shard)?;
        // Skip synthetic / unbound / non-fail-closed readers.
        if reader.header.source_olean_blake3 == [0u8; 32] || reader.header.fail_closed_verified != 1
        {
            (false, None)
        } else {
            (
                true,
                reader.source_module.clone().map(|module| {
                    let served: Vec<String> = reader
                        .constants
                        .iter()
                        .filter(|c| crate::closure_source::servable_kind(c.decl_kind))
                        .map(|c| reader.strings.get(c.name_idx as usize).cloned())
                        .map(|n| n.unwrap_or_default())
                        .collect();
                    (
                        module,
                        reader.header.source_olean_blake3,
                        reader.header.source_olean_len,
                        served,
                    )
                }),
            )
        }
    };
    if !is_v3_bound {
        return None;
    }
    let Some((module, hdr_hash, hdr_len, served_names)) = candidate else {
        // v3 fail-closed marker present but no module name recorded — can never
        // bind; stays unverified.
        return Some(false);
    };

    // Resolve the olean for the shard's OWN module (never the file name).
    let Some(olean) = resolve_module_olean(&module, search_paths) else {
        eprintln!(
            "kv lazy-closure: shard for `{module}` has no resolvable .olean on the \
             closure search paths — left UNVERIFIED (=> eager for its names)."
        );
        return Some(false);
    };

    // Recompute the source-olean digest (read + blake3 ONLY — never an Expr
    // parse, never the mmap'd arena) and compare to the header.
    let (recomputed_hash, recomputed_len) = match source_olean_digest(&olean) {
        Ok(d) => d,
        Err(e) => {
            eprintln!(
                "kv lazy-closure: hashing `{}` failed: {e} — UNVERIFIED.",
                olean.display()
            );
            return Some(false);
        }
    };
    if recomputed_hash != hdr_hash || recomputed_len != hdr_len {
        eprintln!(
            "kv lazy-closure: source-olean MISMATCH for module `{module}` \
             (shard is stale/swapped vs on-disk .olean) — UNVERIFIED (=> eager)."
        );
        return Some(false);
    }

    // SUBSET CHECK (defeats foreign-constant laundering): every served name in
    // this reader must be DECLARED by the resolved olean for `module`. We
    // re-derive the declared-name SET straight from that olean (a names-only
    // walk of its constant table) rather than a namespace-prefix heuristic,
    // because a module legitimately declares differently-namespaced top-level
    // names (e.g. `identity`, `id_id`). A name not in the olean's own decls is
    // a foreign constant laundered under a benign module — refuse. An olean
    // that fails to parse (e.g. a forged garbage file) yields no decls, so any
    // served name is rejected => unverified => eager.
    let declared: std::collections::HashSet<String> =
        match crate::lean4::olean::olean_bridge::parse_target_module_with_proofs(&olean) {
            Ok(parsed) => parsed.constants.iter().map(|c| c.name.clone()).collect(),
            Err(e) => {
                eprintln!(
                    "kv lazy-closure: parsing `{}` for the subset check failed: {e} — \
                     UNVERIFIED.",
                    olean.display()
                );
                return Some(false);
            }
        };
    let subset_ok = served_names.iter().all(|name| {
        let ok = !name.is_empty() && declared.contains(name);
        if !ok {
            eprintln!(
                "kv lazy-closure: shard `{module}` serves name `{name}` NOT declared by its \
                 olean — UNVERIFIED (foreign-constant laundering refused)."
            );
        }
        ok
    });
    if !subset_ok {
        return Some(false);
    }

    // LOAD-TIME ARENA-BINDING CHECK (the no-weaker fix). The source-olean
    // digest above binds the `.olean` BYTES eager would import, but NOT the
    // shard's own FlatExpr arena that the lazy `get()` actually materializes
    // and serves. The lazy serving path (`open_lazy` -> `from_mmap_no_checksum`)
    // SKIPS the footer blake3, so a shard with an intact, matching header but a
    // CORRUPTED / STALE / SWAPPED arena would otherwise pass every header gate,
    // be marked verified, and serve a WRONG (type, value) that `add_decl`
    // δ-reduces into a KernelVerified verdict the eager path would REJECT —
    // strictly WEAKER than eager, inside the certificate's own corruption/swap
    // threat model.
    //
    // SOUNDNESS: for EVERY served constant, re-materialize via the SAME
    // `materialize_constant_from_reader` path the loader serves and require its
    // `recon_digest` to equal the header's stamped per-constant digest. The
    // build-time oracle stamped that digest from the VERIFIED reconstruction
    // (after `verify_round_trip_equal` against the eager `ConstantInfo`), so a
    // load-time match proves the served arena reconstructs to that
    // build-time-verified content. On ANY mismatch — or a served constant
    // lacking a stamped digest, or one that fails to materialize — the shard is
    // left UNVERIFIED: `get()` refuses => coverage miss => HARD EAGER FALLBACK.
    // This is what makes `recon_digest` a REAL load-time gate (it had zero
    // load-time callers before), binding the served arena to the verified
    // content. The digest is 64-bit, so it detects accidental corruption /
    // bit-rot / partial-write / arena-swap (collision ~2^-64). A FULLY-MALICIOUS
    // attacker who controls the shard bytes can recompute a matching digest
    // (the bytes also carry `_pad2`); that case stays out-of-scope (no signing
    // key) — exactly as the no-weaker certificate states.
    let arena_ok = {
        let Some(reader) = source.reader(shard) else {
            return Some(false);
        };
        reader
            .constants
            .iter()
            .enumerate()
            .filter(|(_, c)| crate::closure_source::servable_kind(c.decl_kind))
            .all(|(idx, c)| {
                let Some(stamped) = c.recon_digest() else {
                    eprintln!(
                        "kv lazy-closure: shard `{module}` served constant #{idx} has NO \
                             recon_digest — UNVERIFIED (=> eager)."
                    );
                    return false;
                };
                match crate::closure_source::materialize_constant_from_reader(reader, idx as u32) {
                    Some(rc) if recon_digest_of(&rc) == stamped => true,
                    Some(_) => {
                        eprintln!(
                            "kv lazy-closure: shard `{module}` constant #{idx} arena \
                                 reconstructs to a recon_digest != the stamped one \
                                 (corrupted/stale/swapped arena) — UNVERIFIED (=> eager)."
                        );
                        false
                    }
                    None => {
                        eprintln!(
                            "kv lazy-closure: shard `{module}` constant #{idx} failed to \
                                 materialize at load time — UNVERIFIED (=> eager)."
                        );
                        false
                    }
                }
            })
    };
    if !arena_ok {
        return Some(false);
    }

    // Full match: this shard's content is byte-bound to the on-disk olean
    // eager would import, only serves names that olean declares, AND every
    // served constant's arena reconstructs to the build-time-verified content
    // (recon_digest match). Mark it.
    source.mark_shard_verified(shard);
    Some(true)
}

/// Coverage check for the HYBRID lazy closure (step 3 of the Phase-1 wiring).
///
/// Returns `true` iff every name in each target's TRANSITIVE `Const`-reference
/// closure is resolvable without the dropped eager definitional constants:
/// either served by the lazy `source`, present eagerly in `env` (inductive
/// families, prelude, Quot, structure metadata), or a TARGET name the shard
/// replay will re-mint. Transitive expansion follows references found in the
/// types/values the lazy source materializes (and in eager constants), so a
/// definitional dep of a definitional dep is checked too.
///
/// On a miss it logs the first few unresolved names (diagnostic) and returns
/// `false`; the caller then hard-falls-back to the fully-eager loader, so a lazy
/// run can never silently lose a verdict.
pub(crate) fn lazy_closure_covers_targets(
    env: &Environment,
    source: &ShardConstantSource,
    targets: &[PathBuf],
    root: &Path,
) -> bool {
    let missing = lazy_closure_missing_names(env, source, targets, root);
    if !missing.is_empty() {
        eprintln!(
            "kv lazy-closure coverage MISS: {} name(s) unresolved (hard-falling-back to eager); first few: {}",
            missing.len(),
            missing
                .iter()
                .take(8)
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        return false;
    }
    true
}

/// The transitive `Const`-reference names a target needs that resolve NEITHER
/// eagerly (in `env`: inductive families, prelude, quotients) NOR lazily (in
/// `source`) NOR as a target-declared (replay-reminted) name. Empty ⇒ full
/// coverage. The PARAGON base uses the returned names to eager-load their owning
/// modules (bounded coverage repair) before falling back to fully-eager.
pub(crate) fn lazy_closure_missing_names(
    env: &Environment,
    source: &ShardConstantSource,
    targets: &[PathBuf],
    root: &Path,
) -> Vec<Name> {
    // BFS over the transitive Const closure, seeded by every target's own decls.
    // `scratch` is reused per node so we allocate one set, not one per term.
    let mut visited: std::collections::HashSet<Name> = std::collections::HashSet::new();
    let mut worklist: Vec<Name> = Vec::new();
    let mut missing: Vec<Name> = Vec::new();
    let mut scratch: std::collections::HashSet<Name> = std::collections::HashSet::new();
    // The names the TARGET modules themselves DECLARE. A reference to any of these
    // is re-minted by the shard replay (targets are deliberately excluded from the
    // closure), so it is NOT a coverage miss — regardless of the constant's
    // NAMESPACE (a target module may declare `Exists.fst`, `Classical.foo._proof_1`,
    // …, which are not under the target's MODULE-name prefix). Built from the
    // target shards' own constant tables, so it is exact, not a prefix heuristic.
    let mut target_decl_names: std::collections::HashSet<Name> = std::collections::HashSet::new();

    let push_refs = |ty: &clean_kernel::expr::Expr,
                     val: &Option<clean_kernel::expr::Expr>,
                     scratch: &mut std::collections::HashSet<Name>,
                     worklist: &mut Vec<Name>| {
        scratch.clear();
        ty.collect_constants_into(scratch);
        if let Some(v) = val {
            v.collect_constants_into(scratch);
        }
        worklist.extend(scratch.iter().cloned());
    };

    // Seed from the target shards' declared constants, and record every target-
    // declared NAME (the replay re-mints these).
    let _ = root; // module/name resolution is by the target shards' own tables now.
    for target in targets {
        match crate::lean4::olean::olean_bridge::convert_olean_to_mathverse(target) {
            Ok((buf, _)) => match crate::shard::ShardReader::from_bytes(&buf) {
                Ok(reader) => {
                    for c in &reader.constants {
                        if let Some(rc_name) = reader.strings.get(c.name_idx as usize) {
                            target_decl_names.insert(Name::from_string(rc_name));
                            // Walk the target decl's reconstructed type/value for
                            // its Const references — these are the closure seeds.
                            if let Ok(rc) =
                                crate::inductive_replay::reconstruct_constant(rc_name, &reader, c)
                            {
                                push_refs(
                                    &rc.type_expr,
                                    &rc.value_expr,
                                    &mut scratch,
                                    &mut worklist,
                                );
                            }
                        }
                    }
                }
                // A target we cannot even read as a shard means the eager path is
                // the only sound option. Signal an UNREPAIRABLE miss (a synthetic
                // name absent from any dropped-const map) so the caller hard-falls-
                // back rather than serving a partial closure.
                Err(_) => return vec![Name::from_string("<paragon:target-shard-unreadable>")],
            },
            Err(_) => return vec![Name::from_string("<paragon:target-convert-failed>")],
        }
    }

    while let Some(name) = worklist.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        // A target's own decl, re-minted by the replay — never a miss. Checked
        // FIRST so a target decl that happens to share a name with a closure
        // constant is still treated as the fresh, re-minted one.
        if target_decl_names.contains(&name) {
            continue;
        }
        // Eager: inductive families, constructors, recursors, quotients, and the
        // prelude live in the eager tables. The lazy source is not yet installed,
        // so consult it explicitly. Both Eager and Lazy carry (type, value) for
        // transitive expansion.
        if let Some(ci) = env.get_const(&name) {
            push_refs(&ci.type_, &ci.value, &mut scratch, &mut worklist);
        } else if env.get_inductive(&name).is_some()
            || env.get_constructor(&name).is_some()
            || env.get_recursor(&name).is_some()
        {
            // Inductive-family member: resolvable; its dep closure is owned by the
            // kernel's add_inductive path (eager families are fully resident).
        } else if let Some(ci) = source.get(&name) {
            push_refs(&ci.type_, &ci.value, &mut scratch, &mut worklist);
        } else {
            missing.push(name);
        }
    }

    missing.sort();
    missing.dedup();
    missing
}

/// Format the closure-load failure reason, annotating the bounded-loader cap so
/// the operator knows to pick a more foundational target rather than chase a
/// missing module.
fn closure_load_reason(import_name: &str, err: &ImportError) -> String {
    match err {
        ImportError::UnsupportedModule { reason, .. }
            if reason.contains("bounded loader limit") =>
        {
            format!(
                "import `{import_name}`: transitive closure exceeds the {}-module \
                 cap — raise CLEAN_MAX_CLOSURE_MODULES or pick a more foundational target module ({reason})",
                max_closure_modules()
            )
        }
        other => format!("import `{import_name}`: {other}"),
    }
}

/// Discover sibling lake-package `.olean` roots so a Mathlib closure can resolve
/// dependency packages (Batteries, Aesop, Qq, Plausible, …) that live in
/// separate `.lake/packages/<pkg>/.lake/build/lib/lean` trees rather than under
/// the project's own `build/lib/lean` root.
///
/// Walks up from `closure_root` and enumerates `packages/*/.lake/build/lib/lean`
/// and `packages/*/build/lib/lean` under **every** enclosing `.lake` directory,
/// not just the innermost. Returns only directories that exist. Best-effort: any
/// unreadable layer is skipped silently (the caller still has the prelude +
/// stdlib paths).
///
/// WHY every `.lake`, not the first: when Mathlib is itself a *dependency*, the
/// closure root is `<proj>/.lake/packages/mathlib/.lake/build/lib/lean`. Its
/// innermost enclosing `.lake` is Mathlib's own, whose `packages/*` are
/// SOURCE-ONLY checkouts with no compiled `build/lib/lean` (Lake hoists the built
/// dependency oleans to the OUTER project's `.lake/packages/*/.lake/build/lib/lean`).
/// Stopping at the first `.lake` therefore finds no sibling oleans and leaves
/// `Batteries`/`Aesop`/`Qq`/… unresolved — e.g. `congr_arg₂` (Batteries), which
/// the per-constant walk needs to kernel-check `taylor_mean_remainder_lagrange`.
/// Scanning every `.lake` ancestor and keeping only existing build dirs covers
/// both the hoisted-outer and the self-contained-inner layouts; the
/// `candidate.is_dir()` filter drops the source-only inner checkouts for free.
fn discover_lake_package_olean_roots(closure_root: &Path) -> Vec<PathBuf> {
    let mut roots = Vec::new();

    for ancestor in closure_root.ancestors() {
        if ancestor.file_name().is_none_or(|n| n != ".lake") {
            continue;
        }
        let packages_dir = ancestor.join("packages");
        let Ok(entries) = std::fs::read_dir(&packages_dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let pkg = entry.path();
            // Lake nests each dependency package's compiled oleans under its own
            // `.lake/build/lib/lean`; older layouts use a bare `build/lib/lean`.
            for rel in [".lake/build/lib/lean", "build/lib/lean"] {
                let candidate = pkg.join(rel);
                if candidate.is_dir() {
                    roots.push(candidate);
                }
            }
        }
    }
    roots.sort();
    roots.dedup();
    roots
}

/// Compute the content binding for an olean and its proof companions, used by
/// BOTH the closure-shard BUILDER (records it in the v3 header) and the LOADER
/// (recomputes it against the on-disk olean and refuses to serve on mismatch).
///
/// FRAMING (must be byte-identical build vs load): the three regions —
/// `base` (`.olean`), `private` (`.olean.private`), `server` (`.olean.server`)
/// — are concatenated in THAT fixed order, each as `u64 LE length || bytes`. An
/// absent companion contributes a length-0 region (no bytes), so a present-but-
/// empty companion and an absent one are distinguishable and unambiguous. The
/// blake3 of the whole stream is the 32-byte digest; the total stream length is
/// returned alongside as a cheap secondary tripwire.
///
/// SOUNDNESS: hashing the LENGTH-PREFIXED `.private` (the proof-carrying region
/// `parse_target_module_with_proofs` merges) binds the proof bytes, not just the
/// value-less base — a companion swap cannot be masked. The `base` path is the
/// `.olean`; `priv`/`server` are derived from it by extension, exactly as the
/// parser does, so build and load see the same companion set.
pub(crate) fn source_olean_digest(base: &Path) -> std::io::Result<([u8; 32], u64)> {
    let private = base.with_extension("olean.private");
    let server = base.with_extension("olean.server");

    let mut hasher = blake3::Hasher::new();
    let mut total: u64 = 0;
    // Read a region's bytes (absent => empty), then hash `len(u64 LE) || bytes`.
    let mut hash_region = |path: &Path, required: bool| -> std::io::Result<()> {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && !required => Vec::new(),
            Err(e) => return Err(e),
        };
        let len = bytes.len() as u64;
        hasher.update(&len.to_le_bytes());
        hasher.update(&bytes);
        total = total.saturating_add(8).saturating_add(len);
        Ok(())
    };
    hash_region(base, true)?;
    hash_region(&private, false)?;
    hash_region(&server, false)?;
    Ok((*hasher.finalize().as_bytes(), total))
}

/// Resolve a Lean module NAME (`Mathlib.Logic.Basic`) to its `.olean` file by
/// trying each search path: `<path>/Mathlib/Logic/Basic.olean`. Returns the
/// first existing match. Used by the closure-as-shards prerequisite builder.
pub(crate) fn resolve_module_olean(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel: PathBuf = module
        .split('.')
        .collect::<PathBuf>()
        .with_extension("olean");
    search_paths
        .iter()
        .map(|p| p.join(&rel))
        .find(|c| c.is_file())
}

/// Build the trusted-closure `.mathverse` shards for `target` (the
/// CLEAN_LAZY_CLOSURE prerequisite): convert every module in `target`'s
/// TRANSITIVE import closure (the target itself is EXCLUDED — its decls are
/// re-minted by the replay) into one `.mathverse` shard under `out_dir`, named
/// `<dotted.module>.mathverse`.
///
/// This mirrors the eager closure loader's resolution (same search paths) so the
/// shard set covers exactly the closure the eager `.olean` path loads. It uses
/// the same single-module converter (`convert_olean_to_mathverse`) the stamp
/// path uses, so the shard bytes are identical to what the eager olean import
/// would have reconstructed. Best-effort per module: a module that fails to
/// resolve or convert is reported but does not abort the build (the coverage
/// gate at load time is the backstop — a missing dep forces eager fallback).
///
/// Outcome of a union closure-shard build: how many closure modules were
/// converted, and the NAMES of the modules that could not be converted (so the
/// PARAGON lazy base can eagerly full-load exactly those — the shard builder's
/// parse is stricter than the eager `.olean` loader on a handful of complex
/// modules, e.g. `Mathlib.Data.Real.Basic` — closing the coverage gap that would
/// otherwise force a whole-run eager fallback).
#[derive(Debug, Default, Clone)]
pub(crate) struct ClosureShardBuild {
    /// Closure modules converted to `.mathverse` shards (the demand-paged bulk).
    pub(crate) converted: usize,
    /// Closure module NAMES the shard builder could not convert (resolve/parse
    /// failure). Their constants are absent from the shards, so the lazy base
    /// must supply them another way (eager full-load) or the coverage gate fails.
    pub(crate) skipped_modules: Vec<String>,
    /// `dropped constant name -> owning module name`: SERVABLE-kind constants that
    /// the shard builder dropped PER-CONSTANT (convert/serialize failure or
    /// value-less) inside an otherwise-converted module. They are absent from the
    /// shards, so if a target references one the lazy base must eager-load its
    /// owning module. Captured for free during the build (the names are already
    /// parsed) so the bounded coverage repair needs no extra olean parse.
    pub(crate) dropped_const_modules: std::collections::HashMap<String, String>,
}

/// Returns `(modules_converted, modules_skipped)`.
pub(crate) fn build_closure_shards_for_target(
    target: &Path,
    root: &Path,
    out_dir: &Path,
) -> Result<(usize, usize), MathverseCliError> {
    // Sequential single-target semantics: EXCLUDE the target (its decls are
    // re-minted by the replay against the closure).
    let b = build_closure_shards_for_targets(&[target.to_path_buf()], root, out_dir, true)?;
    Ok((b.converted, b.skipped_modules.len()))
}

/// PARAGON variant of [`build_closure_shards_for_target`]: build the
/// trusted-closure `.mathverse` shards for the UNION of every target's
/// transitive import closure in ONE walk.
///
/// The PARAGON base re-verifies every target against ONE shared closure, so it
/// needs ONE shard set covering the union of all targets' closures. Doing the
/// BFS once over a single shared `visited` set means a module imported by many
/// targets is converted exactly once (the closure-cache win), instead of once
/// per target.
///
/// `exclude_targets` controls whether the TARGET modules themselves are shard-
/// built:
/// - `true` (sequential single-target semantics): targets are pre-excluded;
///   their decls are re-minted by the replay against the closure.
/// - `false` (PARAGON multi-target): targets ARE shard-built too, because in a
///   subtree the targets DEPEND ON EACH OTHER — module B's proof references
///   module A's constants, and the eager `build_base_env` carries every target,
///   so the lazy base must serve sibling-target constants as well. The replay
///   still re-mints each target from its OWN target-output shard and checks it;
///   the closure shards just make a sibling target's constants available as a
///   trusted DEPENDENCY (byte-identical to the eager base carrying it).
///
/// Returns the converted count + the skipped module NAMES across the whole union.
pub(crate) fn build_closure_shards_for_targets(
    targets: &[PathBuf],
    root: &Path,
    out_dir: &Path,
    exclude_targets: bool,
) -> Result<ClosureShardBuild, MathverseCliError> {
    let search_paths = build_closure_search_paths(root);
    build_closure_shards_for_targets_with_search_paths(
        targets,
        root,
        &search_paths,
        out_dir,
        exclude_targets,
    )
}

/// Like [`build_closure_shards_for_targets`] but resolves modules against EXPLICIT
/// `search_paths` instead of re-deriving them from `root` via
/// [`build_closure_search_paths`]. The content-addressed graduate cache populate
/// uses this so each shard's source-olean BINDING is stamped against the SAME
/// `.olean` the eager/warm loader will import (the `lean-toolchain`-pinned path),
/// not whatever copy `default_search_paths()` happens to surface first. With
/// several toolchains installed, the re-derived paths can resolve a core module
/// (`Init.*`/`Lean.*`/`Std.*`) to a DIFFERENT toolchain's `.olean`, whose digest
/// then mismatches the live one the warm load binds — a spurious, permanent warm
/// MISS. `root` is still used only to name targets via `module_name_from_path`.
pub(crate) fn build_closure_shards_for_targets_with_search_paths(
    targets: &[PathBuf],
    root: &Path,
    search_paths: &[PathBuf],
    out_dir: &Path,
    exclude_targets: bool,
) -> Result<ClosureShardBuild, MathverseCliError> {
    use std::collections::VecDeque;

    std::fs::create_dir_all(out_dir)?;

    // BFS the transitive import closure over one shared `visited` set. When
    // `exclude_targets`, pre-seed target names so they never enter the shards
    // (sequential re-mint semantics). Otherwise the targets are enqueued below so
    // their own shards are built too (PARAGON inter-target dependency serving).
    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    if exclude_targets {
        for target in targets {
            visited.insert(module_name_from_path(target, root));
        }
    } else {
        for target in targets {
            queue.push_back(module_name_from_path(target, root));
        }
    }
    for target in targets {
        let target_module = module_name_from_path(target, root);
        let target_bytes = std::fs::read(target).map_err(|e| MathverseCliError::StampClosure {
            module: target_module.clone(),
            reason: format!("read {}: {e}", target.display()),
        })?;
        for import in
            parse_imports_only(&target_bytes).map_err(|e| MathverseCliError::StampClosure {
                module: target_module.clone(),
                reason: format!("parse imports: {e}"),
            })?
        {
            let nm = import.module_name.trim().to_string();
            if !nm.is_empty() {
                queue.push_back(nm);
            }
        }
    }

    let mut converted = 0usize;
    let mut skipped_modules: Vec<String> = Vec::new();
    let mut dropped_const_modules: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    while let Some(module) = queue.pop_front() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let Some(olean) = resolve_module_olean(&module, search_paths) else {
            eprintln!("build-closure-shards: skip `{module}` (no .olean on search paths)");
            skipped_modules.push(module);
            continue;
        };
        // Enqueue this module's own imports BEFORE converting, so the walk is
        // complete even if conversion fails.
        if let Ok(bytes) = std::fs::read(&olean) {
            if let Ok(imports) = parse_imports_only(&bytes) {
                for import in imports {
                    let nm = import.module_name.trim().to_string();
                    if !nm.is_empty() && !visited.contains(&nm) {
                        queue.push_back(nm);
                    }
                }
            }
        }
        match build_kernel_faithful_shard(&olean, &module) {
            Ok((buf, dropped)) => {
                let shard_path = out_dir.join(format!("{module}.mathverse"));
                std::fs::write(&shard_path, &buf)?;
                converted += 1;
                // Record each per-constant drop's owning module so the lazy base
                // can eager-load it on a coverage miss (bounded repair).
                for name in dropped {
                    dropped_const_modules
                        .entry(name)
                        .or_insert_with(|| module.clone());
                }
            }
            Err(e) => {
                eprintln!("build-closure-shards: skip `{module}` (convert: {e})");
                skipped_modules.push(module);
            }
        }
    }
    Ok(ClosureShardBuild {
        converted,
        skipped_modules,
        dropped_const_modules,
    })
}

/// Build a `.mathverse` shard for one module whose reconstructed `Expr`s are
/// FAITHFUL to the EAGER olean import — the Phase-1 parity fix (== L2).
///
/// The legacy `convert_olean_to_mathverse` path lowered each `ParsedExpr` to a
/// `FlatExpr` via `LoweringCtx::lower_expr`, a SECOND, divergent encoder: it
/// stripped `MData`, truncated `Nat > u64`, and otherwise produced trees that
/// differ structurally from the eager `convert_expr_direct` import on ~12% of
/// constants (diag_routed_env_diff: struct_value_diff≈13.8k over the closure),
/// which flipped 7/355 KernelVerified verdicts on Mathlib/Logic/Basic.
///
/// This path instead loads the module's OWN declarations through the SAME
/// kernel-faithful converter the eager loader uses (`load_parsed_module` →
/// `convert_expr`), yielding kernel `ConstantInfo`s identical to eager, then
/// serializes each via `KernelShardBuilder` (kernel `Expr` → `FlatBuilder` →
/// shard). Reconstructing such a shard reproduces the eager `Expr` exactly
/// (modulo `MData`, which `is_def_eq` strips, so verdict-transparent), pinned by
/// `single_subdag_matches_full_reconstruct` for the round-trip. Inductives /
/// constructors / recursors are served EAGERLY by the HYBRID loader, so a
/// definitional-kind-only shard is sufficient and the lazy `get_const` resolves
/// every name (eager inductive families + prelude first, then this shard).
/// Build the `Declaration` the shard serializer needs from a kernel
/// `ConstantInfo`. Returns `None` for a value-less Definition/Theorem/Opaque
/// (not servable). The ConstantInfo's reducibility is carried separately into
/// the shard header (the Declaration's `is_reducible` bool cannot represent
/// `Regular(height)`).
fn constant_info_to_declaration(
    ci: &clean_kernel::env::ConstantInfo,
) -> Option<clean_kernel::env::Declaration> {
    use clean_kernel::env::{ConstantKind, Declaration};
    Some(match ci.kind {
        ConstantKind::Definition => Declaration::Definition {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
            value: ci.value.clone()?,
            is_reducible: ci.is_reducible,
        },
        ConstantKind::Theorem => Declaration::Theorem {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
            value: ci.value.clone()?,
        },
        ConstantKind::Opaque => Declaration::Opaque {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
            value: ci.value.clone()?,
        },
        ConstantKind::Axiom => Declaration::Axiom {
            name: ci.name.clone(),
            level_params: ci.level_params.clone(),
            type_: ci.type_.clone(),
        },
    })
}

/// Build a module's kernel-faithful shard, returning the shard bytes AND the
/// names of any constant the shard does NOT serve for a coverage-relevant reason
/// (a non-servable-kind convert failure, or a value-less Def/Thm/Opaque). Those
/// names are absent from the shard, so the PARAGON lazy base must eager-load their
/// owning module or the coverage gate falls back. Inductive-family members and
/// compiler-IR names are NOT counted as dropped — they are served eagerly by
/// design, not via the shard. SERVABLE, value-bearing constants are FAIL-CLOSED:
/// a convert/add/round-trip failure on one aborts the whole module's shard (Err)
/// rather than silently dropping it (the v3 soundness hardening below).
fn build_kernel_faithful_shard(
    olean: &Path,
    module: &str,
) -> Result<(Vec<u8>, Vec<String>), MathverseCliError> {
    use crate::export::kernel_export::KernelShardBuilder;
    use crate::types::SourceSystem;

    let stamp_err = |reason: String| MathverseCliError::StampClosure {
        module: module.to_string(),
        reason,
    };

    let parsed = crate::lean4::olean::olean_bridge::parse_target_module_with_proofs(olean)
        .map_err(|e| stamp_err(format!("parse: {e}")))?;

    // Convert each of the module's OWN non-inductive declarations through the
    // SAME `convert_expr` path the eager olean import uses, WITHOUT environment
    // registration. Inductives / constructors / recursors are served EAGERLY by
    // the HYBRID loader, so they are skipped here.
    //
    // FAIL-CLOSED (Step 6): a constant that becomes `add_declaration`'d is a
    // SERVED constant (servable_kind + value-bearing). For those, convert/add
    // errors PROPAGATE as StampClosure (no silent drop) — the eager path would
    // serve them, so a shard that cannot faithfully carry them must not claim to.
    // Inductive families (Ok(None)) and value-less Def/Thm/Opaque are legitimately
    // not served (the eager inductive/coverage paths own them), so they are skipped.
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Lean4);
    // Coverage-relevant constants the shard does NOT serve (non-servable convert
    // failures + value-less Def/Thm/Opaque): returned so the PARAGON base can
    // eager-load their owning module (bounded coverage repair).
    let mut dropped: Vec<String> = Vec::new();
    // (const_idx, source ConstantInfo) for every served constant — checked by the
    // build-time round-trip oracle after serialization.
    let mut served: Vec<(u32, clean_kernel::env::ConstantInfo)> = Vec::new();
    for constant in &parsed.constants {
        // Skip Lean compiler-IR stage decls (`._cstage1`/`._cstage2`): not
        // kernel-checkable, never enter the shard (matches the legacy builder).
        if clean_olean::import::is_compiler_ir_name(&constant.name) {
            continue;
        }
        // Convert to a kernel ConstantInfo (carries the TRUE reducibility from
        // the olean hints — not just the is_reducible bool a Declaration holds).
        let ci = match clean_olean::convert_parsed_constant_to_const_info(constant) {
            // Inductive/constructor/recursor — served eagerly, not in the shard
            // (NOT a drop: the eager leg covers them).
            Ok(None) => continue,
            Ok(Some(ci)) => ci,
            Err(e) => {
                // A SERVABLE, value-bearing constant that fails to convert WOULD be
                // served by eager — fail closed (v3 soundness; no silent drop). A
                // value-less / non-servable kind is left to the eager/coverage path;
                // record it as dropped so the PARAGON bounded coverage repair can
                // eager-load its owning module. Never a wrong verdict either way.
                if servable_kind_of(&ci_kind_byte(constant)) {
                    return Err(stamp_err(format!(
                        "served constant `{}` failed convert: {e}",
                        constant.name
                    )));
                }
                dropped.push(constant.name.clone());
                continue;
            }
        };
        // Build the Declaration the shard serializer needs from the ConstantInfo.
        let decl = match constant_info_to_declaration(&ci) {
            Some(d) => d,
            // Value-less Def/Thm/Opaque (no proof value): NOT a served constant
            // (the eager/coverage path owns it). A target that references one is a
            // real coverage hole, so record it for the PARAGON bounded repair.
            None => {
                dropped.push(constant.name.clone());
                continue;
            }
        };
        // SERVED constant: an add failure is fail-closed (it cannot silently drop).
        let const_idx = builder
            .add_declaration(&decl, &[])
            .map_err(|e| stamp_err(format!("served constant `{}` failed add: {e}", ci.name)))?;
        // Record the EXACT eager reducibility so the lazily-served ConstantInfo
        // δ-unfolds identically. ASSERT it round-tripped into the header (never the
        // legacy decl_kind heuristic) before trusting it.
        if !builder
            .shard_writer_mut()
            .set_constant_reducibility(const_idx, ci.reducibility)
        {
            return Err(stamp_err(format!(
                "served constant `{}`: set_constant_reducibility out of range",
                ci.name
            )));
        }
        // Persist the Lean `DefinitionSafety` flag (`_pad2[25]`) alongside the
        // reducibility so the kernel-faithful shard carries the same trust
        // metadata as the heuristic converter's shards (an `unsafe def` must
        // never silently read back as safe).
        if let Some(safety) = constant.definition_safety {
            if !builder
                .shard_writer_mut()
                .set_constant_definition_safety(const_idx, safety)
            {
                return Err(stamp_err(format!(
                    "served constant `{}`: set_constant_definition_safety out of range",
                    ci.name
                )));
            }
        }
        served.push((const_idx, ci));
    }

    // Serialize once; the oracle re-opens THESE bytes (not the in-RAM arena).
    let bytes = builder
        .write_to_bytes()
        .map_err(|e| stamp_err(format!("write shard: {e}")))?;

    // BUILD-TIME ROUND-TRIP ORACLE (Step 6): re-open the SERIALIZED bytes via the
    // exact mmap reader the lazy loader uses, then for EVERY served constant run
    // the EXACT materialize() path and assert it verdict-equals the source `ci` on
    // the historically verdict-flipping axes. A single failure => StampClosure
    // (the whole module's shard is un-served). Only on full success do we stamp
    // recon digests + set fail_closed_verified.
    let reader = crate::shard::ShardMmapReader::open_lazy_from_bytes(&bytes)
        .map_err(|e| stamp_err(format!("oracle reopen: {e}")))?;

    // Verify reducibility category + the header-recorded reducibility matches.
    let mut digests: Vec<(u32, [u8; 8])> = Vec::with_capacity(served.len());
    for (const_idx, ci) in &served {
        // Header must carry the recorded reducibility (never the legacy heuristic).
        let header = reader
            .constants
            .get(*const_idx as usize)
            .ok_or_else(|| stamp_err(format!("oracle: const #{const_idx} missing on reopen")))?;
        if header.reducibility() != Some(ci.reducibility) {
            return Err(stamp_err(format!(
                "served constant `{}`: header reducibility {:?} != source {:?}",
                ci.name,
                header.reducibility(),
                ci.reducibility
            )));
        }
        let rc = crate::closure_source::materialize_constant_from_reader(&reader, *const_idx)
            .ok_or_else(|| {
                stamp_err(format!(
                    "served constant `{}`: oracle materialize failed",
                    ci.name
                ))
            })?;
        verify_round_trip_equal(ci, &rc).map_err(stamp_err)?;
        digests.push((*const_idx, recon_digest_of(&rc)));
    }
    drop(reader);

    // Re-stamp the verified shard: write the per-constant recon digests and flip
    // fail_closed_verified=1, plus the source-olean content binding + module name,
    // then re-serialize. Only NOW is the shard servable on the lazy path.
    for (const_idx, digest) in &digests {
        if !builder
            .shard_writer_mut()
            .set_constant_recon_digest(*const_idx, *digest)
        {
            return Err(stamp_err(format!(
                "set_constant_recon_digest out of range for #{const_idx}"
            )));
        }
    }
    let (src_hash, src_len) =
        source_olean_digest(olean).map_err(|e| stamp_err(format!("source-olean hash: {e}")))?;
    let writer = builder.shard_writer_mut();
    writer.set_source_olean_digest(src_hash, src_len);
    writer.set_module_name(module);
    writer.set_fail_closed_verified(true);
    let bytes = builder
        .write_to_bytes()
        .map_err(|e| stamp_err(format!("write verified shard: {e}")))?;
    Ok((bytes, dropped))
}

/// The `DeclKind` byte for a parsed olean constant, used to decide whether a
/// CONVERT FAILURE was on a constant the lazy path would serve (fail-closed) or
/// one it never serves (skip). Mirrors the kernel's kind mapping; on any
/// uncertainty it errs toward "served" so a convert failure fails closed.
fn ci_kind_byte(constant: &clean_olean::ParsedConstant) -> u8 {
    use crate::types::DeclKind;
    use clean_olean::ConstantKind as OleanKind;
    match constant.kind {
        OleanKind::Definition => DeclKind::Definition as u8,
        OleanKind::Theorem => DeclKind::Theorem as u8,
        OleanKind::Opaque => DeclKind::Opaque as u8,
        OleanKind::Axiom => DeclKind::Axiom as u8,
        // Inductive families / quotient — not lazily served.
        _ => DeclKind::Inductive as u8,
    }
}

/// `servable_kind` over a `DeclKind` byte (delegates to the closure source's
/// canonical hybrid filter so the builder's fail-closed decision matches what
/// the loader actually serves).
fn servable_kind_of(kind_byte: &u8) -> bool {
    crate::closure_source::servable_kind(*kind_byte)
}

/// Verdict-equality of a source `ConstantInfo` and its round-tripped (serialize
/// -> mmap-reparse -> materialize) reconstruction, on the historically
/// verdict-flipping axes ONLY:
/// - reducibility CATEGORY (Regular vs Opaque vs Reducible vs Irreducible),
/// - kind,
/// - level_params,
/// - FVar-freeness (a stored constant must be FVar-free; an FVar hashes
///   differently eager-vs-lazy and breaks defeq),
/// - type/value modulo MData + binder-info (which is_def_eq provably strips),
///   via `types_equal_ignoring_binder_info`.
fn verify_round_trip_equal(
    src: &clean_kernel::env::ConstantInfo,
    rc: &clean_kernel::env::ConstantInfo,
) -> Result<(), String> {
    if reducibility_category(src.reducibility) != reducibility_category(rc.reducibility) {
        return Err(format!(
            "`{}`: reducibility category {:?} != {:?}",
            src.name, src.reducibility, rc.reducibility
        ));
    }
    if src.kind != rc.kind {
        return Err(format!(
            "`{}`: kind {:?} != {:?}",
            src.name, src.kind, rc.kind
        ));
    }
    if src.level_params != rc.level_params {
        return Err(format!(
            "`{}`: level_params {:?} != {:?}",
            src.name, src.level_params, rc.level_params
        ));
    }
    if expr_has_fvar(&src.type_) || expr_has_fvar(&rc.type_) {
        return Err(format!("`{}`: FVar in type (not FVar-free)", src.name));
    }
    if !crate::inductive_replay::types_equal_ignoring_binder_info(&src.type_, &rc.type_) {
        return Err(format!("`{}`: type differs structurally", src.name));
    }
    match (&src.value, &rc.value) {
        (Some(sv), Some(rv)) => {
            if expr_has_fvar(sv) || expr_has_fvar(rv) {
                return Err(format!("`{}`: FVar in value (not FVar-free)", src.name));
            }
            if !crate::inductive_replay::types_equal_ignoring_binder_info(sv, rv) {
                return Err(format!("`{}`: value differs structurally", src.name));
            }
        }
        (None, None) => {}
        _ => return Err(format!("`{}`: value presence differs", src.name)),
    }
    Ok(())
}

/// The verdict-relevant reducibility CATEGORY (the `Regular` height is
/// verdict-neutral, so all `Regular(_)` collapse to one category).
fn reducibility_category(r: clean_kernel::env::Reducibility) -> u8 {
    use clean_kernel::env::Reducibility;
    match r {
        Reducibility::Reducible => 0,
        Reducibility::Regular(_) => 1,
        Reducibility::Irreducible => 2,
        Reducibility::Opaque => 3,
    }
}

/// blake3-truncated (8-byte) digest of a reconstructed `ConstantInfo`'s
/// type/value/kind/reducibility — a CORRUPTION tripwire only.
fn recon_digest_of(rc: &clean_kernel::env::ConstantInfo) -> [u8; 8] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(rc.name.to_string().as_bytes());
    hasher.update(format!("{:?}", rc.kind).as_bytes());
    hasher.update(format!("{:?}", rc.reducibility).as_bytes());
    hasher.update(format!("{:?}", rc.type_).as_bytes());
    if let Some(v) = &rc.value {
        hasher.update(format!("{v:?}").as_bytes());
    }
    let full = hasher.finalize();
    let mut out = [0u8; 8];
    out.copy_from_slice(&full.as_bytes()[..8]);
    // Avoid the all-zero sentinel (== unset) on the astronomically unlikely
    // collision: flip the low bit so a real digest is never decoded as "unset".
    if out == [0u8; 8] {
        out[0] = 1;
    }
    out
}

/// Whether an expr tree contains an FVar node (a stored constant must be
/// FVar-free; an FVar hashes differently eager-vs-lazy and breaks defeq).
fn expr_has_fvar(e: &clean_kernel::expr::Expr) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut stack = vec![e];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            ExprKind::FVar(_) => return true,
            ExprKind::App(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.push(t);
                stack.push(b);
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(t);
                stack.push(v);
                stack.push(b);
            }
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => stack.push(x),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod closure_shard_build_tests {
    use super::*;

    /// DIAGNOSTIC + PINPOINT for the remaining Phase-1 gap (opt-in): for EVERY
    /// name the lazy source serves, compare its shard-reconstructed `ConstantInfo`
    /// to the eager olean-import one and report where type or value differ. This
    /// is the canonical reproduction of the olean-import vs shard-reconstruct
    /// Expr-identity gap (BinderInfo / Multiplicity fidelity in the
    /// `.olean -> .mathverse` builder) that makes 7/355 KernelVerified names
    /// diverge on Mathlib/Logic/Basic — the documented remaining work before
    /// CLEAN_LAZY_CLOSURE can default ON. Drive with KV_DIFF_TARGET / KV_DIFF_ROOT
    /// / KV_DIFF_SHARDS. Skips green when unset.
    #[test]
    fn diag_diff_eager_vs_lazy_consts() {
        let (Ok(target), Ok(root), Ok(shards)) = (
            std::env::var("KV_DIFF_TARGET"),
            std::env::var("KV_DIFF_ROOT"),
            std::env::var("KV_DIFF_SHARDS"),
        ) else {
            return;
        };
        // Eager olean closure (all kinds), and the lazy shard source.
        let eager = load_targets_closure(
            &[PathBuf::from(&target)],
            Path::new(&root),
            ProofValueElision::None,
        )
        .expect("eager closure");
        let source = ShardConstantSource::from_dir(Path::new(&shards)).expect("lazy source");

        let names = source.servable_names();
        let (mut checked, mut type_diff, mut value_diff, mut eager_missing) =
            (0u64, 0u64, 0u64, 0u64);
        // Diffs that survive binder-info canonicalization are the TRUE
        // verdict-affecting candidates (defeq is binder-blind, so binder-only
        // diffs are noise). Track them separately.
        let (mut struct_type_diff, mut struct_value_diff) = (0u64, 0u64);
        let mut shown = 0u32;
        let mut struct_shown = 0u32;
        // Optional focus: KV_DIFF_ONLY=comma,separated,names restricts the
        // structural dump to a specific set (e.g. the 7 eager-only decls).
        let focus: Option<Vec<String>> = std::env::var("KV_DIFF_ONLY")
            .ok()
            .map(|s| s.split(',').map(|x| x.trim().to_string()).collect());
        // FVar smoking-gun scan: a STORED constant should be FVar-free; an FVar
        // in a reconstructed closure constant is hashed by a DIFFERENT function
        // eager vs lazy (ahash fixed-seed vs std DefaultHasher), so its identity
        // diverges and breaks defeq for any dependent. Count & show them.
        fn has_fvar(e: &clean_kernel::expr::Expr) -> bool {
            use clean_kernel::expr::ExprKind;
            let mut stack = vec![e.clone()];
            while let Some(cur) = stack.pop() {
                match cur.kind() {
                    ExprKind::FVar(_) => return true,
                    ExprKind::App(a, b) => {
                        stack.push(a.as_ref().clone());
                        stack.push(b.as_ref().clone());
                    }
                    ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                        stack.push(t.as_ref().clone());
                        stack.push(b.as_ref().clone());
                    }
                    ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => {
                        stack.push(x.as_ref().clone());
                    }
                    ExprKind::Let(_, t, v, b, _) => {
                        stack.push(t.as_ref().clone());
                        stack.push(v.as_ref().clone());
                        stack.push(b.as_ref().clone());
                    }
                    _ => {}
                }
            }
            false
        }
        // PARITY PINPOINT: walk eager vs lazy Expr in parallel and return a
        // description of the FIRST differing ExprKind node (kind tags + path +
        // the two differing operands). Binder-info differences are skipped
        // (defeq is binder-blind) so the result names a VERDICT-RELEVANT diff.
        fn first_expr_diff(
            eag: &clean_kernel::expr::Expr,
            lazy: &clean_kernel::expr::Expr,
            path: &str,
        ) -> Option<String> {
            use clean_kernel::expr::ExprKind as K;
            match (eag.kind(), lazy.kind()) {
                (K::BVar(a), K::BVar(b)) => {
                    (a != b).then(|| format!("BVar@{path}: eager={a} lazy={b}"))
                }
                (K::FVar(a), K::FVar(b)) => {
                    (a != b).then(|| format!("FVar@{path}: eager={a:?} lazy={b:?}"))
                }
                (K::Sort(a), K::Sort(b)) => {
                    (a != b).then(|| format!("Sort@{path}: eager={a:?} lazy={b:?}"))
                }
                (K::Const(na, la), K::Const(nb, lb)) => {
                    if na != nb {
                        Some(format!("Const.name@{path}: eager={na} lazy={nb}"))
                    } else if la != lb {
                        Some(format!(
                            "Const.levels@{path} (name={na}): eager={la:?} lazy={lb:?}"
                        ))
                    } else {
                        None
                    }
                }
                (K::App(fa, aa), K::App(fb, ab)) => first_expr_diff(fa, fb, &format!("{path}.fn"))
                    .or_else(|| first_expr_diff(aa, ab, &format!("{path}.arg"))),
                // Binder-info is verdict-transparent: only recurse into ty/body.
                (K::Lam(_, ta, ba), K::Lam(_, tb, bb)) | (K::Pi(_, ta, ba), K::Pi(_, tb, bb)) => {
                    first_expr_diff(ta, tb, &format!("{path}.ty"))
                        .or_else(|| first_expr_diff(ba, bb, &format!("{path}.body")))
                }
                (K::Let(_, ta, va, ba, _), K::Let(_, tb, vb, bb, _)) => {
                    first_expr_diff(ta, tb, &format!("{path}.ty"))
                        .or_else(|| first_expr_diff(va, vb, &format!("{path}.val")))
                        .or_else(|| first_expr_diff(ba, bb, &format!("{path}.body")))
                }
                (K::Lit(a), K::Lit(b)) => {
                    (a != b).then(|| format!("Lit@{path}: eager={a:?} lazy={b:?}"))
                }
                (K::Proj(na, fa, xa), K::Proj(nb, fb, xb)) => {
                    if na != nb {
                        Some(format!("Proj.name@{path}: eager={na} lazy={nb}"))
                    } else if fa != fb {
                        Some(format!(
                            "Proj.field@{path} (name={na}): eager={fa} lazy={fb}"
                        ))
                    } else {
                        first_expr_diff(xa, xb, &format!("{path}.proj_inner"))
                    }
                }
                // MData is stripped on the lazy side (FlatExpr has no MData tag);
                // is_def_eq strips it too, so peel it on either side and recurse.
                (K::MData(_, inner), _) => first_expr_diff(inner, lazy, &format!("{path}.mdata")),
                (_, K::MData(_, inner)) => first_expr_diff(eag, inner, &format!("{path}.mdata")),
                // Different ExprKind discriminants entirely.
                (a, b) => Some(format!(
                    "KIND-MISMATCH@{path}: eager={} lazy={}",
                    kind_tag(a),
                    kind_tag(b)
                )),
            }
        }
        fn kind_tag(k: &clean_kernel::expr::ExprKind) -> &'static str {
            use clean_kernel::expr::ExprKind as K;
            match k {
                K::BVar(_) => "BVar",
                K::FVar(_) => "FVar",
                K::Sort(_) => "Sort",
                K::Const(..) => "Const",
                K::App(..) => "App",
                K::Lam(..) => "Lam",
                K::Pi(..) => "Pi",
                K::Let(..) => "Let",
                K::Lit(_) => "Lit",
                K::Proj(..) => "Proj",
                K::MData(..) => "MData",
                _ => "Other",
            }
        }
        let mut fvar_consts = 0u64;
        let mut fvar_shown = 0u32;
        // Aggregate first-diff node descriptions across the whole servable set so
        // the dominant mis-encoded node type is named even without a focus filter.
        let mut first_diff_tally: std::collections::BTreeMap<String, u64> =
            std::collections::BTreeMap::new();
        let mut first_diff_examples: Vec<String> = Vec::new();
        // TARGETED full-dump: KV_DIFF_NAMES=a,b,c prints the FULL first-diff for
        // exactly these closure constants (the suspected deps of the failing
        // targets), so a single (slow) closure load yields every relevant diff.
        let diff_names: Option<Vec<String>> = std::env::var("KV_DIFF_NAMES")
            .ok()
            .map(|s| s.split(',').map(|x| x.trim().to_string()).collect());
        if let Some(want) = &diff_names {
            for want_name in want {
                let nm = Name::from_string(want_name);
                let (Some(lazy), Some(eag)) = (source.get(&nm), eager.env.get_const(&nm)) else {
                    eprintln!(
                        "TARGETED `{want_name}`: NOT BOTH SERVABLE (lazy={} eager={})",
                        source.get(&nm).is_some(),
                        eager.env.get_const(&nm).is_some()
                    );
                    continue;
                };
                let tdesc = first_expr_diff(&eag.type_, &lazy.type_, "type");
                let vdesc = match (&eag.value, &lazy.value) {
                    (Some(a), Some(b)) => first_expr_diff(a, b, "value"),
                    (None, None) => None,
                    (a, b) => Some(format!(
                        "VALUE-PRESENCE: eager={} lazy={}",
                        a.is_some(),
                        b.is_some()
                    )),
                };
                eprintln!(
                    "TARGETED `{want_name}`: type_diff={:?} value_diff={:?}\n  eager.lp={:?} lazy.lp={:?}",
                    tdesc, vdesc, eag.level_params, lazy.level_params
                );
                // Full dump when KV_DIFF_FULL is set: print both whole exprs so the
                // exact divergent subtree (App vs Pi vs BVar) is visible.
                if std::env::var("KV_DIFF_FULL").is_ok() {
                    eprintln!("  eager.type = {:?}", eag.type_);
                    eprintln!("  lazy.type  = {:?}", lazy.type_);
                    eprintln!("  eager.value = {:?}", eag.value);
                    eprintln!("  lazy.value  = {:?}", lazy.value);
                }
            }
        }
        // When KV_DIFF_NAMES is set we only want the targeted dump above; skip the
        // expensive whole-servable-set loop (115k reconstructs).
        let scan_all = diff_names.is_none();
        for name in &names {
            if !scan_all {
                break;
            }
            let Some(lazy) = source.get(name) else {
                continue;
            };
            let Some(eag) = eager.env.get_const(name) else {
                eager_missing += 1;
                continue;
            };
            checked += 1;
            // FVar smoking-gun scan.
            let lazy_fv = has_fvar(&lazy.type_) || lazy.value.as_ref().is_some_and(has_fvar);
            let eag_fv = has_fvar(&eag.type_) || eag.value.as_ref().is_some_and(has_fvar);
            if lazy_fv || eag_fv {
                fvar_consts += 1;
                if fvar_shown < 15 {
                    fvar_shown += 1;
                    eprintln!(
                        "FVAR `{name}`: eager_fvar={eag_fv} lazy_fvar={lazy_fv} kind={:?}\n  eager.type = {}\n  lazy.type  = {}",
                        eag.kind, eag.type_, lazy.type_
                    );
                }
            }
            let td = eag.type_ != lazy.type_;
            let vd = eag.value != lazy.value;
            if td {
                type_diff += 1;
            }
            if vd {
                value_diff += 1;
            }
            // Binder-info-blind structural comparison.
            let std = td
                && !crate::inductive_replay::types_equal_ignoring_binder_info(
                    &eag.type_,
                    &lazy.type_,
                );
            let svd = vd
                && match (&eag.value, &lazy.value) {
                    (Some(a), Some(b)) => {
                        !crate::inductive_replay::types_equal_ignoring_binder_info(a, b)
                    }
                    (None, None) => false,
                    _ => true, // value presence differs => structural
                };
            if std {
                struct_type_diff += 1;
            }
            if svd {
                struct_value_diff += 1;
            }
            // PARITY PINPOINT: for any structural diff, find the first differing
            // ExprKind node and tally its category (the tag@root part).
            if std || svd {
                let mut fd: Option<String> = None;
                if std {
                    fd = first_expr_diff(&eag.type_, &lazy.type_, "type");
                }
                if fd.is_none() && svd {
                    if let (Some(ev), Some(lv)) = (&eag.value, &lazy.value) {
                        fd = first_expr_diff(ev, lv, "value");
                    } else {
                        fd = Some("VALUE-PRESENCE-DIFF".to_string());
                    }
                }
                if let Some(desc) = fd {
                    // Category = text up to the first '@' or ':' (the node kind/field).
                    let cat = desc.split(['@', ':']).next().unwrap_or(&desc).to_string();
                    *first_diff_tally.entry(cat).or_insert(0) += 1;
                    if first_diff_examples.len() < 25 {
                        first_diff_examples.push(format!("{name}: {desc}"));
                    }
                }
            }
            let name_str = name.to_string();
            let is_focus = focus
                .as_ref()
                .is_none_or(|f| f.iter().any(|n| n == &name_str));
            // For the focus set ALWAYS dump full metadata, even if the only diff
            // is binder-info noise — we need to see reducibility/kind/level_params
            // which the type/value comparison does not capture.
            if is_focus && focus.is_some() {
                eprintln!(
                    "FOCUS `{name_str}`:\n  eager: kind={:?} red={:?} is_red={} lp={:?} has_val={}\n  lazy : kind={:?} red={:?} is_red={} lp={:?} has_val={}\n  td={td} vd={vd} struct_td={std} struct_vd={svd}",
                    eag.kind, eag.reducibility, eag.is_reducible, eag.level_params, eag.value.is_some(),
                    lazy.kind, lazy.reducibility, lazy.is_reducible, lazy.level_params, lazy.value.is_some(),
                );
            }
            if (std || svd) && is_focus && struct_shown < 20 {
                struct_shown += 1;
                eprintln!(
                    "STRUCT-DIFF `{name}`: type_struct_diff={std} value_struct_diff={svd}\n  eager.type = {:?}\n  lazy.type  = {:?}",
                    eag.type_, lazy.type_
                );
                if svd {
                    eprintln!(
                        "  eager.value = {:?}\n  lazy.value  = {:?}",
                        eag.value, lazy.value
                    );
                }
            }
            if (td || vd) && shown < 12 {
                shown += 1;
                eprintln!(
                    "DIFF `{name}`: type_diff={td} value_diff={vd} (struct_td={std} struct_vd={svd})",
                );
            }
        }
        eprintln!(
            "DIFF SUMMARY: checked={checked} type_diff={type_diff} value_diff={value_diff} \
             STRUCT_type_diff={struct_type_diff} STRUCT_value_diff={struct_value_diff} \
             FVAR_consts={fvar_consts} \
             eager_missing={eager_missing} (servable={})",
            names.len()
        );
        eprintln!("FIRST-DIFF NODE TALLY (verdict-relevant, binder-blind, MData-peeled):");
        for (cat, n) in &first_diff_tally {
            eprintln!("  {cat}: {n}");
        }
        eprintln!("FIRST-DIFF EXAMPLES:");
        for ex in &first_diff_examples {
            eprintln!("  {ex}");
        }
    }

    /// GATE-FAITHFUL diff (opt-in): compare what the KERNEL actually resolves in
    /// each leg — `get_const` on the fully-EAGER closure env vs the HYBRID LAZY
    /// (mmap) closure env — over every name the shard source can serve. This is
    /// the exact comparison `scripts/kv_invariance_gate.sh` rests on, so it
    /// excludes prelude/eager-inductive SHADOWING noise: a name registered in the
    /// prelude (e.g. `ite`, `Decidable.decide`) resolves to the SAME eager stub in
    /// BOTH legs and shows NO diff here, even though its raw shard bytes differ.
    /// The reported diffs are therefore exactly the constants whose lazy serving
    /// could flip a verdict. Drive with the same KV_DIFF_TARGET/ROOT/SHARDS;
    /// optional KV_DIFF_FULL dumps whole exprs. Skips green when unset.
    #[test]
    fn diag_routed_env_diff() {
        let (Ok(target), Ok(root), Ok(shards)) = (
            std::env::var("KV_DIFF_TARGET"),
            std::env::var("KV_DIFF_ROOT"),
            std::env::var("KV_DIFF_SHARDS"),
        ) else {
            return;
        };
        let eager = load_targets_closure(
            &[PathBuf::from(&target)],
            Path::new(&root),
            ProofValueElision::None,
        )
        .expect("eager closure");
        let lazy = load_targets_closure_mmap(
            &[PathBuf::from(&target)],
            Path::new(&root),
            ProofValueElision::None,
            Path::new(&shards),
        )
        .expect("lazy mmap closure load")
        .expect("lazy closure must cover targets (coverage fallback would mask the bug)");
        // The lazy source for enumerating candidate names (the routed env resolves
        // each through prelude->eager-inductive->shard, exactly like the kernel).
        let source = ShardConstantSource::from_dir(Path::new(&shards)).expect("lazy source");
        let full = std::env::var("KV_DIFF_FULL").is_ok();

        let mut checked = 0u64;
        let (mut type_diff, mut value_diff, mut presence_diff) = (0u64, 0u64, 0u64);
        let mut meta_diff = 0u64;
        let mut shown = 0u32;
        // FULL-SET classification: bucket every diverging name by its last dotted
        // component (`noConfusion`, `noConfusionType`, `rec`, …) so the dominant
        // class is named over the WHOLE servable set, not just the first 30 shown.
        let mut suffix_tally: std::collections::BTreeMap<String, u64> =
            std::collections::BTreeMap::new();
        for name in source.servable_names() {
            let (Some(e), Some(l)) = (eager.env.get_const(&name), lazy.env.get_const(&name)) else {
                continue;
            };
            checked += 1;
            let td = e.type_ != l.type_
                && !crate::inductive_replay::types_equal_ignoring_binder_info(&e.type_, &l.type_);
            let vd = match (&e.value, &l.value) {
                (Some(a), Some(b)) => {
                    a != b && !crate::inductive_replay::types_equal_ignoring_binder_info(a, b)
                }
                (None, None) => false,
                _ => {
                    presence_diff += 1;
                    true
                }
            };
            // Reducibility / kind / level-params METADATA diff: verdict-relevant
            // even when type+value are byte-identical, because the kernel's
            // δ-unfold heuristics key on `reducibility` (a `@[reducible]` def the
            // lazy side serves as `Regular(0)` reduces differently in is_def_eq).
            let red_d = e.reducibility != l.reducibility;
            let rec_d = e.is_reducible != l.is_reducible;
            let kind_d = e.kind != l.kind;
            let lp_d = e.level_params != l.level_params;
            if red_d || rec_d {
                meta_diff += 1;
            }
            if td {
                type_diff += 1;
            }
            if vd {
                value_diff += 1;
            }
            if td || vd || red_d || rec_d || kind_d || lp_d {
                let suffix = name
                    .to_string()
                    .rsplit('.')
                    .next()
                    .unwrap_or("<anon>")
                    .to_string();
                *suffix_tally.entry(suffix).or_insert(0) += 1;
            }
            if (td || vd || red_d || rec_d || kind_d || lp_d) && shown < 30 {
                shown += 1;
                eprintln!(
                    "ROUTED-DIFF `{name}`: type={td} value={vd} red={red_d} is_red={rec_d} kind={kind_d} lp={lp_d}\n  eager: red={:?} is_red={} kind={:?}\n  lazy : red={:?} is_red={} kind={:?}",
                    e.reducibility, e.is_reducible, e.kind,
                    l.reducibility, l.is_reducible, l.kind,
                );
                if full {
                    eprintln!("  eager.type = {:?}\n  lazy.type  = {:?}", e.type_, l.type_);
                    eprintln!(
                        "  eager.value = {:?}\n  lazy.value  = {:?}",
                        e.value, l.value
                    );
                }
            }
        }
        eprintln!(
            "ROUTED-DIFF SUMMARY: checked={checked} struct_type_diff={type_diff} \
             struct_value_diff={value_diff} value_presence_diff={presence_diff} \
             reducibility_or_isreducible_diff={meta_diff}"
        );
        eprintln!("ROUTED-DIFF SUFFIX TALLY (whole servable set, last dotted component):");
        let mut tally_sorted: Vec<(&String, &u64)> = suffix_tally.iter().collect();
        tally_sorted.sort_by(|a, b| b.1.cmp(a.1));
        for (suffix, n) in tally_sorted.iter().take(40) {
            eprintln!("  .{suffix}: {n}");
        }
    }

    /// TARGETED culprit-finder: for each TARGET decl named in KV_DIFF_TARGETS
    /// (comma-separated, e.g. the 7 divergent names), reconstruct it from the
    /// target olean, walk the transitive Const-closure of its type+value, and
    /// routed-compare every reachable closure constant (eager env vs lazy mmap
    /// env) — reporting any with a struct type/value/reducibility/kind diff. The
    /// FIRST such constant on a failing target's path is the verdict-breaker.
    /// Drive with KV_DIFF_TARGET/ROOT/SHARDS + KV_DIFF_TARGETS. Skips green unset.
    #[test]
    fn diag_target_culprit() {
        let (Ok(target), Ok(root), Ok(shards), Ok(want)) = (
            std::env::var("KV_DIFF_TARGET"),
            std::env::var("KV_DIFF_ROOT"),
            std::env::var("KV_DIFF_SHARDS"),
            std::env::var("KV_DIFF_TARGETS"),
        ) else {
            return;
        };
        let eager = load_targets_closure(
            &[PathBuf::from(&target)],
            Path::new(&root),
            ProofValueElision::None,
        )
        .expect("eager closure");
        let lazy = load_targets_closure_mmap(
            &[PathBuf::from(&target)],
            Path::new(&root),
            ProofValueElision::None,
            Path::new(&shards),
        )
        .expect("lazy mmap load")
        .expect("lazy must cover targets");

        // Reconstruct the named target decls from the target's own shard bytes.
        let (buf, _) =
            crate::lean4::olean::olean_bridge::convert_olean_to_mathverse(Path::new(&target))
                .expect("convert target");
        let reader = crate::shard::ShardReader::from_bytes(&buf).expect("read target shard");
        let want_names: Vec<String> = want.split(',').map(|s| s.trim().to_string()).collect();

        for wn in &want_names {
            // Seed the closure walk from the target decl's type+value Const refs.
            let mut seeds: std::collections::HashSet<Name> = std::collections::HashSet::new();
            for c in &reader.constants {
                let Some(cn) = reader.strings.get(c.name_idx as usize) else {
                    continue;
                };
                if cn != wn {
                    continue;
                }
                if let Ok(rc) = crate::inductive_replay::reconstruct_constant(cn, &reader, c) {
                    rc.type_expr.collect_constants_into(&mut seeds);
                    if let Some(v) = &rc.value_expr {
                        v.collect_constants_into(&mut seeds);
                    }
                }
            }
            // BFS the Const closure through the EAGER env; routed-compare each.
            let mut visited: std::collections::HashSet<Name> = std::collections::HashSet::new();
            let mut work: Vec<Name> = seeds.into_iter().collect();
            let mut culprits = 0u32;
            while let Some(n) = work.pop() {
                if !visited.insert(n.clone()) {
                    continue;
                }
                let (Some(e), Some(l)) = (eager.env.get_const(&n), lazy.env.get_const(&n)) else {
                    continue;
                };
                let td = e.type_ != l.type_
                    && !crate::inductive_replay::types_equal_ignoring_binder_info(
                        &e.type_, &l.type_,
                    );
                let vd = match (&e.value, &l.value) {
                    (Some(a), Some(b)) => {
                        a != b && !crate::inductive_replay::types_equal_ignoring_binder_info(a, b)
                    }
                    (None, None) => false,
                    _ => true,
                };
                let rd = e.reducibility != l.reducibility || e.is_reducible != l.is_reducible;
                if td || vd || rd {
                    culprits += 1;
                    if culprits <= 12 {
                        eprintln!(
                            "CULPRIT for `{wn}`: `{n}` type={td} value={vd} red={rd}\n    eager.red={:?} lazy.red={:?} eager.kind={:?} lazy.kind={:?}",
                            e.reducibility, l.reducibility, e.kind, l.kind
                        );
                        if std::env::var("KV_DIFF_FULL").is_ok() {
                            eprintln!("    eager.type  = {:?}", e.type_);
                            eprintln!("    lazy.type   = {:?}", l.type_);
                            eprintln!("    eager.value = {:?}", e.value);
                            eprintln!("    lazy.value  = {:?}", l.value);
                        }
                    }
                }
                // Expand through the EAGER constant's refs (full closure).
                let mut refs: std::collections::HashSet<Name> = std::collections::HashSet::new();
                e.type_.collect_constants_into(&mut refs);
                if let Some(v) = &e.value {
                    v.collect_constants_into(&mut refs);
                }
                for r in refs {
                    if !visited.contains(&r) {
                        work.push(r);
                    }
                }
            }
            eprintln!(
                "TARGET `{wn}`: closure_size={} culprits={culprits}",
                visited.len()
            );
        }
    }

    /// PREREQUISITE BUILDER (opt-in): build the trusted-closure `.mathverse`
    /// shards for one target so `scripts/kv_invariance_gate.sh` can drive the
    /// lazy leg. Drive with:
    ///   KV_BUILD_TARGET=<...>/Mathlib/Logic/Basic.olean
    ///   KV_BUILD_ROOT=<...>/.lake/build/lib/lean
    ///   KV_BUILD_OUT=<dir for the closure shards>
    /// Skips (green) when the env vars are unset. Not a unit assertion — it is a
    /// gated one-shot tool, so it only asserts the build produced at least one
    /// shard (a closure with zero deps would mean the wrong target).
    #[test]
    fn build_closure_shards_prerequisite() {
        let (Ok(target), Ok(root), Ok(out)) = (
            std::env::var("KV_BUILD_TARGET"),
            std::env::var("KV_BUILD_ROOT"),
            std::env::var("KV_BUILD_OUT"),
        ) else {
            eprintln!(
                "skip: set KV_BUILD_TARGET / KV_BUILD_ROOT / KV_BUILD_OUT to build closure shards"
            );
            return;
        };
        let (converted, skipped) =
            build_closure_shards_for_target(Path::new(&target), Path::new(&root), Path::new(&out))
                .expect("closure shard build");
        eprintln!("closure shards: converted={converted} skipped={skipped} -> {out}");
        assert!(
            converted > 0,
            "no closure modules converted (wrong target/root?)"
        );
    }

    /// One-module diagnostic: build the kernel-faithful shard for a single olean
    /// (KV_ONE_OLEAN=<path>, KV_ONE_MODULE=<dotted>) and report how many
    /// constants it serves and whether a few probe names resolve. Used to debug
    /// the Init.Prelude coverage gap. Skips green when unset.
    #[test]
    fn diag_one_module_shard() {
        let (Ok(olean), Ok(module)) = (
            std::env::var("KV_ONE_OLEAN"),
            std::env::var("KV_ONE_MODULE"),
        ) else {
            return;
        };
        match build_kernel_faithful_shard(Path::new(&olean), &module) {
            Ok((buf, _dropped)) => {
                eprintln!("ONE-MODULE `{module}`: shard bytes={}", buf.len());
                match crate::shard::ShardReader::from_bytes(&buf) {
                    Ok(r) => {
                        eprintln!("ONE-MODULE `{module}`: constants={}", r.constants.len());
                        let probes = std::env::var("KV_ONE_PROBES").unwrap_or_default();
                        for p in probes.split(',').filter(|s| !s.trim().is_empty()) {
                            let found = r
                                .constants
                                .iter()
                                .filter_map(|c| r.strings.get(c.name_idx as usize))
                                .any(|n| n == p.trim());
                            eprintln!("  probe `{}`: served={found}", p.trim());
                        }
                    }
                    Err(e) => eprintln!("ONE-MODULE `{module}`: shard read error: {e}"),
                }
            }
            Err(e) => eprintln!("ONE-MODULE `{module}`: BUILD ERROR: {e}"),
        }
    }
}
/// ALWAYS-ON tests for the v3 closure-binding fail-closed hardening, split into
/// `closure_load_v3_tests.rs` (build-time oracle + digest half) and
/// `closure_load_v3_tests_binding.rs` (load-time content/arena binding + serving
/// half) for the 500-line paragon ratchet. The `#[path]` makes each a submodule
/// of `closure_load`, so its `use super::*` resolves to this module's private
/// items.
#[cfg(test)]
#[path = "closure_load_v3_tests.rs"]
mod v3_closure_binding_tests;

#[cfg(test)]
#[path = "closure_load_v3_tests_binding.rs"]
mod v3_closure_binding_tests_binding;

#[cfg(test)]
mod sibling_discovery_tests {
    use super::discover_lake_package_olean_roots;
    use std::fs;

    /// Regression: a Mathlib-as-dependency layout has an INNER `.lake` whose
    /// `packages/*` are source-only checkouts (no `build/lib/lean`) and an OUTER
    /// project `.lake` whose `packages/*/.lake/build/lib/lean` hold the actually
    /// built dependency oleans (Batteries, Aesop, …). Discovery must scan EVERY
    /// `.lake` ancestor and return the built OUTER roots while skipping the
    /// source-only inner ones — otherwise `congr_arg₂` (Batteries) never resolves
    /// and `taylor_mean_remainder_lagrange` fails to kernel-verify.
    #[test]
    fn discovers_hoisted_outer_packages_and_skips_source_only_inner() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let base = tmp.path();

        // OUTER project: <base>/.lake/packages/{batteries,mathlib}/...
        let outer_lake = base.join(".lake");
        let batteries_built = outer_lake.join("packages/batteries/.lake/build/lib/lean");
        fs::create_dir_all(&batteries_built).unwrap();
        // The closure root: Mathlib's own build dir, itself a package.
        let mathlib_pkg = outer_lake.join("packages/mathlib");
        let closure_root = mathlib_pkg.join(".lake/build/lib/lean");
        fs::create_dir_all(&closure_root).unwrap();
        // INNER `.lake`: Mathlib's own packages/* are SOURCE-ONLY (no build dir).
        let inner_batteries_src = mathlib_pkg.join(".lake/packages/batteries");
        fs::create_dir_all(&inner_batteries_src).unwrap();

        let roots = discover_lake_package_olean_roots(&closure_root);

        assert!(
            roots.iter().any(|p| p == &batteries_built),
            "must discover the built OUTER batteries root; got {roots:?}"
        );
        assert!(
            !roots
                .iter()
                .any(|p| p.starts_with(mathlib_pkg.join(".lake/packages"))),
            "must NOT include the source-only inner package (no build dir); got {roots:?}"
        );
    }

    /// A self-contained project (closure root directly under its own `.lake`,
    /// with real built packages) still resolves its dependency roots — the fix
    /// generalizes the old single-`.lake` behaviour, it does not regress it.
    #[test]
    fn discovers_packages_in_a_self_contained_project() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let base = tmp.path();
        let lake = base.join(".lake");
        let closure_root = lake.join("build/lib/lean");
        fs::create_dir_all(&closure_root).unwrap();
        let dep_built = lake.join("packages/batteries/.lake/build/lib/lean");
        fs::create_dir_all(&dep_built).unwrap();

        let roots = discover_lake_package_olean_roots(&closure_root);
        assert!(
            roots.contains(&dep_built),
            "self-contained project must still discover its built deps; got {roots:?}"
        );
    }
}
