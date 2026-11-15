// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module loading: file I/O, recursive dependency resolution, and parallel loading.
//!
//! Public API for loading .olean modules into kernel Environment, with support
//! for uncached, cached, and parallel dependency resolution strategies.
//!
//! The uncached path (`load_olean_file`, `load_module_with_deps`) uses the
//! direct binary-to-Expr conversion (#2428), bypassing `ParsedExpr` entirely.
//! Cached and parallel loading use the same direct conversion with content-bound
//! module bundles. The public ParsedModule conversion APIs remain separate.

use super::load_parse::{parse_load_module, parse_load_module_incremental, LoadModule};
use super::load_register::{
    load_module_direct_with_cache_and_policy, load_module_part_direct, refresh_artifact_families,
    DeferredRecursors, PartEntries,
};
use super::module_cache_direct::read_optional;
use super::path::{
    legacy_module_name, module_name_from_path, module_visit_key, resolve_typed_module_path,
};
use super::{
    estimate_module_graph_size, ExprInternCache, ImportError, LoadSummary, OleanImportPolicy,
};
use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use hashbrown::HashSet;
use std::path::PathBuf;

mod cached;

#[cfg(test)]
mod deferred_recursors_tests;
pub use cached::{
    load_module_with_deps_cached, load_module_with_deps_cached_guarded,
    load_module_with_deps_parallel, load_modules_with_deps_checked,
    load_modules_with_deps_checked_with_limits, load_typed_module_with_deps_cached,
    load_typed_module_with_deps_parallel, CapturedModuleBytes, ModuleCaptureLimits,
};

#[cfg(test)]
mod deadline_load_tests;
mod graph_limit;
mod replay_load;
#[cfg(test)]
mod typed_traversal_tests;

pub use replay_load::load_module_with_deps_replaying_module;

use graph_limit::{enforce_module_graph_limit, enforce_typed_module_graph_limit_with_loaded};

/// Load an .olean file from disk into the given environment.
///
/// Uses the direct binary-to-Expr conversion path (#2428), bypassing
/// intermediate `ParsedExpr` tree allocation.
///
/// # REQUIRES
/// - `env` must be a valid Environment (may be empty or contain prior constants)
/// - `path` must point to an existing .olean file
///
/// # ENSURES
/// - On success, `env` contains all new constants from the file
/// - Duplicate constants (already in `env`) are skipped, not overwritten
/// - Returns `LoadSummary` with counts of added/skipped/duplicate constants
/// - `env` is unchanged on error (partial load failure may leave some constants)
pub fn load_olean_file(
    env: &mut Environment,
    path: impl AsRef<std::path::Path>,
) -> Result<LoadSummary, ImportError> {
    load_olean_file_with_import_policy(env, path, OleanImportPolicy::default())
}

/// Load an .olean file from disk into the given environment using an explicit
/// import policy.
///
/// With [`OleanImportPolicy::reject_unpinned_external`], the file is rejected
/// after parsing but before any constants are registered unless the caller has
/// chosen a future pinned/verified path.
pub fn load_olean_file_with_import_policy(
    env: &mut Environment,
    path: impl AsRef<std::path::Path>,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    let path = path.as_ref();
    let bytes = std::fs::read(path).map_err(|source| ImportError::FileUnreadable {
        path: path.to_path_buf(),
        source,
    })?;
    let module_name = module_name_from_path(path);
    super::world_gate::check_part_bytes(
        env,
        module_name.as_deref().unwrap_or("<unnamed module>"),
        &bytes,
    )?;
    let load_module = parse_load_module(bytes)?.read_from(path);
    super::clean_payload_requirement::check_load_module(env, &load_module, module_name.as_deref())?;
    policy.check_load_module(&load_module, module_name.as_deref())?;
    let mut intern_cache = ExprInternCache::default();
    // One file is the whole load of its artifact here: a stub it leaves for
    // a later part to complete has no later part.
    let artifact = module_name.clone();
    super::artifact_ledger::begin_artifact_load(env, &artifact, load_module.is_module)?;
    let mut summary = load_module_direct_with_cache_and_policy(
        env,
        &load_module,
        module_name,
        &mut intern_cache,
        policy,
    )?;
    let completion = super::artifact_ledger::finish_artifact_load(env, &artifact)?;
    let authoritative = (!load_module.is_module).then_some((&load_module, 0));
    super::restatement_evidence::complete(
        env,
        completion,
        authoritative,
        std::slice::from_mut(&mut summary),
    );
    Ok(summary)
}

/// Load a module by name along with all of its imports (depth-first).
///
/// Uses the direct binary-to-Expr conversion path (#2428).
///
/// `module` should be a dot-separated Lean module name like `Init.Core`.
/// `search_paths` should contain directories that hold `.olean` files, typically
/// the repository-pinned toolchain's `lib/lean`.
///
/// # REQUIRES
/// - `module` is a valid dot-separated module name (e.g., "Init.Core", "Mathlib.Data.List")
/// - `search_paths` contains directories with .olean files (empty paths will error)
///
/// # ENSURES
/// - Loads `module` and all transitive imports in dependency order (imports before dependents)
/// - Returns `Vec<LoadSummary>` with one entry per loaded module
/// - Each module is loaded at most once (duplicate imports are deduplicated)
/// - On error, returns `ImportError` with module name and search paths tried
pub fn load_module_with_deps(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
) -> Result<Vec<LoadSummary>, ImportError> {
    load_module_with_deps_with_import_policy(
        env,
        module,
        search_paths,
        OleanImportPolicy::default(),
    )
}

/// Load a module by name along with all imports using an explicit import
/// policy.
///
/// The policy is checked for each parsed `.olean` module before its constants
/// are registered. The default [`load_module_with_deps`] preserves legacy
/// allow-unpinned behavior.
pub fn load_module_with_deps_with_import_policy(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_with_import_policy(
        env,
        &legacy_module_name(module)?,
        search_paths,
        policy,
        policy,
    )
}

/// The closure load behind [`load_module_with_deps_with_import_policy`]:
/// `module`'s own parts under `own_policy`, every import under `policy`
/// ([`load_module_with_deps_replaying_module`] is the one caller that splits
/// them).
fn load_typed_module_with_deps_with_import_policy(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    policy: OleanImportPolicy,
    own_policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    // Ensure native reducers are registered. These are critical for type
    // checking .olean constants that depend on native functions like
    // System.Platform.getNumBits, Nat.decEq, String.decEq, etc.
    // Idempotent: re-inserting the same HashMap entries is harmless.
    // Part of #3210.
    env.ensure_native_reducers();

    // Pre-allocate for the full import graph. Init has ~320 modules with ~57K
    // constants; Std adds ~200 modules with ~80K constants. Reserving upfront
    // avoids ~log2(N) HashMap resizing rounds during loading. Part of #3133.
    let estimated_constants = estimate_module_graph_size(&module.to_string());
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }

    let mut visited = HashSet::new();
    let mut summaries = Vec::new();
    // Cross-module intern cache: expressions shared across the entire
    // dependency graph (e.g. `Nat`, `Prop`, `BVar(0)`) are deduplicated
    // once instead of independently per module (#2383).
    // Pre-size for typical Init/Std module graphs (~64K unique hash buckets).
    // Part of #3133.
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    load_typed_module_recursive(
        env,
        module,
        search_paths,
        &mut visited,
        &mut HashSet::new(),
        &mut summaries,
        &mut intern_cache,
        policy,
        own_policy,
    )?;
    // Regenerate noConfusionType/noConfusion for inductives where these were
    // loaded as axioms (no value) from the .olean. This happens when the
    // kernel couldn't generate them during add_inductive due to missing
    // same-module dependencies. Now that all modules are loaded, the full
    // environment is available for type inference. Part of #3134.
    env.regenerate_missing_no_confusion();
    // Register all built-in native reducers:
    //   Nat.decEq, Bool.decEq, String.decEq, String ops,
    //   Nat.add/sub/mul/blt, UInt{8..Size} ops, Platform ops.
    // Without these, reduce_native always returns None and the type checker
    // cannot compute definitional equalities involving these primitives,
    // causing TypeMismatch and NotAFunction failures. Part of #3134, #3210.
    env.ensure_native_reducers();
    // Recover structure/class field-name tables from the loaded projection
    // functions, NOW — once, with the whole import closure present. The
    // per-module finalize pass (in `load_register`) runs while a structure's
    // PROP-field (class-axiom) projections — `Monoid.mul_one`,
    // `Semigroup.mul_assoc`, … — are still served LAZILY by the zero-copy import
    // path and so are absent from `env.constants()`; at that point only the
    // structure's owned DATA-field projections are visible, a non-contiguous
    // index set that the recovery rejects (real Mathlib `Monoid` populates 0/7
    // fields per-module). By the end of the deps load every projection is
    // materialized, so this single authoritative scan recovers the full
    // contiguous field list (Monoid, Semigroup, MulOneClass, Group, …),
    // unlocking clean-auto's typeclass-projection law lane on real Mathlib. The
    // pass is idempotent (skips already-registered structures) and only appends
    // search metadata — never TCB (#olean-structure-field-names).
    // The DECODED `Lean.structureExt` tables and parents first — parked per
    // module while their structures were still served lazily — so a decoded
    // table wins over a recovered one.
    super::load_register::flush_pending_structure_metadata(env)?;
    super::load_register::register_structure_fields_from_projections(env);
    // Compatibility policy: retry explicit retained instance records now that
    // the closure's constants are available. The former type-shape heuristic
    // invented registrations and is not an admissible fallback for lost data.
    if policy.defer_global_instance_backfill() {
        super::load_register::finalize_global_instance_backfill(env);
    }
    Ok(summaries)
}

/// [`load_module_with_deps`] but sharing the caller's `visited` set ACROSS calls
/// and WITHOUT the per-call post-load fixups.
///
/// Keep `visited` with its Environment and treat its entries as opaque completed
/// keys. Ordinary dotted module keys remain compatible; quoted components use
/// an injective internal encoding instead of ambiguous display strings. A
/// failed module is not inserted; completed descendants may remain on error.
///
/// The cumulative batch verifier loads thousands of modules into one growing
/// `Environment`. With the plain [`load_module_with_deps`] (a fresh `visited`
/// each call) every call re-walks, re-reads, and re-parses the module's ENTIRE
/// transitive import closure from disk, so the batch costs O(modules × closure)
/// of redundant `.olean` reads (~50 min just to LOAD the v4.30 stdlib; a late
/// 0-constant aggregator module took 30-40 s alone, all re-parsing already-loaded
/// imports). Threading one caller-owned `visited` set makes an already-loaded
/// import short-circuit at the visited check in `load_module_recursive` BEFORE
/// any disk read, so the batch loads the UNION closure once: O(union).
///
/// Unlike [`load_module_with_deps`], this does NOT call
/// `regenerate_missing_no_confusion`: regenerating on a PARTIAL environment
/// mis-generates auxiliary constants for inductives whose dependencies load
/// later, and (because each module is loaded exactly once) there is no implicit
/// retry. The caller MUST run `regenerate_missing_no_confusion` ONCE after the
/// whole batch is loaded — equivalent to the per-module reload path, verified by
/// `import::tests::diag_shared_vs_perloop_constant_loss`.
///
/// SOUNDNESS: registration semantics are identical to [`load_module_with_deps`]
/// (same `extend_*` import path, insert-only, idempotent on duplicates). Sharing
/// `visited` only suppresses redundant RE-loads of already-registered modules;
/// it never changes which constants are admitted. Part of Lane A (Mathverse
/// ingestion throughput).
pub fn load_module_with_deps_shared(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    visited: &mut HashSet<String>,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_module_with_deps_shared_with_policy(
        env,
        module,
        search_paths,
        visited,
        OleanImportPolicy::default(),
    )
}

/// [`load_module_with_deps_shared`] with an explicit import policy.
pub fn load_module_with_deps_shared_with_policy(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    visited: &mut HashSet<String>,
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    env.ensure_native_reducers();
    let estimated_constants = estimate_module_graph_size(module);
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }
    let mut summaries = Vec::new();
    // Each call interns only its OWN module's new expressions (already-loaded
    // imports are skipped via the shared `visited`), so a small cache suffices.
    let mut intern_cache = ExprInternCache::with_capacity(8192);
    load_module_recursive(
        env,
        module,
        search_paths,
        visited,
        &mut summaries,
        &mut intern_cache,
        policy,
    )?;
    Ok(summaries)
}

/// Load SEVERAL modules into one environment in a single shared pass.
///
/// Sharing one `visited` set + intern cache across all requested modules is the whole
/// point: when modules `[A, B, C]` each transitively import a large common closure (e.g.
/// several mathlib-based modules all pulling `Mathlib.*`), the naive
/// `for m in modules { load_module_with_deps(env, m, ..) }` loop re-walks AND re-reads
/// that shared closure once per module — because each `load_module_with_deps` call starts
/// with a fresh `visited`. On a mathlib-scale closure that is O(modules × closure) of
/// redundant `.olean` reads/parses (observed: a second mathlib-based module took >70min on
/// top of the first's 13min). With a shared `visited`, the second and later modules skip
/// every already-loaded dependency module, so total work is ~one pass over the UNION of the
/// closures. The post-load fixups (`regenerate_missing_no_confusion`, native reducers) run
/// once at the end, exactly as the single-module path does.
pub fn load_modules_with_deps(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
) -> Result<Vec<LoadSummary>, ImportError> {
    load_modules_with_deps_with_import_policy(
        env,
        modules,
        search_paths,
        OleanImportPolicy::default(),
    )
}

/// [`load_modules_with_deps`] with an explicit import policy.
pub fn load_modules_with_deps_with_import_policy(
    env: &mut Environment,
    modules: &[String],
    search_paths: &[PathBuf],
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    env.ensure_native_reducers();
    // Reserve for the largest single module's estimate; the union is at least that big and
    // the HashMap grows from there. Avoids repeated resize rounds on the first big module.
    let estimated_constants = modules
        .iter()
        .map(|m| estimate_module_graph_size(m))
        .max()
        .unwrap_or(0);
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }
    // The shared state — the fix. `visited` and `intern_cache` persist ACROSS modules.
    let mut visited = HashSet::new();
    let mut summaries = Vec::new();
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    for module in modules {
        load_module_recursive(
            env,
            module,
            search_paths,
            &mut visited,
            &mut summaries,
            &mut intern_cache,
            policy,
        )?;
    }
    env.regenerate_missing_no_confusion();
    env.ensure_native_reducers();
    // See the note in `load_module_with_deps_with_import_policy`: recover
    // structure field-name tables once, after the whole union closure (and its
    // lazily-served law projections) is materialized.
    // The DECODED `Lean.structureExt` tables and parents first — parked per
    // module while their structures were still served lazily — so a decoded
    // table wins over a recovered one.
    super::load_register::flush_pending_structure_metadata(env)?;
    super::load_register::register_structure_fields_from_projections(env);
    Ok(summaries)
}

/// Load a module and dependencies only if import graph discovery stays within
/// `max_modules`.
///
/// This is intended for frontend paths that need a fail-fast guard around
/// broad Lean/Mathlib aggregate imports. The default [`load_module_with_deps`]
/// remains unbounded for callers that intentionally want full graph loading.
pub fn load_module_with_deps_bounded(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
) -> Result<Vec<LoadSummary>, ImportError> {
    enforce_module_graph_limit(env, module, search_paths, max_modules)?;
    load_module_with_deps(env, module, search_paths)
}

/// Load a module and its transitive imports into `env`, sharing the
/// already-loaded module set in `visited` ACROSS calls.
///
/// Unlike [`load_module_with_deps`], which allocates a fresh `visited` set per
/// call (so re-loading an overlapping closure re-parses and re-walks every
/// already-registered module), this entry point threads a caller-owned
/// `visited` set through the recursion. A module whose name is already in
/// `visited` is skipped without re-reading its `.olean` from disk and without
/// re-descending into its imports. This makes building the UNION import closure
/// of many target modules into one cumulative `Environment` cost O(union) file
/// I/O + parse work instead of O(targets × closure).
///
/// SOUNDNESS: identical registration semantics to [`load_module_with_deps`] —
/// constants are admitted through the same `.olean` import path
/// (`extend_*_unchecked` / `extend_constants_structural`), which is insert-only
/// and idempotent on duplicates. Sharing `visited` only suppresses redundant
/// *re-loads* of modules already registered; it never changes which constants
/// end up in `env`. The bounded guard
/// (`graph_limit::enforce_module_graph_limit_with_loaded`) is still applied per call — with
/// already-loaded subgraphs treated as leaves — so any single target's NEW
/// closure depth stays capped.
///
/// The `max_modules` guard is applied to each call (it bounds the depth of the
/// graph rooted at `module`); the cumulative size across all calls is bounded
/// only by the caller's set of targets.
pub fn load_module_with_deps_bounded_shared(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
    visited: &mut HashSet<String>,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_module_with_deps_bounded_shared_with_policy(
        env,
        module,
        search_paths,
        max_modules,
        visited,
        OleanImportPolicy::default(),
    )
}

/// Like [`load_module_with_deps_bounded_shared`], but with an explicit
/// [`OleanImportPolicy`] — used by bounded-memory closure loading (WS3) to
/// carry a [`clean_kernel::env::ProofValueElision`] policy so never-unfolded
/// proof VALUES are dropped AT REGISTRATION (capping PEAK resident memory, not
/// merely steady-state).
///
/// SOUNDNESS: the elision only affects which proof VALUES are stored for the
/// TRUSTED IMPORTED constants this loader admits; it never changes which
/// constants are registered, never touches their TYPES, and keeps every
/// `Definition` value. Set a non-`None` elision only when this env is pure
/// trusted imported context for checking a separate target module.
pub fn load_module_with_deps_bounded_shared_with_policy(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
    visited: &mut HashSet<String>,
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_bounded_shared_with_policy(
        env,
        &legacy_module_name(module)?,
        search_paths,
        max_modules,
        visited,
        policy,
    )
}

/// Exact typed-name counterpart of the bounded loader. This preserves the
/// existing import policy; typed identity does not grant kernel admission.
pub fn load_typed_module_with_deps_bounded(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    max_modules: usize,
) -> Result<Vec<LoadSummary>, ImportError> {
    enforce_typed_module_graph_limit_with_loaded(
        env,
        module,
        search_paths,
        max_modules,
        &HashSet::new(),
    )?;
    load_typed_module_with_deps_with_import_policy(
        env,
        module,
        search_paths,
        OleanImportPolicy::default(),
        OleanImportPolicy::default(),
    )
}

/// Share the existing injective internal visit keys without rendering/reparsing
/// the source module Name. Limits and registration policy are unchanged.
pub fn load_typed_module_with_deps_bounded_shared(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    max_modules: usize,
    visited: &mut HashSet<String>,
) -> Result<Vec<LoadSummary>, ImportError> {
    load_typed_module_with_deps_bounded_shared_with_policy(
        env,
        module,
        search_paths,
        max_modules,
        visited,
        OleanImportPolicy::default(),
    )
}

fn load_typed_module_with_deps_bounded_shared_with_policy(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    max_modules: usize,
    visited: &mut HashSet<String>,
    policy: OleanImportPolicy,
) -> Result<Vec<LoadSummary>, ImportError> {
    enforce_typed_module_graph_limit_with_loaded(env, module, search_paths, max_modules, visited)?;

    env.ensure_native_reducers();
    // This display-based estimate affects capacity only, never lookup/identity.
    let estimated_constants = estimate_module_graph_size(&module.to_string());
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }

    let mut summaries = Vec::new();
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    load_typed_module_recursive(
        env,
        module,
        search_paths,
        visited,
        &mut HashSet::new(),
        &mut summaries,
        &mut intern_cache,
        policy,
        policy,
    )?;
    // Capture the auto-generated noConfusion/noConfusionType constants: they are
    // inserted here, AFTER register_converted_constants, so they appear in no
    // LoadSummary. Fold them into a synthetic summary so the verify-batch O(new)
    // name scan sees them (otherwise it would under-count tc_pass).
    let regen_names = env.regenerate_missing_no_confusion();
    if !regen_names.is_empty() {
        let mut s = LoadSummary::empty();
        s.module_name = Some("<regenerated-no-confusion>".to_string());
        s.added_names = regen_names;
        summaries.push(s);
    }
    env.ensure_native_reducers();
    // The shared loader deliberately skips the O(env) post-load fixups, but
    // the decoded `Lean.structureExt` tables parked per module (while their
    // structures were still served lazily) cost only their own length to
    // apply, and without this the frontend's `clean check --imports-prefer-olean`
    // path — which is THIS loader — never registered a field table or a parent
    // for any olean-imported structure (measured 2026-09-10 on
    // `Mathlib/Order/Defs/PartialOrder`: `Preorder` had no `lt_iff_le_not_ge`
    // and no `toLE`/`toLT` parents while the eager loader's test had both).
    super::load_register::flush_pending_structure_metadata(env)?;
    Ok(summaries)
}

/// Every constant name the parts of the `.olean` at `path` store — the base
/// part, `.olean.server` and `.olean.private` — read with the parsers the
/// loader registers them with ([`load_companions_direct`]), without converting
/// an expression. `leanchecker` replays the constants of the most private part,
/// which subsume the others' (`LeanChecker.lean`, `replayFromImports`); the
/// union returned here is that set. `clean olean replay` accounts for each.
#[cfg(any(feature = "cli", test))]
pub(crate) fn stored_constant_names(path: &std::path::Path) -> Result<Vec<String>, ImportError> {
    let base = parse_load_module(std::fs::read(path)?)?;
    let server = read_optional(&path.with_extension("olean.server"))?;
    let private = read_optional(&path.with_extension("olean.private"))?;
    let mut names: Vec<String> = base.constants.iter().map(|c| c.name.clone()).collect();
    if let Some(bytes) = server.as_ref() {
        let part = parse_load_module_incremental(&base.bytes, None, bytes.clone())?;
        names.extend(part.constants.iter().map(|c| c.name.clone()));
    }
    if let Some(bytes) = private {
        let part = parse_load_module_incremental(&base.bytes, server.as_deref(), bytes)?;
        names.extend(part.constants.iter().map(|c| c.name.clone()));
    }
    names.retain(|name| !name.is_empty());
    names.sort();
    names.dedup();
    Ok(names)
}

/// Read and parse a module's `.olean.server` and `.olean.private`
/// companions against its base bytes, before anything of the artifact is
/// registered. A module-system artifact's private part holds every declaration
/// (its proofs and private declarations included) and is the part a consumer
/// that is not a `module` reads; its `.olean` and server part restate subsets
/// of it. A non-module artifact is read through its `.olean`, so its companions
/// may only restate names the `.olean` declares (R113, `artifact.rs`; `clean
/// lake build` writes empty companions). Both use incremental region parsing.
/// Part of #3134. A companion of a refused world is refused by name, as its
/// base part is (R81).
fn read_companions_direct(
    env: &Environment,
    label: &str,
    path: &std::path::Path,
    base_bytes: &[u8],
) -> Result<(Option<LoadModule>, Option<LoadModule>), ImportError> {
    let server = read_optional(&path.with_extension("olean.server"))?;
    let private = read_optional(&path.with_extension("olean.private"))?;
    for (bytes, suffix) in [(&server, "._server"), (&private, "._private")] {
        if let Some(bytes) = bytes {
            super::world_gate::check_part_bytes(env, &format!("{label}{suffix}"), bytes)?;
        }
    }
    let server_module = server
        .as_ref()
        .map(|bytes| parse_load_module_incremental(base_bytes, None, bytes.clone()))
        .transpose()?;
    let private_module = private
        .map(|bytes| parse_load_module_incremental(base_bytes, server.as_deref(), bytes))
        .transpose()?;
    Ok((server_module, private_module))
}

/// How a consumer that is not itself a `module` — every file Clean checks —
/// reads the parts of one artifact, after `lean` v4.30.0-rc2
/// (`Environment.lean`): `findOLeanParts` loads the `.olean`, the
/// `.olean.server` when present, and the `.olean.private` only beside the
/// server part; `ImportedModule.mainModule?` at `OLeanLevel.private` is the
/// private part of a module-system artifact (its `.olean` says `isModule`)
/// and the `.olean` of any other; and `finalizeImport` imports that one
/// part's constants and environment-extension entries
/// (`setImportedEntries` over `mainModule?`), its import list included
/// (`goRec` walks `mainModule?.imports`).
///
/// So a module-system artifact is read through its private part, which
/// must be there with its server part (`lean`: "missing data file"), and
/// any other artifact through its `.olean`. The returned roles say which
/// part's elaborator tables are registered; every part's declarations still
/// load, under rule 4 of `artifact_ledger`. A module-system artifact's parts
/// must state one import list: `lean` follows the private part's, Clean the
/// `.olean`'s. Any other artifact's imports are its `.olean`'s alone, for
/// `lean` and for Clean, so a companion's list is not compared (Clean's own
/// `lake build` writes companions whose lists differ).
fn read_plan(
    module: &str,
    base: &LoadModule,
    server: Option<&LoadModule>,
    private: Option<&LoadModule>,
) -> Result<[PartEntries; 3], ImportError> {
    // R113's artifact rule (`artifact.rs`), the one every re-check lane reads
    // through, before anything of the artifact registers: one header, one
    // record per name, and no name the authoritative part lacks.
    super::artifact::check_artifact_parts(
        module,
        base,
        server,
        private,
        super::artifact::ArtifactDepth::Records,
    )?;
    // Rule 4 for the tables Clean reads, over all the parts at once.
    super::artifact_ledger::check_artifact_entries(
        &Some(module.to_string()),
        base.is_module,
        &[
            Some(base.entries.as_slice()),
            server.map(|p| p.entries.as_slice()),
            private.map(|p| p.entries.as_slice()),
        ],
    )?;
    Ok(if base.is_module {
        [
            PartEntries::Compared,
            PartEntries::Compared,
            PartEntries::Read,
        ]
    } else {
        [
            PartEntries::Read,
            PartEntries::Compared,
            PartEntries::Compared,
        ]
    })
}

/// Load the parts of the artifact `module`, in level order, as one load of
/// it (`artifact_ledger`): its `.olean` under the label `module`, its
/// companions under `module._server` / `module._private`.
#[allow(clippy::too_many_arguments)]
fn load_artifact_parts(
    env: &mut Environment,
    module: &str,
    base: &LoadModule,
    server: Option<&LoadModule>,
    private: Option<&LoadModule>,
    summaries: &mut Vec<LoadSummary>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<(), ImportError> {
    let roles = read_plan(module, base, server, private)?;
    // Check every actual parsed part before beginning any artifact mutation.
    super::clean_payload_requirement::check_artifact_parts(env, module, base, server, private)?;
    let artifact = Some(module.to_string());
    super::artifact_ledger::begin_artifact_load(env, &artifact, base.is_module)?;
    let first_part = summaries.len();
    // read_plan has validated the complete artifact, including private-part
    // presence, one exact record per name and companion consistency. Defer
    // only dependencies genuinely absent from BOTH earlier parts.
    let mut deferred = private.filter(|_| base.is_module).map(|private| {
        let early: HashSet<_> = base
            .constants
            .iter()
            .chain(server.into_iter().flat_map(|part| &part.constants))
            .map(|constant| &constant.kernel_name)
            .collect();
        DeferredRecursors::new(
            module,
            private
                .constants
                .iter()
                .filter(|constant| !early.contains(&constant.kernel_name))
                .map(|constant| constant.kernel_name.clone())
                .collect(),
        )
    });
    for ((suffix, part), role) in [
        ("", Some(base)),
        ("._server", server),
        ("._private", private),
    ]
    .into_iter()
    .zip(roles)
    {
        let Some(part) = part else { continue };
        let label = format!("{module}{suffix}");
        policy.check_load_module(part, Some(&label))?;
        // A companion is a part of the artifact `module`, not an artifact
        // of its own (see `artifact_ledger`).
        let summary_ordinal = summaries.len();
        summaries.push(load_module_part_direct(
            env,
            part,
            Some(label),
            artifact.clone(),
            intern_cache,
            policy,
            role,
            if role == PartEntries::Compared {
                deferred.as_mut().map(|queue| (queue, summary_ordinal))
            } else {
                None
            },
        )?);
    }
    if let Some(private) = private.filter(|_| base.is_module) {
        refresh_artifact_families(
            env,
            &artifact,
            private
                .constants
                .iter()
                .filter(|constant| matches!(constant.kind, crate::ConstantKind::Inductive))
                .map(|constant| constant.kernel_name.clone()),
        );
    }
    if let Some(deferred) = deferred {
        deferred.finish(env, summaries)?;
    }
    // R142: every declaration the authoritative part states with a value is
    // resident as this artifact's own, with it. A re-check lane's load refuses
    // the import otherwise; a replay load records it for the replay to refuse.
    if policy.checks_authoritative_values() {
        let authoritative = if base.is_module { private } else { Some(base) };
        if let Some(part) = authoritative {
            let parts = summaries.get(first_part..).unwrap_or_default();
            let unmet = super::authoritative_values::unmet(env, &artifact, part, parts, policy);
            if policy.refuses_refused_completions() {
                if let Some((name, reason)) = unmet.first() {
                    return Err(ImportError::AuthoritativeValueNotResident {
                        module: module.to_string(),
                        name: name.to_string(),
                        reason: reason.clone(),
                    });
                }
            }
            if let Some(summary) = summaries.last_mut() {
                for (name, reason) in unmet {
                    if !summary.refused_completions.iter().any(|(n, _)| *n == name) {
                        summary.refused_completions.push((name, reason));
                    }
                }
            }
        }
    }
    let completion = super::artifact_ledger::finish_artifact_load(env, &artifact)?;
    let authoritative = if base.is_module {
        private.map(|part| (part, 1 + usize::from(server.is_some())))
    } else {
        Some((base, 0))
    };
    super::restatement_evidence::complete(
        env,
        completion,
        authoritative,
        &mut summaries[first_part..],
    );
    Ok(())
}

fn load_module_recursive(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    visited: &mut HashSet<String>,
    summaries: &mut Vec<LoadSummary>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<(), ImportError> {
    load_typed_module_recursive(
        env,
        &legacy_module_name(module)?,
        search_paths,
        visited,
        &mut HashSet::new(),
        summaries,
        intern_cache,
        policy,
        policy,
    )
}

/// Load `module`'s imports (recursively, under `policy`), then `module`'s own
/// parts under `own_policy`.
fn load_typed_module_recursive(
    env: &mut Environment,
    module: &Name,
    search_paths: &[PathBuf],
    visited: &mut HashSet<String>,
    visiting: &mut HashSet<Name>,
    summaries: &mut Vec<LoadSummary>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
    own_policy: OleanImportPolicy,
) -> Result<(), ImportError> {
    let key = module_visit_key(module)?;
    if visited.contains(&key) {
        return Ok(());
    }
    if !visiting.insert(module.clone()) {
        return Err(ImportError::UnsupportedModule {
            module: format!("{module:?}"),
            reason: "module dependency cycle in typed import graph".into(),
        });
    }
    // On failure, completed descendants may remain in the Environment. Only
    // successful complete modules enter the shared visited set; an in-progress
    // ancestor is not a completed dependency, and a retry must see failures.
    let result = (|| {
        // A load past its caller's deadline stops before each module.
        super::deadline::check()?;
        let path = resolve_typed_module_path(module, search_paths)?;
        let bytes = std::fs::read(&path)?;
        let label = module.to_string();
        // A module of a refused world is refused by name before its imports
        // are walked, not by whatever they fail with first (R81).
        super::world_gate::check_part_bytes(env, &label, &bytes)?;
        let load_module = parse_load_module(bytes)?.read_from(&path);
        super::clean_payload_requirement::check_load_module(env, &load_module, Some(&label))?;
        own_policy.check_load_module(&load_module, Some(&label))?;

        for import in &load_module.typed_imports {
            load_typed_module_recursive(
                env,
                &import.module_name,
                search_paths,
                visited,
                visiting,
                summaries,
                intern_cache,
                policy,
                policy,
            )?;
        }

        // Every part is read before anything of the artifact registers.
        let (server, private) = read_companions_direct(env, &label, &path, &load_module.bytes)?;
        let server = server.map(|part| part.read_from(&path));
        let private = private.map(|part| part.read_from(&path));
        load_artifact_parts(
            env,
            &label,
            &load_module,
            server.as_ref(),
            private.as_ref(),
            summaries,
            intern_cache,
            own_policy,
        )
    })();
    visiting.remove(module);
    if result.is_ok() {
        visited.insert(key);
    }
    result
}
