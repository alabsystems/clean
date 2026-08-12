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
//! The cached and parallel paths still use `ParsedModule` for cache compatibility.

use super::load_parse::{parse_load_module, parse_load_module_incremental};
use super::load_register::{
    load_module_direct_with_cache_and_policy, load_parsed_module_with_cache,
};
use super::parse::{parse_imports_only, parse_module, parse_module_incremental};
use super::path::{module_name_from_path, resolve_module_path};
use super::{
    estimate_module_graph_size, ExprInternCache, ImportError, LoadSummary, ModuleCache,
    OleanImportPolicy,
};
use crate::module::ParsedModule;
use clean_kernel::env::Environment;
use hashbrown::HashSet;
use rayon::prelude::*;
use std::collections::VecDeque;
use std::path::PathBuf;
use std::sync::Arc;

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
    let load_module = parse_load_module(bytes)?;
    policy.check_load_module(&load_module, module_name.as_deref())?;
    let mut intern_cache = ExprInternCache::default();
    load_module_direct_with_cache_and_policy(
        env,
        &load_module,
        module_name,
        &mut intern_cache,
        policy,
    )
}

/// Load a module by name along with all of its imports (depth-first).
///
/// Uses the direct binary-to-Expr conversion path (#2428).
///
/// `module` should be a dot-separated Lean module name like `Init.Core`.
/// `search_paths` should contain directories that hold `.olean` files, typically
/// something like `~/.elan/toolchains/<toolchain>/lib/lean`.
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
    // Ensure native reducers are registered. These are critical for type
    // checking .olean constants that depend on native functions like
    // System.Platform.getNumBits, Nat.decEq, String.decEq, etc.
    // Idempotent: re-inserting the same HashMap entries is harmless.
    // Part of #3210.
    env.ensure_native_reducers();

    // Pre-allocate for the full import graph. Init has ~320 modules with ~57K
    // constants; Std adds ~200 modules with ~80K constants. Reserving upfront
    // avoids ~log2(N) HashMap resizing rounds during loading. Part of #3133.
    let estimated_constants = estimate_module_graph_size(module);
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
    load_module_recursive(
        env,
        module,
        search_paths,
        &mut visited,
        &mut summaries,
        &mut intern_cache,
        policy,
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
    super::load_register::register_structure_fields_from_projections(env);
    // When the policy deferred the O(env) heuristic instance backfill (to avoid
    // the O(modules × env) quadratic across a large closure), run it ONCE now that
    // every module — and thus every real `@[instance]`/`@[class]` decoded per
    // module — is present. The result is identical to the per-module schedule
    // (additive + idempotent, real registrations already won first-writer).
    if policy.defer_global_instance_backfill() {
        super::load_register::finalize_global_instance_backfill(env);
    }
    Ok(summaries)
}

/// [`load_module_with_deps`] but sharing the caller's `visited` set ACROSS calls
/// and WITHOUT the per-call post-load fixups.
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
    enforce_module_graph_limit(module, search_paths, max_modules)?;
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
/// ([`enforce_module_graph_limit_with_loaded`]) is still applied per call — with
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
    enforce_module_graph_limit_with_loaded(module, search_paths, max_modules, visited)?;

    env.ensure_native_reducers();
    let estimated_constants = estimate_module_graph_size(module);
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }

    let mut summaries = Vec::new();
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    load_module_recursive(
        env,
        module,
        search_paths,
        visited,
        &mut summaries,
        &mut intern_cache,
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
    Ok(summaries)
}

fn enforce_module_graph_limit(
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
) -> Result<(), ImportError> {
    enforce_module_graph_limit_with_loaded(module, search_paths, max_modules, &HashSet::new())
}

/// Bounded import-graph discovery that treats every module in `already_loaded`
/// as a leaf: it neither resolves its path nor descends into its imports, and
/// it does not count against `max_modules`.
///
/// This is the shared-env analog of [`enforce_module_graph_limit`]: when many
/// target closures are accumulated into one cumulative env, a subgraph an
/// earlier target already loaded must NOT be re-walked (no redundant header
/// reads) and must NOT recount against this target's budget. The cap then bounds
/// only the *new* modules this target contributes, which is the correct
/// per-target depth guard for the cumulative load.
fn enforce_module_graph_limit_with_loaded(
    module: &str,
    search_paths: &[PathBuf],
    max_modules: usize,
    already_loaded: &HashSet<String>,
) -> Result<(), ImportError> {
    // A root already fully loaded by an earlier target contributes nothing new.
    if already_loaded.contains(module) {
        return Ok(());
    }

    let mut discovered = HashSet::new();
    let mut pending = VecDeque::from([module.to_string()]);

    while let Some(current) = pending.pop_front() {
        // Skip subgraphs already resident in the cumulative env: they were
        // walked and registered by a prior target, so re-reading their headers
        // here would re-do O(shared closure) work per target — exactly what the
        // shared-env cache exists to avoid.
        if already_loaded.contains(&current) {
            continue;
        }
        if !discovered.insert(current.clone()) {
            continue;
        }

        if discovered.len() > max_modules {
            return Err(ImportError::UnsupportedModule {
                module: module.to_string(),
                reason: format!(
                    "import graph exceeds the bounded loader limit of {max_modules} modules \
                     while discovering {current}; full Lean module loading is not yet \
                     supported on the frontend import path"
                ),
            });
        }

        let path = resolve_module_path(&current, search_paths)?;
        let bytes = std::fs::read(&path).map_err(|source| ImportError::FileUnreadable {
            path: path.clone(),
            source,
        })?;
        for import in parse_imports_only(&bytes)? {
            if !import.module_name.is_empty()
                && !discovered.contains(&import.module_name)
                && !already_loaded.contains(&import.module_name)
            {
                pending.push_back(import.module_name);
            }
        }
    }

    Ok(())
}

/// Load .olean.server and .olean.private companions for a module using the
/// direct binary-to-Expr path. Server files contain server-only constants
/// (e.g., casesOn for test/internal inductives). Private files contain
/// private/match helper constants. Server is loaded first since private may
/// reference server constants. Both use incremental region parsing. Part of #3134.
fn load_companions_direct(
    env: &mut Environment,
    path: &std::path::Path,
    base_bytes: &[u8],
    module: &str,
    summaries: &mut Vec<LoadSummary>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<(), ImportError> {
    let server_path = path.with_extension("olean.server");
    if server_path.exists() {
        if let Ok(server_bytes) = std::fs::read(&server_path) {
            if let Ok(server_module) = parse_load_module_incremental(base_bytes, None, server_bytes)
            {
                let server_module_name = format!("{}._server", module);
                policy.check_load_module(&server_module, Some(&server_module_name))?;
                if let Ok(s) = load_module_direct_with_cache_and_policy(
                    env,
                    &server_module,
                    Some(server_module_name),
                    intern_cache,
                    policy,
                ) {
                    summaries.push(s);
                }
            }
        }
    }
    let private_path = path.with_extension("olean.private");
    if server_path.exists() && private_path.exists() {
        if let Ok(private_bytes) = std::fs::read(&private_path) {
            let server_bytes = std::fs::read(&server_path).ok();
            if let Ok(private_module) =
                parse_load_module_incremental(base_bytes, server_bytes.as_deref(), private_bytes)
            {
                let private_module_name = format!("{}._private", module);
                policy.check_load_module(&private_module, Some(&private_module_name))?;
                if let Ok(s) = load_module_direct_with_cache_and_policy(
                    env,
                    &private_module,
                    Some(private_module_name),
                    intern_cache,
                    policy,
                ) {
                    summaries.push(s);
                }
            }
        }
    }
    Ok(())
}

/// Load .olean.server and .olean.private companions using the cached/parsed
/// module path. Same semantics as `load_companions_direct` but works with
/// `ParsedModule` and `ModuleCache`. Part of #3134.
fn load_companions_cached(
    env: &mut Environment,
    path: &std::path::Path,
    module: &str,
    summaries: &mut Vec<LoadSummary>,
    cache: &ModuleCache,
    intern_cache: &mut ExprInternCache,
) {
    let server_path = path.with_extension("olean.server");
    if server_path.exists() {
        let server_key = format!("{}._server", module);
        let server_parsed: Option<Arc<ParsedModule>> =
            if let Some(cached) = cache.get(&server_key, &server_path) {
                Some(cached)
            } else if let Ok(server_bytes) = std::fs::read(&server_path) {
                let base_bytes = std::fs::read(path).ok();
                let base = base_bytes.as_deref().unwrap_or(&[]);
                parse_module_incremental(base, None, &server_bytes)
                    .ok()
                    .map(|parsed| cache.insert(&server_key, &server_path, parsed))
            } else {
                None
            };
        if let Some(sp) = server_parsed {
            if let Ok(s) = load_parsed_module_with_cache(env, &sp, Some(server_key), intern_cache) {
                summaries.push(s);
            }
        }
    }
    let private_path = path.with_extension("olean.private");
    if server_path.exists() && private_path.exists() {
        let private_key = format!("{}._private", module);
        let private_parsed: Option<Arc<ParsedModule>> =
            if let Some(cached) = cache.get(&private_key, &private_path) {
                Some(cached)
            } else if let Ok(private_bytes) = std::fs::read(&private_path) {
                let base_bytes = std::fs::read(path).ok();
                let server_bytes = std::fs::read(&server_path).ok();
                let base = base_bytes.as_deref().unwrap_or(&[]);
                parse_module_incremental(base, server_bytes.as_deref(), &private_bytes)
                    .ok()
                    .map(|parsed| cache.insert(&private_key, &private_path, parsed))
            } else {
                None
            };
        if let Some(pp) = private_parsed {
            if let Ok(s) = load_parsed_module_with_cache(env, &pp, Some(private_key), intern_cache)
            {
                summaries.push(s);
            }
        }
    }
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
    if !visited.insert(module.to_string()) {
        return Ok(());
    }

    let path = resolve_module_path(module, search_paths)?;
    let bytes = std::fs::read(&path)?;
    let load_module = parse_load_module(bytes)?;
    policy.check_load_module(&load_module, Some(module))?;

    for import in &load_module.imports {
        if !import.module_name.is_empty() {
            load_module_recursive(
                env,
                &import.module_name,
                search_paths,
                visited,
                summaries,
                intern_cache,
                policy,
            )?;
        }
    }

    let summary = load_module_direct_with_cache_and_policy(
        env,
        &load_module,
        Some(module.to_string()),
        intern_cache,
        policy,
    )?;
    summaries.push(summary);
    load_companions_direct(
        env,
        &path,
        &load_module.bytes,
        module,
        summaries,
        intern_cache,
        policy,
    )?;

    Ok(())
}

/// Load a module by name along with all of its imports, using a cache.
///
/// Like `load_module_with_deps` but uses the provided cache to avoid
/// re-parsing modules. The cache persists across calls and automatically
/// invalidates entries when file modification times change.
///
/// Note: The cached path still uses `ParsedModule` for cache compatibility.
/// The cache stores `ParsedModule` which includes `ParsedExpr` trees.
/// For the uncached path, use `load_module_with_deps` which uses the direct
/// binary-to-Expr conversion (#2428).
///
/// # REQUIRES
/// - Same as `load_module_with_deps`
/// - `cache` must be a valid `ModuleCache` (may be empty or contain prior entries)
///
/// # ENSURES
/// - Same guarantees as `load_module_with_deps`
/// - Cache hit: returns cached parsed module (avoids re-parsing)
/// - Cache miss: parses module and inserts into cache
/// - Stale cache (mtime changed): invalidates entry and re-parses
pub fn load_module_with_deps_cached(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    env.ensure_native_reducers();
    let estimated_constants = estimate_module_graph_size(module);
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }
    let mut visited = HashSet::new();
    let mut summaries = Vec::new();
    let mut intern_cache = ExprInternCache::with_capacity(65536);
    load_module_recursive_cached(
        env,
        module,
        search_paths,
        &mut visited,
        &mut summaries,
        cache,
        &mut intern_cache,
    )?;
    env.regenerate_missing_no_confusion();
    env.ensure_native_reducers();
    Ok(summaries)
}

fn load_module_recursive_cached(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    visited: &mut HashSet<String>,
    summaries: &mut Vec<LoadSummary>,
    cache: &ModuleCache,
    intern_cache: &mut ExprInternCache,
) -> Result<(), ImportError> {
    if !visited.insert(module.to_string()) {
        return Ok(());
    }

    let path = resolve_module_path(module, search_paths)?;

    // Try cache first - now returns Arc<ParsedModule> to avoid expensive clones
    let parsed: Arc<ParsedModule> = if let Some(cached) = cache.get(module, &path) {
        cached
    } else {
        // Parse and cache - insert returns Arc to avoid clone
        let bytes = std::fs::read(&path)?;
        let parsed = parse_module(&bytes)?;
        cache.insert(module, &path, parsed)
    };

    for import in &parsed.imports {
        if !import.module_name.is_empty() {
            load_module_recursive_cached(
                env,
                &import.module_name,
                search_paths,
                visited,
                summaries,
                cache,
                intern_cache,
            )?;
        }
    }

    // Borrow the Arc<ParsedModule> directly — no deep clone needed (#2383).
    let summary =
        load_parsed_module_with_cache(env, &parsed, Some(module.to_string()), intern_cache)?;
    summaries.push(summary);
    load_companions_cached(env, &path, module, summaries, cache, intern_cache);

    Ok(())
}

/// Load a module and dependencies with parallel I/O and parsing.
/// Functionally equivalent to `load_module_with_deps_cached` but parses in
/// parallel via rayon, then loads sequentially in topological order.
pub fn load_module_with_deps_parallel(
    env: &mut Environment,
    module: &str,
    search_paths: &[PathBuf],
    cache: &ModuleCache,
) -> Result<Vec<LoadSummary>, ImportError> {
    env.ensure_native_reducers();
    let estimated_constants = estimate_module_graph_size(module);
    if estimated_constants > 0 {
        env.reserve_capacity(estimated_constants);
    }
    // Phase 1: Discover all modules and collect their paths
    let mut to_discover: Vec<String> = vec![module.to_string()];
    let mut discovered: HashSet<String> = HashSet::new();
    let mut module_bytes: Vec<(String, PathBuf, Vec<u8>)> = Vec::new();

    while let Some(mod_name) = to_discover.pop() {
        if !discovered.insert(mod_name.clone()) {
            continue;
        }

        let path = resolve_module_path(&mod_name, search_paths)?;

        // Check if already in cache
        if let Some(cached) = cache.get(&mod_name, &path) {
            for import in &cached.imports {
                if !import.module_name.is_empty() && !discovered.contains(&import.module_name) {
                    to_discover.push(import.module_name.clone());
                }
            }
            continue;
        }

        // Read file and extract imports for discovery (keep bytes for later parsing)
        let bytes = std::fs::read(&path)?;
        let imports = parse_imports_only(&bytes)?;

        module_bytes.push((mod_name.clone(), path, bytes));

        for import in imports {
            if !import.module_name.is_empty() && !discovered.contains(&import.module_name) {
                to_discover.push(import.module_name.clone());
            }
        }
    }

    // Phase 2: Parse all modules in parallel. Also parse server/private companions.
    let parsed_modules: Vec<Result<Vec<(String, PathBuf, ParsedModule)>, ImportError>> =
        module_bytes
            .into_par_iter()
            .map(|(name, path, bytes)| {
                let mut results = Vec::with_capacity(3);
                results.push((name.clone(), path.clone(), parse_module(&bytes)?));
                let server_path = path.with_extension("olean.server");
                if server_path.exists() {
                    if let Ok(sb) = std::fs::read(&server_path) {
                        if let Ok(sp) = parse_module_incremental(&bytes, None, &sb) {
                            results.push((format!("{}._server", name), server_path.clone(), sp));
                        }
                    }
                }
                let private_path = path.with_extension("olean.private");
                if server_path.exists() && private_path.exists() {
                    if let Ok(pb) = std::fs::read(&private_path) {
                        let sb = std::fs::read(&server_path).ok();
                        if let Ok(pp) = parse_module_incremental(&bytes, sb.as_deref(), &pb) {
                            results.push((format!("{}._private", name), private_path, pp));
                        }
                    }
                }
                Ok(results)
            })
            .collect();

    for result in parsed_modules {
        for (name, path, parsed) in result? {
            cache.insert(&name, &path, parsed);
        }
    }

    // Phase 3: Load modules in topological order (post-order DFS)
    let mut visited = HashSet::new();
    let mut summaries = Vec::new();
    let mut intern_cache = ExprInternCache::with_capacity(65536);

    fn load_in_order(
        env: &mut Environment,
        module: &str,
        search_paths: &[PathBuf],
        visited: &mut HashSet<String>,
        summaries: &mut Vec<LoadSummary>,
        cache: &ModuleCache,
        intern_cache: &mut ExprInternCache,
    ) -> Result<(), ImportError> {
        if !visited.insert(module.to_string()) {
            return Ok(());
        }

        let path = resolve_module_path(module, search_paths)?;
        let parsed = cache
            .get(module, &path)
            .expect("module should be in cache after parallel parse");

        for import in &parsed.imports {
            if !import.module_name.is_empty() {
                load_in_order(
                    env,
                    &import.module_name,
                    search_paths,
                    visited,
                    summaries,
                    cache,
                    intern_cache,
                )?;
            }
        }

        let summary =
            load_parsed_module_with_cache(env, &parsed, Some(module.to_string()), intern_cache)?;
        summaries.push(summary);
        load_companions_cached(env, &path, module, summaries, cache, intern_cache);

        Ok(())
    }

    load_in_order(
        env,
        module,
        search_paths,
        &mut visited,
        &mut summaries,
        cache,
        &mut intern_cache,
    )?;
    env.regenerate_missing_no_confusion();
    env.ensure_native_reducers();
    Ok(summaries)
}
