// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch .olean verification: shared environment, dependency ordering, type-checking.
//!
//! Core logic for loading many .olean modules into a cumulative kernel Environment
//! in dependency order and type-checking their constants. Used by the
//! `verify_olean_batch` binary.

#[cfg(feature = "cli")]
use crate::load_module_with_deps_shared_with_policy;
use crate::{
    load_module_with_deps_bounded_shared_with_policy, load_module_with_deps_with_import_policy,
    LoadSummary, OleanImportPolicy,
};
use clean_kernel::env::Environment;
use clean_kernel::env::ProofValueElision;
use clean_kernel::expr::Expr;
use clean_kernel::tc::{TypeChecker, DEFAULT_HEARTBEAT_LIMIT};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use tracing::{info, warn};

/// The load policy of verify-batch, a re-check lane over Lean's world: a
/// refused completion of an artifact's own stub refuses the import (R131),
/// never left as a trusted axiom that the full re-check then passes.
pub(crate) fn recheck_policy() -> OleanImportPolicy {
    OleanImportPolicy::default().refusing_refused_completions()
}

// -- Data types ---------------------------------------------------------------

// Full validation (infer_sort + check_type) is in verify_batch_full.rs.
pub use crate::verify_batch_full::{typecheck_constants_full, ValidationMode};

/// Per-module verification result.
#[derive(Debug, Clone, Serialize)]
pub struct ModuleResult {
    pub path: String,
    pub module_name: String,
    pub load_ok: bool,
    pub constants_added: usize,
    pub constants_skipped: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub elapsed_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub load_error: Option<String>,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub tc_errors: BTreeMap<String, String>,
}

/// Aggregate summary across all modules.
#[derive(Debug, Clone, Serialize)]
pub struct BatchSummary {
    pub root_dir: String,
    pub total_files: usize,
    pub processed_files: usize,
    pub load_success: usize,
    pub load_failure: usize,
    pub total_constants: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub total_skipped: usize,
    pub total_elapsed_secs: f64,
    pub pass_rate_pct: f64,
    /// Which validation mode produced `tc_pass`/`tc_fail`/`pass_rate_pct`.
    ///
    /// AUDIT-CRITICAL HONEST LABEL. `InferOnly` means the numbers are TYPE-ONLY
    /// (the proof value was NOT re-derived); `Full` means each value was
    /// re-derived with `check_type` IN THE ASSUMED ENVIRONMENT. Neither is
    /// `add_decl`-equivalent and neither visits the dependency cone — see
    /// [`crate::recheck_closed::RecheckLevel`], and
    /// [`crate::recheck_closed::recheck_closed`] for the level that is.
    pub validation_mode: ValidationMode,
    /// Human-readable honest label for `validation_mode`
    /// (`"type-only-infer"` vs `"local-assumed-env"`). Emitted so JSON
    /// consumers see the meaning without decoding the enum.
    pub validation_label: String,
    pub error_categories: BTreeMap<String, usize>,
    pub modules: Vec<ModuleResult>,
}

/// Module descriptor with parsed import information.
pub struct ModuleDesc {
    /// Path to the .olean file on disk.
    pub path: PathBuf,
    /// Dot-separated module name (e.g. "Mathlib.Data.Nat.Basic").
    pub module_name: String,
}

// -- File discovery -----------------------------------------------------------

pub fn discover_olean_files(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    discover_recursive(root, &mut files);
    files.sort();
    files
}

fn discover_recursive(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            discover_recursive(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "olean") {
            out.push(path);
        }
    }
}

// -- Helpers ------------------------------------------------------------------

pub fn module_name_from_path(path: &Path, root: &Path) -> String {
    let relative = path.strip_prefix(root).unwrap_or(path);
    let stem = relative.with_extension("");
    stem.components()
        .filter_map(|c| c.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

pub fn relative_display(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .to_string()
}

pub(crate) fn error_category(err: &str) -> String {
    let patterns = [
        ("HeartbeatExceeded", "HeartbeatExceeded"),
        ("heartbeat", "HeartbeatExceeded"),
        ("stack overflow", "StackOverflow"),
        ("StackOverflow", "StackOverflow"),
        ("not found in environment", "ConstNotFound"),
        ("ModuleNotFound", "ConstNotFound"),
        ("type mismatch", "TypeMismatch"),
        ("TypeMismatch", "TypeMismatch"),
        ("NotAFunction", "NotAFunction"),
        ("not a function", "NotAFunction"),
        ("universe", "UniverseError"),
        ("Universe", "UniverseError"),
        ("deep recursion", "RecursionDepth"),
        ("RecursionDepth", "RecursionDepth"),
        ("kernel panic", "KernelPanic"),
        ("parse error", "ParseError"),
        ("I/O error", "IoError"),
    ];
    for (needle, category) in patterns {
        if err.contains(needle) {
            return category.to_string();
        }
    }
    err.chars().take(40).collect::<String>()
}

// -- Dependency graph ---------------------------------------------------------

/// Build dependency graph and return modules in topological order.
///
/// The returned order respects TRANSITIVE dependencies among the target modules,
/// including those that route through modules NOT in `olean_files`. This matters
/// for cumulative-env replay (e.g. single-pass kernel verification): if target A
/// imports target B only transitively — through an intermediate module C that is
/// not itself a target (it lives in the dependency closure) — a naive sort over
/// just the target subgraph sees no A→B edge, can order A before B, and then B's
/// constants are `UnknownConst` when A is checked. To avoid that, we expand the
/// graph with every intermediate module reachable under `root`, topologically
/// sort the FULL graph, then keep only the target modules. The intermediate
/// modules are only read for their import headers (cheap) and never returned.
pub fn build_dependency_order(
    olean_files: &[PathBuf],
    root: &Path,
) -> (Vec<ModuleDesc>, Vec<(PathBuf, String)>) {
    let (mut modules, parse_failures) = parse_all_imports(olean_files, root);
    // The target set: only these are returned, in transitive-dependency order.
    let target_names: HashSet<String> = modules.keys().cloned().collect();
    // Pull in intermediate modules so target→target edges that route through a
    // non-target dependency are represented as a path of direct edges. Ordering
    // only needs intermediates UNDER `root` (out-of-root deps cannot route back
    // to a target), so resolve against `root` alone here.
    expand_import_graph(&mut modules, std::slice::from_ref(&root));
    let ordered = topological_sort(&modules);
    let result = ordered
        .into_iter()
        .filter(|name| target_names.contains(name))
        .filter_map(|name| {
            modules.get(&name).map(|(path, _)| ModuleDesc {
                path: path.clone(),
                module_name: name,
            })
        })
        .collect();
    (result, parse_failures)
}

/// For each target `.olean`, the set of `.olean` paths in its transitive import
/// closure that resolve under `root`, **including the module itself**, sorted
/// for determinism.
///
/// This is the content-addressed incremental-cache foundation. A module's
/// verification verdict is a pure function of its own bytes plus the bytes of
/// everything it transitively imports — its terms cannot reference any constant
/// outside that closure — so two runs agree on a module's verdict iff its
/// closure bytes (and the kernel fingerprint) agree. Keying the cache on a hash
/// of this closure means a single changed module re-verifies only itself and its
/// transitive dependents. Imports that do not resolve under `root` (stdlib,
/// sibling Lake packages) are excluded exactly as [`build_dependency_order`]
/// excludes them; they are trusted context the kernel already imported.
pub fn build_import_closures(
    olean_files: &[PathBuf],
    root: &Path,
) -> HashMap<PathBuf, Vec<PathBuf>> {
    build_import_closures_with_search_paths(olean_files, root, std::slice::from_ref(&root))
}

/// Like [`build_import_closures`], but resolves transitive imports across EVERY
/// `search_path` (root first), not just under `root`.
///
/// CORRECTNESS — incremental-cache completeness. The PARAGON base
/// (`build_base_env`) loads each target's full dependency closure across all its
/// search paths: `root` (Mathlib), sibling Lake packages (`.lake/packages/*`),
/// and the toolchain stdlib/Batteries/Aesop (`default_search_paths`). A module's
/// verdict therefore depends on the bytes of EVERY resolved closure member,
/// including out-of-`root` ones. The original `build_import_closures` excluded
/// out-of-root members from the hashed closure, so an out-of-root dependency
/// change (a stdlib/Batteries/Aesop/lake-package bump) did NOT re-key the cache
/// — a stale-reuse risk. Resolving across all search paths closes that gap: any
/// dependency whose bytes can change a target's verdict is now part of the
/// target's closure hash. Members are deduped (same module resolved once via the
/// first matching search path) and sorted for a deterministic key.
pub fn build_import_closures_with_search_paths(
    olean_files: &[PathBuf],
    root: &Path,
    search_paths: &[&Path],
) -> HashMap<PathBuf, Vec<PathBuf>> {
    let (mut modules, _parse_failures) = parse_all_imports(olean_files, root);
    let target_names: Vec<String> = modules.keys().cloned().collect();
    // Same transitive expansion build_dependency_order uses, so closures route
    // through intermediate (non-target) modules correctly — but resolved across
    // ALL search paths so out-of-root deps become hashed closure members.
    expand_import_graph(&mut modules, search_paths);

    let mut out: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();
    for name in &target_names {
        let Some((target_path, _)) = modules.get(name) else {
            continue;
        };
        let target_path = target_path.clone();
        // DFS over import edges, collecting every reachable module that resolved
        // under any search path (including the target itself, pushed first).
        let mut seen: HashSet<String> = HashSet::new();
        let mut stack: Vec<String> = vec![name.clone()];
        while let Some(cur) = stack.pop() {
            if !seen.insert(cur.clone()) {
                continue;
            }
            if let Some((_, imports)) = modules.get(&cur) {
                for imp in imports {
                    if modules.contains_key(imp) && !seen.contains(imp) {
                        stack.push(imp.clone());
                    }
                }
            }
        }
        let mut paths: Vec<PathBuf> = seen
            .iter()
            .filter_map(|n| modules.get(n).map(|(p, _)| p.clone()))
            .collect();
        paths.sort();
        out.insert(target_path, paths);
    }
    out
}

/// Grow `modules` with every module transitively imported by the current entries
/// whose `.olean` resolves under any `search_path` (first match wins, search-path
/// order), reading each module's import header exactly once. Imports that resolve
/// under no search path (e.g. a renamed/deleted dep) are skipped. Pure graph
/// expansion — no kernel work, no full module load.
///
/// Passing a single root reproduces the original root-only behavior used by
/// [`build_dependency_order`] (ordering only needs intermediates under `root`).
/// Passing the full PARAGON search path set is what makes
/// [`build_import_closures_with_search_paths`] hash out-of-root dependencies.
fn expand_import_graph(
    modules: &mut HashMap<String, (PathBuf, Vec<String>)>,
    search_paths: &[&Path],
) {
    let mut queue: VecDeque<String> = modules.keys().cloned().collect();
    while let Some(name) = queue.pop_front() {
        let imports = match modules.get(&name) {
            Some((_, imports)) => imports.clone(),
            None => continue,
        };
        for imp in imports {
            if modules.contains_key(&imp) {
                continue;
            }
            let rel = imp.replace('.', "/");
            let rel_olean = format!("{rel}.olean");
            let Some(path) = search_paths
                .iter()
                .map(|base| base.join(&rel_olean))
                .find(|p| p.exists())
            else {
                continue;
            };
            let import_names = artifact_import_names(&imp, &path).unwrap_or_default();
            modules.insert(imp.clone(), (path, import_names));
            queue.push_back(imp);
        }
    }
}

/// The import list of the artifact at `path` as every reader reads it (R113):
/// its authoritative part's (`crate::read_artifact`); an artifact whose parts
/// disagree is an error. Before, the closure walks took the `.olean`'s list,
/// which `lean` does not follow for a module-system artifact (review finding
/// P3: the `--incremental` cache key and verify-batch's order).
fn artifact_import_names(module: &str, path: &Path) -> Result<Vec<String>, crate::ImportError> {
    crate::read_artifact(module, path, crate::ArtifactDepth::Names)
        .map(|read| read.imports.into_iter().map(|i| i.module_name).collect())
}

fn parse_all_imports(
    olean_files: &[PathBuf],
    root: &Path,
) -> (
    HashMap<String, (PathBuf, Vec<String>)>,
    Vec<(PathBuf, String)>,
) {
    let mut modules: HashMap<String, (PathBuf, Vec<String>)> = HashMap::new();
    let mut parse_failures: Vec<(PathBuf, String)> = Vec::new();

    for path in olean_files {
        let module_name = module_name_from_path(path, root);
        match artifact_import_names(&module_name, path) {
            Ok(import_names) => {
                modules.insert(module_name, (path.clone(), import_names));
            }
            Err(e) => parse_failures.push((path.clone(), format!("import parse: {e}"))),
        }
    }
    (modules, parse_failures)
}

fn topological_sort(modules: &HashMap<String, (PathBuf, Vec<String>)>) -> Vec<String> {
    let known: HashSet<&str> = modules.keys().map(|s| s.as_str()).collect();
    let mut in_degree: HashMap<&str, usize> = HashMap::new();
    let mut dependents: HashMap<&str, Vec<&str>> = HashMap::new();

    for (name, (_, imports)) in modules {
        in_degree.entry(name.as_str()).or_insert(0);
        for imp in imports {
            if known.contains(imp.as_str()) {
                *in_degree.entry(name.as_str()).or_insert(0) += 1;
                dependents
                    .entry(imp.as_str())
                    .or_default()
                    .push(name.as_str());
            }
        }
    }

    let mut queue: VecDeque<&str> = VecDeque::new();
    let mut seeds: Vec<&str> = in_degree
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(&n, _)| n)
        .collect();
    seeds.sort();
    queue.extend(seeds);

    let mut ordered: Vec<String> = Vec::with_capacity(modules.len());
    let mut visited: HashSet<&str> = HashSet::new();

    while let Some(name) = queue.pop_front() {
        if !visited.insert(name) {
            continue;
        }
        ordered.push(name.to_string());
        if let Some(deps) = dependents.get(name) {
            let mut next: Vec<&str> = deps
                .iter()
                .filter(|&&dep| {
                    in_degree.get_mut(dep).is_some_and(|d| {
                        *d = d.saturating_sub(1);
                        *d == 0
                    })
                })
                .copied()
                .collect();
            next.sort();
            queue.extend(next);
        }
    }

    // Cycle modules go at the end.
    let ordered_set: HashSet<&str> = ordered.iter().map(|s| s.as_str()).collect();
    let mut cycle: Vec<String> = modules
        .keys()
        .filter(|k| !ordered_set.contains(k.as_str()))
        .cloned()
        .collect();
    cycle.sort();
    if !cycle.is_empty() {
        warn!(count = cycle.len(), "modules in dependency cycles");
    }
    ordered.extend(cycle);
    ordered
}

pub fn typecheck_constants(
    env: &Environment,
    target_names: &BTreeSet<String>,
) -> (usize, usize, BTreeMap<String, String>) {
    let tc = TypeChecker::new(env);
    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors = BTreeMap::new();

    let check = |name: &str,
                 type_: &Expr,
                 tc: &TypeChecker<'_>,
                 pass: &mut usize,
                 fail: &mut usize,
                 errors: &mut BTreeMap<String, String>| {
        if !target_names.contains(name) {
            return;
        }
        match tc.infer_type(type_) {
            Ok(_) => *pass += 1,
            Err(e) => {
                *fail += 1;
                errors.insert(name.to_string(), format!("{e:?}"));
            }
        }
    };

    for ci in env.constants() {
        check(
            &ci.name.to_string(),
            &ci.type_,
            &tc,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for ind in env.inductives() {
        check(
            &ind.name.to_string(),
            &ind.type_,
            &tc,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for ctor in env.constructors() {
        check(
            &ctor.name.to_string(),
            &ctor.type_,
            &tc,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }
    for rec in env.recursors() {
        check(
            &rec.name.to_string(),
            &rec.type_,
            &tc,
            &mut pass,
            &mut fail,
            &mut errors,
        );
    }

    (pass, fail, errors)
}

pub fn collect_new_env_names(env: &Environment, known: &mut HashSet<String>) -> BTreeSet<String> {
    #[cfg(debug_assertions)]
    let known_snapshot = known.clone();

    // Single pass over the `constants` table. Inductives, constructors, and
    // recursors are each ALSO mirrored into `constants` at registration
    // (env/registration.rs `self.constants.extend(...)`), and the auto-generated
    // `noConfusion`/`noConfusionType` constants insert there too — so
    // `env.constants()` is the complete superset of declared names. The former
    // separate inductives()/constructors()/recursors() passes were redundant:
    // every name they produced was already inserted by this loop and dropped by
    // the `known` dedup. Dropping them removes ~3 redundant scans + their
    // throwaway `to_string` allocations per module on the type-check batch path,
    // with a byte-identical result (asserted below in debug builds).
    let mut new_names = BTreeSet::new();
    for ci in env.constants() {
        let name = ci.name.to_string();
        if known.insert(name.clone()) {
            new_names.insert(name);
        }
    }

    // Oracle: in debug builds, recompute the old four-table scan from the
    // pre-mutation `known` and assert the single pass produced the identical set.
    // Guards the "constants is the superset" invariant against future env changes.
    #[cfg(debug_assertions)]
    {
        let mut oracle_known = known_snapshot;
        let mut oracle = BTreeSet::new();
        let mut try_insert = |name: String| {
            if oracle_known.insert(name.clone()) {
                oracle.insert(name);
            }
        };
        for ci in env.constants() {
            try_insert(ci.name.to_string());
        }
        for ind in env.inductives() {
            try_insert(ind.name.to_string());
        }
        for ctor in env.constructors() {
            try_insert(ctor.name.to_string());
        }
        for rec in env.recursors() {
            try_insert(rec.name.to_string());
        }
        debug_assert_eq!(
            new_names, oracle,
            "collect_new_env_names: single `constants` pass diverged from the four-table scan \
             (constants is no longer the superset of inductives/constructors/recursors?)"
        );
    }

    new_names
}

/// Build a [`BatchSummary`], honestly stamping which [`ValidationMode`] produced
/// the `tc_pass`/`tc_fail`/`pass_rate_pct` numbers.
///
/// AUDIT-CRITICAL: callers MUST pass the mode they actually ran. Passing
/// `Full` here when only `InferOnly` was executed would relabel a type-only
/// count as kernel-verified, which is exactly the over-statement the integrity
/// audit forbids.
pub(crate) fn build_summary_with_mode(
    root: &Path,
    total_files: usize,
    processed_files: usize,
    results: Vec<ModuleResult>,
    elapsed: Duration,
    mode: ValidationMode,
) -> BatchSummary {
    let load_success = results.iter().filter(|r| r.load_ok).count();
    let load_failure = results.iter().filter(|r| !r.load_ok).count();
    let total_constants: usize = results.iter().map(|r| r.constants_added).sum();
    let total_skipped: usize = results.iter().map(|r| r.constants_skipped).sum();
    let tc_pass: usize = results.iter().map(|r| r.tc_pass).sum();
    let tc_fail: usize = results.iter().map(|r| r.tc_fail).sum();
    let pass_rate_pct = if tc_pass + tc_fail > 0 {
        tc_pass as f64 / (tc_pass + tc_fail) as f64 * 100.0
    } else {
        0.0
    };

    let mut error_categories: BTreeMap<String, usize> = BTreeMap::new();
    for r in &results {
        if let Some(ref err) = r.load_error {
            *error_categories.entry(error_category(err)).or_default() += 1;
        }
        for err in r.tc_errors.values() {
            *error_categories.entry(error_category(err)).or_default() += 1;
        }
    }

    BatchSummary {
        root_dir: root.to_string_lossy().to_string(),
        total_files,
        processed_files,
        load_success,
        load_failure,
        total_constants,
        tc_pass,
        tc_fail,
        total_skipped,
        total_elapsed_secs: elapsed.as_secs_f64(),
        pass_rate_pct,
        validation_mode: mode,
        validation_label: mode.honest_label().to_string(),
        error_categories,
        modules: results,
    }
}

/// Back-compat shim: builds a summary labelled as the TYPE-ONLY (`InferOnly`)
/// mode. Use [`build_summary_with_mode`] when the caller may have run the full
/// `add_decl`-equivalent re-check, so the label is honest.
pub fn build_summary(
    root: &Path,
    total_files: usize,
    processed_files: usize,
    results: Vec<ModuleResult>,
    elapsed: Duration,
) -> BatchSummary {
    build_summary_with_mode(
        root,
        total_files,
        processed_files,
        results,
        elapsed,
        ValidationMode::InferOnly,
    )
}

// -- Module-level verification ------------------------------------------------

/// Verify a module using the default fast path (`InferOnly`).
pub fn verify_one_module(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    known_names: &mut HashSet<String>,
    load_only: bool,
) -> ModuleResult {
    verify_one_module_with_mode(
        env,
        module_name,
        rel_path,
        search_paths,
        known_names,
        load_only,
        ValidationMode::InferOnly,
        DEFAULT_HEARTBEAT_LIMIT,
    )
}

/// Load-only fast path: load `module_name` via the shared-`visited` loader (so
/// already-loaded imports are not re-parsed) and record a [`ModuleResult`].
///
/// Does NOT type-check and does NOT regenerate no-confusion constants — the
/// caller runs a single `regenerate_missing_no_confusion` after the WHOLE batch
/// is loaded (per-module regeneration on a partial env mis-generates aux
/// constants; see `import::tests::diag_shared_vs_perloop_constant_loss`). Used
/// only when `--load-only` is set; the type-checking paths keep the per-module
/// reload behavior unchanged.
#[cfg(feature = "cli")]
pub(crate) fn verify_one_module_load_shared(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    visited: &mut hashbrown::HashSet<String>,
) -> ModuleResult {
    let start = Instant::now();
    let load_result = load_module_with_deps_shared_with_policy(
        env,
        module_name,
        search_paths,
        visited,
        recheck_policy(),
    );
    let elapsed = start.elapsed();
    match load_result {
        Ok(summaries) => {
            // O(1) accounting from the loader's OWN per-module count, instead of a
            // `collect_new_env_names` scan of the entire growing environment on
            // every module — that scan is O(modules × env) = the dominant residual
            // cost after the shared-load fix (roughly half the load-only wall time
            // on the v4.30 stdlib, since it is untimed per module yet runs 2302×
            // over a ~215K-constant env).
            let added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
            ModuleResult {
                path: rel_path.to_string(),
                module_name: module_name.to_string(),
                load_ok: true,
                constants_added: added,
                constants_skipped: skipped,
                tc_pass: 0,
                tc_fail: 0,
                elapsed_ms: elapsed.as_millis() as u64,
                load_error: None,
                tc_errors: BTreeMap::new(),
            }
        }
        Err(e) => ModuleResult {
            path: rel_path.to_string(),
            module_name: module_name.to_string(),
            load_ok: false,
            constants_added: 0,
            constants_skipped: 0,
            tc_pass: 0,
            tc_fail: 0,
            elapsed_ms: elapsed.as_millis() as u64,
            load_error: Some(format!("{e}")),
            tc_errors: BTreeMap::new(),
        },
    }
}

/// Verify a module with configurable validation mode (Part of #3232).
///
/// Standalone entry: uses a throwaway `visited`. The cumulative batch loop calls
/// [`verify_one_module_with_mode_shared`] with ONE shared `visited` set so
/// already-loaded imports are not re-parsed per module (O(union), not
/// O(modules × closure)).
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_one_module_with_mode(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    known_names: &mut HashSet<String>,
    load_only: bool,
    mode: ValidationMode,
    max_heartbeats: u32,
) -> ModuleResult {
    let mut visited = hashbrown::HashSet::new();
    verify_one_module_with_mode_shared(
        env,
        module_name,
        rel_path,
        search_paths,
        known_names,
        load_only,
        mode,
        max_heartbeats,
        ProofValueElision::None,
        &mut visited,
    )
}

/// Like [`verify_one_module_with_mode`] but threads a caller-owned `visited` set
/// across calls (the cumulative batch loop), so an already-loaded import
/// short-circuits before any `.olean` re-read — eliminating the O(modules ×
/// closure) re-parse on the type-checking path too. Per-call no-confusion
/// regeneration is retained (the per-module type-check needs it). The loaded
/// environment is identical to the per-module-reload path (the
/// `diag_full_shared_vs_perloop` qualification example compares their complete
/// name inventories), so type-check results are unchanged.
#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_one_module_with_mode_shared(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    known_names: &mut HashSet<String>,
    load_only: bool,
    mode: ValidationMode,
    max_heartbeats: u32,
    elide_proof_values: ProofValueElision,
    visited: &mut hashbrown::HashSet<String>,
) -> ModuleResult {
    verify_one_module_with_mode_in_run(
        env,
        module_name,
        rel_path,
        search_paths,
        known_names,
        load_only,
        mode,
        max_heartbeats,
        elide_proof_values,
        visited,
        &mut BTreeSet::new(),
    )
}

/// `verify_one_module_with_mode_shared` as one module of a multi-module run
/// in one cumulative environment. `not_admitted` carries the display spellings
/// of every declaration an EARLIER module of the run refused under
/// `ValidationMode::Full`, and gains this module's refusals. A declaration that
/// mentions one is refused, as Lean's replay of the whole run would refuse it
/// (`crate::verify_batch_full::typecheck_constants_full_streaming_in_run`).
#[allow(clippy::too_many_arguments)]
pub fn verify_one_module_with_mode_in_run(
    env: &mut Environment,
    module_name: &str,
    rel_path: &str,
    search_paths: &[PathBuf],
    known_names: &mut HashSet<String>,
    load_only: bool,
    mode: ValidationMode,
    max_heartbeats: u32,
    elide_proof_values: ProofValueElision,
    visited: &mut hashbrown::HashSet<String>,
    not_admitted: &mut BTreeSet<String>,
) -> ModuleResult {
    let start = Instant::now();
    let load_result: Result<Vec<LoadSummary>, _> = load_module_with_deps_bounded_shared_with_policy(
        env,
        module_name,
        search_paths,
        usize::MAX,
        visited,
        recheck_policy(),
    );
    let elapsed = start.elapsed();

    match load_result {
        Ok(summaries) => {
            // Snapshot the pre-mutation `known` for the debug oracle below.
            #[cfg(debug_assertions)]
            let known_before = known_names.clone();
            // O(new) threaded scan: union the per-load added names the loader
            // captured (registration chokepoint + the synthetic no-confusion
            // summary), instead of re-scanning the whole growing env per module
            // (which was O(modules × env)).
            let mut new_names: BTreeSet<String> = BTreeSet::new();
            for s in &summaries {
                for n in &s.added_names {
                    let ns = n.to_string();
                    if known_names.insert(ns.clone()) {
                        new_names.insert(ns);
                    }
                }
            }
            // Backstop: the threaded set MUST equal the complete single-pass scan
            // of `env.constants()` (collect_new_env_names is the oracle). Fires in
            // debug/test builds if any name-source is ever missed (e.g. a future
            // post-registration auto-generation pass).
            #[cfg(debug_assertions)]
            {
                let mut oracle_known = known_before;
                let oracle = collect_new_env_names(env, &mut oracle_known);
                debug_assert_eq!(
                    new_names, oracle,
                    "verify-batch threaded added-name set diverged from collect_new_env_names \
                     (a name-source is uncaptured — see LoadSummary.added_names)"
                );
            }
            let added = new_names.len();
            let skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();
            // Declarations of this module the loader dropped because another
            // module's constant (or a kernel seed) already held the name: the
            // module's other declarations resolve to that constant instead, so
            // the full re-check refuses each as already declared, and counts it.
            let already_declared: BTreeMap<String, String> = summaries
                .iter()
                .flat_map(|s| s.shadowed_declarations.iter())
                .map(|(name, held_by)| (name.to_string(), held_by.clone()))
                .collect();
            let (tc_pass, tc_fail, tc_errors) = if load_only {
                (0, 0, BTreeMap::new())
            } else {
                match mode {
                    ValidationMode::InferOnly => typecheck_constants(env, &new_names),
                    ValidationMode::Full => {
                        let mut targets = new_names.clone();
                        targets.extend(already_declared.keys().cloned());
                        let (pass, fail, errs, _stats) =
                            crate::verify_batch_full::typecheck_constants_full_streaming_in_run(
                                env,
                                &targets,
                                not_admitted,
                                &already_declared,
                                max_heartbeats,
                                elide_proof_values,
                                None,
                            );
                        // A shadowed name's resident constant is another
                        // module's: its refusal here says nothing about that one.
                        not_admitted.extend(
                            errs.keys()
                                .filter(|k| !already_declared.contains_key(*k))
                                .cloned(),
                        );
                        (pass, fail, errs)
                    }
                }
            };
            ModuleResult {
                path: rel_path.to_string(),
                module_name: module_name.to_string(),
                load_ok: true,
                constants_added: added,
                constants_skipped: skipped,
                tc_pass,
                tc_fail,
                elapsed_ms: elapsed.as_millis() as u64,
                load_error: None,
                tc_errors,
            }
        }
        Err(e) => {
            // A refused import can leave declarations resident: an
            // inconsistent-artifact check (a self-dependent declaration, a name
            // declared twice differently) runs once the artifact's records are
            // registered. Lean's replay of the run never added them, so every
            // name the failed load left behind is not admitted, and a later
            // module's use of one is refused as the run refuses the use of any
            // declaration it did not admit.
            not_admitted.extend(collect_new_env_names(env, known_names));
            ModuleResult {
                path: rel_path.to_string(),
                module_name: module_name.to_string(),
                load_ok: false,
                constants_added: 0,
                constants_skipped: 0,
                tc_pass: 0,
                tc_fail: 0,
                elapsed_ms: elapsed.as_millis() as u64,
                load_error: Some(format!("{e}")),
                tc_errors: BTreeMap::new(),
            }
        }
    }
}

#[cfg(feature = "cli")]
pub(crate) fn emit_summary(summary: &BatchSummary, json_output: bool) {
    if json_output {
        let out = serde_json::to_string_pretty(summary)
            .expect("invariant: BatchSummary is always serializable");
        use std::io::Write;
        std::io::stdout()
            .write_all(out.as_bytes())
            .expect("invariant: stdout write should not fail");
        std::io::stdout().write_all(b"\n").ok();
    } else {
        info!(
            dir = summary.root_dir,
            total_files = summary.total_files,
            processed = summary.processed_files,
            load_ok = summary.load_success,
            load_err = summary.load_failure,
            constants = summary.total_constants,
            tc_pass = summary.tc_pass,
            tc_fail = summary.tc_fail,
            skipped = summary.total_skipped,
            pass_rate = format!("{:.2}%", summary.pass_rate_pct),
            elapsed_secs = format!("{:.2}", summary.total_elapsed_secs),
            "batch verification complete"
        );
        if !summary.error_categories.is_empty() {
            for (cat, count) in &summary.error_categories {
                warn!(category = cat, count, "error category");
            }
        }
    }
}

/// Return true when `root` is itself the `Init` module tree (or a subtree of
/// it), as opposed to a sibling directory that merely *imports* `Init`.
///
/// When the verified directory IS `Init` — e.g. `<toolchain>/lib/lean/Init` —
/// the discovered `.olean` files reconstruct module names like
/// `Init.Data.Nat.Basic` / `BinderNameHint` that ARE the `Init` closure. A
/// separate `Init` pre-load would then re-add every one of those constants
/// first, so the batch loop only ever re-encounters them through the duplicate
/// branch (`LoadSummary.duplicate_constants`) and reports `constants_added=0`,
/// `tc_pass=0` for the whole run. Detecting this lets the caller suppress the
/// redundant pre-load so each module is loaded (and re-verified) for real.
fn root_is_init_tree(root: &Path) -> bool {
    root.components()
        .filter_map(|c| c.as_os_str().to_str())
        .any(|c| c == "Init")
}

/// Pre-load Init into the environment unless root already contains Init.
pub fn preload_init_if_needed(env: &mut Environment, root: &Path, search_paths: &[PathBuf]) {
    preload_init_with_snapshot(
        env,
        root,
        search_paths,
        None,
        false,
        DEFAULT_HEARTBEAT_LIMIT,
        ProofValueElision::None,
    );
}

/// True when a separate Init pre-load is needed (root neither contains nor *is*
/// the Init tree). Factored out so the snapshot path and the legacy path agree.
fn init_preload_needed(root: &Path, search_paths: &[PathBuf]) -> bool {
    // `root_has_init` is true when a sibling `Init` lives *under* root (so its
    // constants will be loaded by the batch loop anyway). `root_is_init_tree`
    // covers the case where root literally IS the Init tree — there the loop
    // reconstructs Init's own modules directly, so a separate pre-load would
    // double-load every constant and zero out the added/tc_pass accounting.
    let root_has_init = root.join("Init").is_dir() || root.join("Init.olean").exists();
    let root_is_init = root_is_init_tree(root);
    if root_is_init {
        info!("root is the Init tree — skipping separate Init pre-load (avoids double-load)");
        return false;
    }
    if root_has_init {
        info!("root contains Init — skipping separate Init pre-load");
        return false;
    }
    !search_paths.is_empty()
}

/// Resolve a module name (e.g. `Init.Core`) to its `.olean` path on the given
/// search paths. Mirrors `import::path::resolve_module_path` (which is
/// `pub(super)`); kept local so the closure-hash walk does not need to expand
/// that module's visibility.
fn resolve_olean_on_paths(module: &str, search_paths: &[PathBuf]) -> Option<PathBuf> {
    let rel: PathBuf = module.split('.').collect::<Vec<_>>().join("/").into();
    let rel = rel.with_extension("olean");
    search_paths
        .iter()
        .map(|base| base.join(&rel))
        .find(|c| c.exists())
}

/// Compute a stable blake3 hash of the Init import closure: the resolved
/// `.olean` files of `Init` and every transitive import, hashed in sorted order
/// by their byte content, mixed with the kernel crate version.
///
/// This is the `init_closure_blake3` header field: it changes whenever ANY file
/// in the Init closure changes on disk (a different toolchain, a rebuilt
/// stdlib, etc.), so a stale snapshot built from different inputs is rejected.
/// On any resolution/parse error the hash still completes over whatever was
/// reachable — the worst case is a spurious cache miss (cold load), never
/// a false hit, because the missing input simply isn't mixed in and the next
/// run that *can* resolve it will produce a different hash and discard.
fn init_closure_hash(search_paths: &[PathBuf]) -> String {
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut file_hashes: BTreeMap<String, String> = BTreeMap::new();
    queue.push_back("Init".to_string());

    while let Some(module) = queue.pop_front() {
        if !visited.insert(module.clone()) {
            continue;
        }
        let Some(path) = resolve_olean_on_paths(&module, search_paths) else {
            continue;
        };
        // Every part the loader reads, and the imports of the part `lean`
        // reads (R113); an unreadable part is mixed in as such, never skipped.
        file_hashes.insert(
            module.clone(),
            crate::verify_cache::artifact_content_hash(&path)
                .unwrap_or_else(|| "<unreadable>".to_string()),
        );
        if let Ok(imports) = artifact_import_names(&module, &path) {
            for imp in imports {
                if !visited.contains(&imp) {
                    queue.push_back(imp);
                }
            }
        }
    }

    // Deterministic: BTreeMap iterates by module name. Mix the kernel version
    // so a binary upgrade alone invalidates even if the files are byte-identical.
    let mut hasher = blake3::Hasher::new();
    hasher.update(clean_kernel::VERSION.as_bytes());
    for (module, hash) in &file_hashes {
        hasher.update(module.as_bytes());
        hasher.update(b"\0");
        hasher.update(hash.as_bytes());
        hasher.update(b"\n");
    }
    hasher.finalize().to_hex().to_string()
}

/// The snapshot file path under a cache directory.
fn snapshot_path(cache_dir: &Path) -> PathBuf {
    cache_dir.join("init.snapshot")
}

/// Pre-load Init, optionally using a `.clean-cache` snapshot for the warm path.
///
/// Behaviour:
/// - If a `cache_dir` is given AND a snapshot exists there AND the P1 header
///   gate matches the current run, restore the env from the snapshot (the fast
///   path: seconds instead of minutes). The restored env REPLACES `env`'s Init
///   contents by merging the snapshot env in.
/// - Otherwise do the full `load_module_with_deps(Init)`. If `full_validation`
///   is set, run the local assumed-environment check (`infer_sort` +
///   `check_type`, `typecheck_constants_full`) over the newly-added Init
///   constants, and ONLY if that check reports zero failures, write the
///   snapshot to `cache_dir`.
///
/// SOUNDNESS:
/// - The snapshot is WRITTEN only after the local assumed-environment check of
///   the Init constants succeeded in THIS run (never from a load-only /
///   infer-only env), so it is
///   a cache of a prior local check, not a trust claim. Since R1-SNAP the
///   write carries a `SnapshotAttestation` of that local check, which the kernel
///   seals into a content-bound `SnapshotReceipt` inside the snapshot header.
/// - The snapshot is REUSED only on an exact header match AND a present,
///   content-bound verification receipt (`SnapshotReceiptPolicy::RequireReceipt`
///   — the only policy used in production); any mismatch, absent receipt, or
///   receipt/content divergence falls back to the full load (fail safe).
///
/// MEMORY BOUNDING (WS3): when `elide != ProofValueElision::None`, the Init
/// closure is loaded through the import policy's proof-value elision, so each
/// Init module's never-unfolded proof VALUES (Opaque, and under
/// `OpaqueAndTheorem` also Theorem) are dropped AT REGISTRATION — capping peak
/// resident memory rather than only steady-state. Under elision the snapshot
/// warm-path RESTORE and the snapshot WRITE are both disabled, because a
/// snapshot is a full-resident image: restoring one would re-inflate the very
/// values we are eliding, and writing one from an elided env would persist a
/// value-stripped image as if it were a complete locally-checked Init. With
/// `ProofValueElision::None` (the default) this is byte-identical to the prior
/// behavior.
pub fn preload_init_with_snapshot(
    env: &mut Environment,
    root: &Path,
    search_paths: &[PathBuf],
    cache_dir: Option<&Path>,
    full_validation: bool,
    max_heartbeats: u32,
    elide: ProofValueElision,
) {
    if !init_preload_needed(root, search_paths) {
        return;
    }

    // -- Warm path: try the snapshot if a cache dir is configured. -----------
    // Only when `env` is empty: the snapshot IS the full Init closure, so it
    // becomes the environment verbatim (preserving every restored `*_init`
    // flag). A non-empty caller env falls through to the full load — fail safe.
    let env_is_empty = env.constants().next().is_none()
        && env.inductives().next().is_none()
        && env.constructors().next().is_none();
    // Under proof-value elision the warm path is DISABLED: a snapshot is a
    // full-resident image (it is only ever WRITTEN from the value-present cold
    // path below), so restoring it would re-inflate exactly the Init values we
    // are eliding — defeating the memory bound. Fall through to the elided cold
    // load instead.
    // A snapshot carries no Lean-world binding (R81): the warm path is taken
    // only over an Init a fresh environment reads, and binds that world after
    // the restore. Any other Init falls through to the cold load, whose
    // import gate refuses it by name.
    let init_world = resolve_olean_on_paths("Init", search_paths)
        .and_then(|init| std::fs::read(init).ok())
        .and_then(|bytes| crate::import::part_world("Init", &bytes).ok().flatten());
    if let (Some(dir), true, true, Some(init_world)) = (
        cache_dir,
        env_is_empty,
        elide == ProofValueElision::None,
        init_world,
    ) {
        let path = snapshot_path(dir);
        if path.exists() {
            let hash = init_closure_hash(search_paths);
            let expected = clean_kernel::env::SnapshotHeader::current(hash);
            // R1-SNAP: production reuse REQUIRES the verification receipt — a
            // snapshot nothing attested (or whose receipt no longer binds to
            // the stored env bytes) is refused and the cold load
            // runs instead. The AcceptUnreceipted opt-out is never used here.
            match Environment::load_snapshot(
                &path,
                &expected,
                clean_kernel::env::SnapshotReceiptPolicy::RequireReceipt,
            ) {
                Ok(clean_kernel::env::SnapshotLoadOutcome::Loaded(mut snap_env)) => {
                    let warm_start = Instant::now();
                    let added = snap_env.constants().count();
                    // Restore the world only if the content-bound profile
                    // already matches it; never rewrite a verified snapshot's
                    // semantic input after its receipt was accepted.
                    match crate::import::bind_restored_world(&mut snap_env, init_world, "Init") {
                        Ok(()) => {
                            *env = *snap_env;
                            info!(constants=added,elapsed_ms=warm_start.elapsed().as_millis(),path=%path.display(),"Init restored from .clean-cache snapshot (warm path)");
                            return;
                        }
                        Err(error) => {
                            warn!(%error,"Init snapshot universe profile mismatch; cold load")
                        }
                    }
                }
                Ok(clean_kernel::env::SnapshotLoadOutcome::Mismatch(h)) => {
                    info!(
                        stale_version = h.snapshot_version,
                        "Init snapshot header mismatch — discarding, cold load"
                    );
                }
                Ok(clean_kernel::env::SnapshotLoadOutcome::ReceiptRefused {
                    violation, ..
                }) => {
                    warn!(
                        violation = %violation,
                        path = %path.display(),
                        "Init snapshot REFUSED: verification receipt absent or \
                         not content-bound — discarding, cold load"
                    );
                }
                Ok(clean_kernel::env::SnapshotLoadOutcome::LoadedUnreceipted {
                    violation, ..
                }) => {
                    // Unreachable under RequireReceipt; refuse to use it anyway
                    // (fail closed) if the kernel contract ever drifts.
                    warn!(
                        violation = %violation,
                        "Init snapshot returned LoadedUnreceipted under \
                         RequireReceipt — NOT reusing it, cold load"
                    );
                }
                Err(e) => {
                    warn!(err = %e, "Init snapshot unreadable/corrupt — cold load");
                }
            }
        }
    }

    // -- Cold path: full load (+ optional local check + snapshot write). ---
    info!("pre-loading Init module (external dependency)...");
    let init_start = Instant::now();
    // Carry the proof-value elision into the load so Init's never-unfolded
    // proof VALUES are dropped at registration (load_register applies
    // `policy.proof_elision()` per constant). With `None` this is identical to
    // the plain `load_module_with_deps`.
    let summaries = match load_module_with_deps_with_import_policy(
        env,
        "Init",
        search_paths,
        // Defer the O(env) heuristic instance backfill to a single end-of-closure
        // pass: the Init closure is ~320 modules, so the per-module schedule is an
        // O(modules × env) quadratic that dominated this pre-load.
        recheck_policy()
            .with_proof_elision(elide)
            .with_deferred_global_instance_backfill(),
    ) {
        Ok(s) => s,
        Err(e) => {
            warn!(err = %e, "failed to pre-load Init (continuing without)");
            return;
        }
    };
    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    info!(
        constants = total_added,
        elapsed_ms = init_start.elapsed().as_millis(),
        "Init loaded"
    );

    // Under proof-value elision NEVER write a snapshot: the env is now missing
    // the elided values, so persisting it would let a future `none` run restore
    // a value-stripped image as if it were a complete, fully-resident Init.
    if elide != ProofValueElision::None {
        info!("snapshot write skipped: proof-value elision active (elided env is not a complete image)");
        return;
    }

    // Snapshot WRITE is gated on a successful local assumed-environment check
    // of THIS run.
    let Some(dir) = cache_dir else {
        return;
    };
    if !full_validation {
        info!("snapshot write skipped: --full-validation required to write a snapshot");
        return;
    }

    let target_names: BTreeSet<String> = init_constant_names(env);
    let reverify_start = Instant::now();
    let (pass, fail, _errors) = typecheck_constants_full(env, &target_names, max_heartbeats);
    info!(
        pass,
        fail,
        elapsed_ms = reverify_start.elapsed().as_millis(),
        "Init local assumed-environment check (typecheck_constants_full; \
         dependencies assumed, not a dependency-closed replay)"
    );
    if fail != 0 {
        warn!(
            fail,
            "Init local assumed-environment check reported failures — NOT writing snapshot"
        );
        return;
    }

    let hash = init_closure_hash(search_paths);
    let header = clean_kernel::env::SnapshotHeader::current(hash);
    let path = snapshot_path(dir);
    // R1-SNAP: attest the local check that just succeeded (the fail==0
    // gate above). save_snapshot seals this claim into a receipt whose digest
    // it computes over the exact env bytes written; load_snapshot refuses any
    // snapshot without it. `verified_at` is diagnostic only — the binding is
    // content-derived and carries no timestamp.
    let attestation = clean_kernel::env::SnapshotAttestation {
        scope: "typecheck_constants_full (local-assumed-env): each Init declaration's \
                type inhabits a Sort and its value has that type, replayed in Lean's \
                order with each Init inductive block rebuilt by the kernel and compared \
                with its stored members, ASSUMING every declaration outside Init; not \
                add_decl, not a dependency-closed replay (preload_init_with_snapshot \
                cold path, fail==0)"
            .to_string(),
        decls_verified: pass as u64,
        verified_at: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| format!("unix:{}", d.as_secs()))
            .unwrap_or_else(|_| "unix:unknown".to_string()),
    };
    match env.save_snapshot(&path, header, Some(&attestation)) {
        Ok(()) => info!(path = %path.display(), "wrote Init .clean-cache snapshot"),
        Err(e) => warn!(err = %e, "failed to write Init snapshot"),
    }
}

/// Names of every constant/inductive/constructor/recursor currently in `env`.
/// On the snapshot cold path Init is the only thing loaded, so this is exactly
/// the Init closure to re-verify before writing the snapshot.
fn init_constant_names(env: &Environment) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for ci in env.constants() {
        names.insert(ci.name.to_string());
    }
    for ind in env.inductives() {
        names.insert(ind.name.to_string());
    }
    for c in env.constructors() {
        names.insert(c.name.to_string());
    }
    for r in env.recursors() {
        names.insert(r.name.to_string());
    }
    names
}

/// Verify a single .olean module in isolation (fresh environment per module).
pub fn verify_one_isolated(
    olean_path: &Path,
    root: &Path,
    search_paths: &[PathBuf],
) -> ModuleResult {
    let module_name = module_name_from_path(olean_path, root);
    let start = Instant::now();
    let mut env = Environment::default();
    if !search_paths.is_empty() {
        let _ = load_module_with_deps_with_import_policy(
            &mut env,
            "Init",
            search_paths,
            recheck_policy(),
        );
    }
    let summary: Result<LoadSummary, _> = crate::import::load_olean_file(&mut env, olean_path);
    let elapsed = start.elapsed();
    let rel_path = relative_display(olean_path, root);
    match summary {
        Ok(ls) => {
            let tc = TypeChecker::new(&env);
            let mut tc_pass = 0usize;
            let mut tc_fail = 0usize;
            let mut tc_errors = BTreeMap::new();
            for ci in env.constants() {
                match tc.infer_type(&ci.type_) {
                    Ok(_) => tc_pass += 1,
                    Err(e) => {
                        tc_fail += 1;
                        tc_errors.insert(ci.name.to_string(), format!("{e:?}"));
                    }
                }
            }
            ModuleResult {
                path: rel_path,
                module_name,
                load_ok: true,
                constants_added: ls.added_constants,
                constants_skipped: ls.skipped_constants.len(),
                tc_pass,
                tc_fail,
                elapsed_ms: elapsed.as_millis() as u64,
                load_error: None,
                tc_errors,
            }
        }
        Err(e) => ModuleResult {
            path: rel_path,
            module_name,
            load_ok: false,
            constants_added: 0,
            constants_skipped: 0,
            tc_pass: 0,
            tc_fail: 0,
            elapsed_ms: elapsed.as_millis() as u64,
            load_error: Some(format!("{e}")),
            tc_errors: BTreeMap::new(),
        },
    }
}

#[cfg(test)]
mod option_b_tests {
    //! Validates the verify-batch O(new) threaded new-constant scan logic (the
    //! consumer in `verify_one_module_with_mode_shared`): union every per-load
    //! `added_names`, keep only names not already in `known`, and INCLUDE the
    //! synthetic `<regenerated-no-confusion>` summary the loader folds in at
    //! `load.rs` for the post-registration auto-generated constants. A bug that
    //! dropped that summary would silently under-count `tc_pass`. The companion
    //! kernel test `tests2::no_confusion_value_tests::test_regenerate_returns_inserted_names`
    //! validates that those names ARE captured; the in-path `debug_assert_eq!`
    //! against `collect_new_env_names` is the runtime backstop on real loads.
    use super::*;
    use clean_kernel::name::Name;

    fn summary_with(names: &[&str]) -> LoadSummary {
        let mut s = LoadSummary::empty();
        s.added_names = names.iter().map(|n| Name::from_string(n)).collect();
        s
    }

    /// The threaded union must: dedup a name across summaries, drop names already
    /// in `known`, and include the synthetic no-confusion summary's names.
    #[test]
    fn test_threaded_added_names_union_dedups_and_includes_regen() {
        let summaries = vec![
            summary_with(&["A", "B"]),
            summary_with(&["B", "C"]), // B duplicated across summaries
            {
                // The synthetic summary load.rs pushes for regenerate_missing_no_confusion.
                let mut s = summary_with(&["Foo.noConfusionType", "Foo.noConfusion"]);
                s.module_name = Some("<regenerated-no-confusion>".to_string());
                s
            },
        ];

        // "A" was already registered by a prior module.
        let mut known: HashSet<String> = HashSet::new();
        known.insert("A".to_string());

        // Exactly the consumer's loop in verify_one_module_with_mode_shared.
        let mut threaded: BTreeSet<String> = BTreeSet::new();
        for s in &summaries {
            for n in &s.added_names {
                let ns = n.to_string();
                if known.insert(ns.clone()) {
                    threaded.insert(ns);
                }
            }
        }

        let expected: BTreeSet<String> = ["B", "C", "Foo.noConfusionType", "Foo.noConfusion"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(
            threaded, expected,
            "threaded scan must dedup vs known + across summaries and include the regen summary"
        );
        // `known` is advanced by exactly the newly-seen names (A was pre-known).
        assert!(known.contains("B") && known.contains("Foo.noConfusion"));
    }

    /// An already-visited module contributes no summary (empty added_names),
    /// so the threaded scan yields nothing new — matching the O(new) intent.
    #[test]
    fn test_threaded_empty_for_already_known() {
        let summaries = vec![summary_with(&["A", "B"])];
        let mut known: HashSet<String> = ["A", "B"].iter().map(|s| s.to_string()).collect();
        let mut threaded: BTreeSet<String> = BTreeSet::new();
        for s in &summaries {
            for n in &s.added_names {
                let ns = n.to_string();
                if known.insert(ns.clone()) {
                    threaded.insert(ns);
                }
            }
        }
        assert!(threaded.is_empty());
    }

    /// Regression for the verify-batch double-load bug: when the verified root
    /// IS the `Init` tree (or a subtree of it), `root_is_init_tree` must return
    /// true so the caller suppresses the redundant separate `Init` pre-load.
    /// Before the fix, `<tc>/lib/lean/Init` was treated as a sibling that merely
    /// imports Init, so every constant hit the duplicate branch and the batch
    /// reported `constants_added=0` / `tc_pass=0`.
    #[test]
    fn test_root_is_init_tree_detects_init_root() {
        // The exact reported invocation root.
        assert!(root_is_init_tree(Path::new(
            "$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean/Init"
        )));
        // A subtree of Init still IS Init's own closure.
        assert!(root_is_init_tree(Path::new("/tc/lib/lean/Init/Data/Nat")));
        // Bare basename.
        assert!(root_is_init_tree(Path::new("Init")));
    }

    /// A directory that merely *imports* Init (no `Init` component in its path)
    /// must NOT be misdetected — the separate pre-load is still required there.
    #[test]
    fn test_root_is_init_tree_rejects_non_init_root() {
        assert!(!root_is_init_tree(Path::new("/tc/lib/lean/Mathlib")));
        assert!(!root_is_init_tree(Path::new("/tc/lib/lean")));
        assert!(!root_is_init_tree(Path::new("/home/user/MyProject/build")));
        // Substring-but-not-component must not match.
        assert!(!root_is_init_tree(Path::new("/tc/lib/lean/InitFoo")));
    }

    /// `topological_sort` must place a module AFTER every module it transitively
    /// imports, even when the dependency is reached through an intermediate. This
    /// is the property `build_dependency_order` relies on after `expand_import_graph`
    /// pulls the intermediate into the graph: target `A` imports intermediate `C`
    /// which imports target `B`, so the order must be `B`-before-`A`. Before the
    /// transitive-expansion fix, `A` (importing only the non-target `C`) had
    /// in-degree 0 and could be emitted before `B`, making `B`'s constants
    /// `UnknownConst` during cumulative-env replay.
    #[test]
    fn test_topological_sort_respects_transitive_dependency_through_intermediate() {
        let mut modules: HashMap<String, (PathBuf, Vec<String>)> = HashMap::new();
        let p = |s: &str| PathBuf::from(format!("/r/{s}.olean"));
        // A -> C -> B (B depends on nothing).
        modules.insert("A".to_string(), (p("A"), vec!["C".to_string()]));
        modules.insert("C".to_string(), (p("C"), vec!["B".to_string()]));
        modules.insert("B".to_string(), (p("B"), vec![]));

        let ordered = topological_sort(&modules);
        let pos = |n: &str| ordered.iter().position(|m| m == n).expect("module present");
        assert!(pos("B") < pos("C"), "B must precede C: {ordered:?}");
        assert!(pos("C") < pos("A"), "C must precede A: {ordered:?}");
        // The transitive consequence the fix guarantees for the filtered targets.
        assert!(
            pos("B") < pos("A"),
            "B must precede A transitively: {ordered:?}"
        );
    }

    fn stdlib_fixture_root() -> PathBuf {
        // CARGO_MANIFEST_DIR = <root>/crates/clean-olean
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.13.0/stdlib")
    }

    /// `build_import_closures` must include the module itself, pull in transitive
    /// imports, and — the property the incremental cache relies on — keep
    /// independent modules out of each other's closures, so a change to one does
    /// NOT invalidate the other. The committed stdlib fixtures form the tree
    /// `Init/Char → Init` and `Init/Option → Init` with Char ⟂ Option.
    #[test]
    fn test_build_import_closures_self_transitive_and_independent() {
        let root = stdlib_fixture_root();
        let init = root.join("Init.olean");
        let char_m = root.join("Init/Char.olean");
        let option_m = root.join("Init/Option.olean");
        // Fixtures are committed: a checkout without them is broken, so fail
        // rather than report `ok` for a test that measured nothing.
        assert!(
            char_m.exists() && option_m.exists(),
            "committed stdlib fixtures missing under {}",
            root.display()
        );

        let closures =
            build_import_closures(&[init.clone(), char_m.clone(), option_m.clone()], &root);

        let char_cl = closures.get(&char_m).expect("Char closure present");
        assert!(
            char_cl.contains(&char_m),
            "a module is in its own closure: {char_cl:?}"
        );
        assert!(
            char_cl.contains(&init),
            "Char transitively imports Init: {char_cl:?}"
        );
        assert!(
            !char_cl.contains(&option_m),
            "Char must NOT contain the independent module Option (cache isolation): {char_cl:?}"
        );

        let option_cl = closures.get(&option_m).expect("Option closure present");
        assert!(option_cl.contains(&init) && option_cl.contains(&option_m));
        assert!(
            !option_cl.contains(&char_m),
            "Option must NOT contain Char (cache isolation): {option_cl:?}"
        );

        // Closures are sorted (deterministic cache key) and self-consistent.
        let mut sorted = char_cl.clone();
        sorted.sort();
        assert_eq!(*char_cl, sorted, "closure members must be sorted");
    }

    /// CORRECTNESS regression for the incremental-cache stale-reuse gap: a
    /// dependency that resolves OUTSIDE `root` (stdlib / sibling Lake package /
    /// toolchain) must enter the closure when its search path is supplied — so a
    /// change to it re-keys the dependent. The root-only `build_import_closures`
    /// MISSED it (root-only resolution), which is exactly the bug.
    ///
    /// Layout (split the committed Char→Init fixture across two dirs):
    ///   root/Init/Char.olean      (the target; imports Init)
    ///   deproot/Init.olean        (the out-of-root dependency)
    #[test]
    fn test_closures_with_search_paths_include_out_of_root_dep() {
        let fixture = stdlib_fixture_root();
        let src_char = fixture.join("Init/Char.olean");
        let src_init = fixture.join("Init.olean");
        // Fixtures are committed: a checkout without them is broken, so fail
        // rather than report `ok` for a test that measured nothing.
        assert!(
            src_char.exists() && src_init.exists(),
            "committed stdlib fixtures missing under {}",
            fixture.display()
        );

        let tmp = tempfile::tempdir().expect("tempdir");
        let root = tmp.path().join("root");
        let deproot = tmp.path().join("deproot");
        std::fs::create_dir_all(root.join("Init")).expect("mkdir root/Init");
        std::fs::create_dir_all(&deproot).expect("mkdir deproot");
        let char_m = root.join("Init/Char.olean");
        let init_m = deproot.join("Init.olean");
        std::fs::copy(&src_char, &char_m).expect("copy Char");
        std::fs::copy(&src_init, &init_m).expect("copy Init");

        // Root-only: Init is NOT under `root`, so the closure misses it (the bug).
        let root_only = build_import_closures(std::slice::from_ref(&char_m), &root);
        let cl_root_only = root_only.get(&char_m).expect("Char closure present");
        assert!(
            !cl_root_only.contains(&init_m),
            "root-only closure must NOT see the out-of-root Init (documents the gap): {cl_root_only:?}"
        );

        // With the dep search path supplied, the out-of-root Init IS a closure
        // member, so a change to it re-keys Char's cache entry.
        let with_paths = build_import_closures_with_search_paths(
            std::slice::from_ref(&char_m),
            &root,
            &[root.as_path(), deproot.as_path()],
        );
        let cl = with_paths.get(&char_m).expect("Char closure present");
        assert!(
            cl.contains(&char_m),
            "a module is in its own closure: {cl:?}"
        );
        assert!(
            cl.contains(&init_m),
            "out-of-root Init must be a hashed closure member: {cl:?}"
        );
    }
}

#[cfg(test)]
mod snapshot_tests {
    //! End-to-end `.clean-cache` Init snapshot tests over the committed stdlib
    //! fixture: cold full-validation write -> warm restore, env-equality of
    //! snapshot-load vs fresh-load, and header-mismatch fallback.
    use super::*;

    fn fixture_init_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.13.0/stdlib")
    }

    /// A search-path list pointing at the Init fixture, with a non-Init `root`
    /// so `preload_init_with_snapshot` actually performs the Init pre-load.
    ///
    /// The Init fixture is committed, so its absence fails the caller instead of
    /// letting it return `ok` having measured nothing.
    fn fixture_setup() -> (PathBuf, Vec<PathBuf>) {
        let stdlib = fixture_init_root();
        assert!(
            stdlib.join("Init.olean").exists(),
            "committed Init fixture missing under {}",
            stdlib.display()
        );
        // root: a sibling temp dir that does NOT contain Init.
        let root = std::env::temp_dir().join(format!("clean-snap-root-{}", std::process::id()));
        std::fs::create_dir_all(&root).expect("create the snapshot root temp dir");
        (root, vec![stdlib])
    }

    fn temp_cache_dir(tag: &str) -> PathBuf {
        std::env::temp_dir().join(format!("clean-snap-cache-{tag}-{}", std::process::id()))
    }

    /// A standalone synthetic "Init-like" env used to stand in for a fully
    /// re-verified Init closure. The committed fixture's `Init.olean` is partial
    /// (its `Init/Prelude.olean` dependency is absent), so a real Init load
    /// cannot complete in-tree — we therefore seed the snapshot with a known
    /// env and assert the WARM restore + GATE behaviour, which is exactly the
    /// load-time half under test. The full cold load+re-verify path is exercised
    /// against a real toolchain in the network "PROVE IT" run.
    fn synthetic_init_env(paths: &[PathBuf]) -> Environment {
        use clean_kernel::expr::Expr;
        use clean_kernel::name::Name;
        use clean_kernel::Declaration;
        let mut env = Environment::default();
        let init = resolve_olean_on_paths("Init", paths).expect("fixture Init must resolve");
        let bytes = std::fs::read(init).expect("fixture Init must be readable");
        let world = crate::import::part_world("Init", &bytes)
            .expect("fixture Init must have a supported world")
            .expect("fixture Init must have a Lean world");
        crate::declare_environment_world(&mut env, world)
            .expect("seed must use the fixture's universe algebra before checking declarations");
        for i in 0..50u32 {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(&format!("Init.Synthetic.d{i}")),
                level_params: vec![],
                type_: Expr::type_(),
                value: Expr::prop(),
                is_reducible: true,
            })
            .expect("synthetic snapshot declaration must pass the kernel checker");
        }
        env
    }

    /// Seed `cache/init.snapshot` from `env` with a header whose closure hash
    /// matches `paths` (so the warm gate accepts it) and a test attestation
    /// (so the R1-SNAP receipt gate accepts it — the seeded env stands in for
    /// a re-verified one). Optionally mutate the header (tamper) before
    /// writing.
    fn seed_snapshot(
        cache: &Path,
        paths: &[PathBuf],
        env: &Environment,
        mutate: impl FnOnce(&mut clean_kernel::env::SnapshotHeader),
    ) {
        let mut header = clean_kernel::env::SnapshotHeader::current(init_closure_hash(paths));
        mutate(&mut header);
        let attestation = clean_kernel::env::SnapshotAttestation {
            scope: "test seed: synthetic env standing in for a re-verified Init".to_string(),
            decls_verified: env.constants().count() as u64,
            verified_at: "test".to_string(),
        };
        env.save_snapshot(&cache.join("init.snapshot"), header, Some(&attestation))
            .expect("seed snapshot write must succeed");
    }

    /// Seed a RECEIPT-LESS snapshot (no attestation): simulates a snapshot
    /// nothing ever claimed to have re-verified. The warm gate must refuse it.
    fn seed_snapshot_unreceipted(cache: &Path, paths: &[PathBuf], env: &Environment) {
        let header = clean_kernel::env::SnapshotHeader::current(init_closure_hash(paths));
        env.save_snapshot(&cache.join("init.snapshot"), header, None)
            .expect("seed snapshot write must succeed");
    }

    #[test]
    fn test_closure_hash_is_deterministic_and_path_sensitive() {
        let (root, paths) = fixture_setup();
        let h1 = init_closure_hash(&paths);
        let h2 = init_closure_hash(&paths);
        assert_eq!(h1, h2, "closure hash must be deterministic");
        assert!(!h1.is_empty(), "closure hash must be non-empty");
        // Empty search paths => no files resolved => different (kernel-version-only) hash.
        let empty = init_closure_hash(&[]);
        assert_ne!(h1, empty, "hash must depend on the resolved closure files");
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_warm_path_restores_identical_env_from_matching_snapshot() {
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("roundtrip");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        // Seed a snapshot whose header matches the current run.
        let fresh = synthetic_init_env(&paths);
        seed_snapshot(&cache, &paths, &fresh, |_| {});

        // Warm run: env empty + matching snapshot => restore from snapshot.
        let mut warm = Environment::default();
        preload_init_with_snapshot(
            &mut warm,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );

        // (c) snapshot-load env IDENTICAL to the seeded env: same constant count
        // + matching constant types.
        assert_eq!(
            warm.constants().count(),
            fresh.constants().count(),
            "warm snapshot env constant count must equal the seeded env"
        );
        assert!(fresh.constants().next().is_some(), "seed must be non-empty");
        assert_eq!(warm.lean_level_profile(), fresh.lean_level_profile());
        assert_eq!(
            crate::environment_world(&warm),
            crate::environment_world(&fresh)
        );
        for ci in fresh.constants() {
            let got = warm
                .get_const(&ci.name)
                .expect("warm env must contain every seeded constant");
            assert_eq!(got.type_, ci.type_, "constant type must round-trip");
        }

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_warm_path_refuses_a_receipted_snapshot_with_another_universe_algebra() {
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("wrong-algebra");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        let mut seeded = synthetic_init_env(&paths);
        let fixture_profile = seeded.lean_level_profile();
        let wrong_profile = Environment::default().lean_level_profile();
        assert_ne!(
            fixture_profile, wrong_profile,
            "control must change the algebra"
        );
        seeded.set_lean_level_profile(wrong_profile);
        seed_snapshot(&cache, &paths, &seeded, |_| {});

        // Header and receipt are valid: only the source-world algebra is wrong.
        let path = cache.join("init.snapshot");
        let before = std::fs::read(&path).expect("seed snapshot must be readable");
        let expected = clean_kernel::env::SnapshotHeader::current(init_closure_hash(&paths));
        match Environment::load_snapshot(
            &path,
            &expected,
            clean_kernel::env::SnapshotReceiptPolicy::RequireReceipt,
        )
        .expect("snapshot must decode")
        {
            clean_kernel::env::SnapshotLoadOutcome::Loaded(env) => {
                assert_eq!(env.constants().count(), 50);
                assert_eq!(env.lean_level_profile(), wrong_profile);
            }
            other => panic!("control: header and receipt must be accepted: {other:?}"),
        }

        let mut warm = Environment::default();
        preload_init_with_snapshot(
            &mut warm,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );
        assert_eq!(
            warm.constants().count(),
            0,
            "wrong-algebra snapshot must be refused"
        );
        assert_eq!(
            std::fs::read(path).expect("snapshot must remain readable"),
            before
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_elision_disables_warm_snapshot_restore() {
        // Under proof-value elision the warm path MUST be skipped: a snapshot is
        // a full-resident image, so restoring it would re-inflate the very
        // values being elided. We seed a MATCHING snapshot (the warm gate would
        // otherwise accept it and restore its 50 synthetic constants), then run
        // the preload with `OpaqueOnly`. The warm restore must NOT fire; the
        // cold path runs against the partial fixture Init (which cannot load
        // fully), so the env ends up EMPTY — proving the snapshot was bypassed.
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("elide-warm");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        let seeded = synthetic_init_env(&paths);
        seed_snapshot(&cache, &paths, &seeded, |_| {});

        // Control: with `None`, the matching snapshot IS restored (50 consts).
        let mut none_env = Environment::default();
        preload_init_with_snapshot(
            &mut none_env,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );
        assert_eq!(
            none_env.constants().count(),
            seeded.constants().count(),
            "control: with None the matching snapshot must be restored"
        );

        // Under elision: warm path skipped -> snapshot's 50 constants ABSENT.
        let mut elided_env = Environment::default();
        preload_init_with_snapshot(
            &mut elided_env,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::OpaqueOnly,
        );
        assert_eq!(
            elided_env.constants().count(),
            0,
            "elision must bypass the warm snapshot restore (its constants must \
             be absent); env reflects the cold elided load of the partial fixture"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_elision_does_not_write_snapshot() {
        // Even with --full-validation, an elided cold load must NOT persist a
        // snapshot: the resident env is missing the elided values, so writing it
        // would let a later `none` run restore a value-stripped image as if it
        // were a complete, fully-resident Init.
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("elide-nowrite");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        let mut env = Environment::default();
        preload_init_with_snapshot(
            &mut env,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::OpaqueAndTheorem,
        );
        assert!(
            !cache.join("init.snapshot").exists(),
            "elision must NOT write a snapshot (elided env is not a complete image)"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_load_only_run_does_not_write_snapshot() {
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("noload");
        let _ = std::fs::remove_dir_all(&cache);

        // full_validation = false => snapshot MUST NOT be written (write is
        // gated on a successful local assumed-environment check this run). No
        // snapshot seeded, so
        // the warm path is a miss and the cold path runs with the write gated.
        let mut env = Environment::default();
        preload_init_with_snapshot(
            &mut env,
            &root,
            &paths,
            Some(&cache),
            false,
            0,
            ProofValueElision::None,
        );
        assert!(
            !cache.join("init.snapshot").exists(),
            "snapshot must NOT be written without --full-validation re-verify"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_tampered_snapshot_version_is_discarded_not_reused() {
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("tamper");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        // Seed a snapshot with a BUMPED (future) snapshot_version header.
        let seeded = synthetic_init_env(&paths);
        seed_snapshot(&cache, &paths, &seeded, |h| {
            h.snapshot_version = clean_kernel::env::SNAPSHOT_VERSION + 1;
        });

        // Warm run MUST discard the stale snapshot and fall back to the (cold)
        // full load. The fixture Init cannot load fully, so the env ends up
        // EMPTY — proving the stale snapshot's 50 constants were NOT reused.
        let mut warm = Environment::default();
        preload_init_with_snapshot(
            &mut warm,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );
        assert_eq!(
            warm.constants().count(),
            0,
            "version-mismatched snapshot must NOT be reused (its 50 constants \
             must be absent); env reflects the fallback full load, not the snapshot"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_closure_hash_mismatch_is_discarded_not_reused() {
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("hashmm");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        // Seed a snapshot whose closure hash is WRONG for `paths`.
        let seeded = synthetic_init_env(&paths);
        seed_snapshot(&cache, &paths, &seeded, |h| {
            h.init_closure_blake3 = "deadbeef-wrong-closure".to_string();
        });

        let mut warm = Environment::default();
        preload_init_with_snapshot(
            &mut warm,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );
        assert_eq!(
            warm.constants().count(),
            0,
            "closure-hash-mismatched snapshot must NOT be reused"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn test_receiptless_snapshot_is_refused_not_reused() {
        // R1-SNAP: a snapshot with a MATCHING header but NO verification
        // receipt (nothing ever attested a re-verification produced it) must
        // be refused by the warm path. The fixture Init cannot load fully, so
        // the env ends up EMPTY — proving the unreceipted snapshot's 50
        // constants were NOT reused.
        let (root, paths) = fixture_setup();
        let cache = temp_cache_dir("norcpt");
        let _ = std::fs::remove_dir_all(&cache);
        std::fs::create_dir_all(&cache).expect("mkdir cache");

        let seeded = synthetic_init_env(&paths);
        seed_snapshot_unreceipted(&cache, &paths, &seeded);

        // Control: the same env seeded WITH a receipt IS restored — so the
        // refusal below is attributable to the receipt gate alone.
        {
            let mut control = Environment::default();
            seed_snapshot(&cache, &paths, &seeded, |_| {});
            preload_init_with_snapshot(
                &mut control,
                &root,
                &paths,
                Some(&cache),
                true,
                0,
                ProofValueElision::None,
            );
            assert_eq!(
                control.constants().count(),
                seeded.constants().count(),
                "control: the receipted twin of this snapshot must be restored"
            );
            seed_snapshot_unreceipted(&cache, &paths, &seeded);
        }

        let mut warm = Environment::default();
        preload_init_with_snapshot(
            &mut warm,
            &root,
            &paths,
            Some(&cache),
            true,
            0,
            ProofValueElision::None,
        );
        assert_eq!(
            warm.constants().count(),
            0,
            "receipt-less snapshot must NOT be reused (its 50 constants must \
             be absent); env reflects the fallback full load, not the snapshot"
        );

        let _ = std::fs::remove_dir_all(&cache);
        let _ = std::fs::remove_dir_all(&root);
    }
}
