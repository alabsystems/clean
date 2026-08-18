// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-wide import-closure loading for the editor path.
//!
//! Real Lean files start with an `import` header. Elaborating them against the
//! backend's bare environment floods the editor with spurious unknown-constant
//! diagnostics, and re-loading the `.olean` closure on every keystroke is
//! unaffordable. This module loads a document's full import set ONCE — a
//! prelude base plus the shared `.olean` loader
//! ([`clean_elab::process_import_batch_with_search_paths`]) — and caches the
//! populated environment process-wide, keyed by the sorted import set plus the
//! file-derived search-path fingerprint, so every open document sharing an
//! import header shares one loaded closure.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};

/// Cache key: the canonical (sorted, deduplicated) dotted module names of a
/// document's import header plus the extra `.olean` search paths derived from
/// the document's on-disk location (its nearest Lake root). Two documents with
/// the same header in the same project share one entry; toolchain-default
/// search paths are process-stable and therefore not part of the key.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ImportClosureKey {
    modules: Vec<String>,
    search_paths: Vec<PathBuf>,
}

/// A cached load outcome. `Err` carries a human-readable reason that the
/// elaboration path surfaces as a single "imports unavailable: <reason>"
/// diagnostic. Failures are cached alongside successes so a broken header does
/// not retry an expensive load on every keystroke.
pub(crate) type ImportClosureOutcome = Result<Arc<clean_kernel::Environment>, String>;

static IMPORT_CLOSURES: OnceLock<Mutex<HashMap<ImportClosureKey, ImportClosureOutcome>>> =
    OnceLock::new();

fn cache_guard() -> MutexGuard<'static, HashMap<ImportClosureKey, ImportClosureOutcome>> {
    let cache = IMPORT_CLOSURES.get_or_init(|| Mutex::new(HashMap::new()));
    match cache.lock() {
        Ok(guard) => guard,
        // A poisoned lock means another thread panicked mid-load. The map is
        // only ever mutated by whole-entry `insert` calls, so its contents
        // remain internally consistent and safe to keep serving.
        Err(poisoned) => poisoned.into_inner(),
    }
}

/// Collect the import header of a parsed document: every module path of every
/// `import` declaration, in source order.
pub(crate) fn import_paths_of_decls(decls: &[clean_parser::SurfaceDecl]) -> Vec<Vec<String>> {
    decls
        .iter()
        .filter_map(|decl| match decl {
            clean_parser::SurfaceDecl::Import { paths, .. } => Some(paths.iter().cloned()),
            _ => None,
        })
        .flatten()
        .collect()
}

/// The shared environment for `import_paths` as seen from a document at
/// `file_path` (used to derive project-local `.olean` search paths; `None` for
/// non-`file:` documents).
///
/// Loads at most once per (import set, search-path fingerprint) pair for the
/// lifetime of the process; concurrent documents block on the same load rather
/// than duplicating it. The lock is intentionally held across the load — the
/// load is the expensive step and every waiter wants its result.
pub(crate) fn shared_import_closure(
    import_paths: &[Vec<String>],
    file_path: Option<&Path>,
) -> ImportClosureOutcome {
    let key = closure_key(import_paths, file_path);
    let mut cache = cache_guard();
    if let Some(outcome) = cache.get(&key) {
        return outcome.clone();
    }
    let outcome = load_import_closure(&key);
    cache.insert(key, outcome.clone());
    outcome
}

fn closure_key(import_paths: &[Vec<String>], file_path: Option<&Path>) -> ImportClosureKey {
    let search_paths = file_path
        .map(clean_elab::lake_import_search_paths_for_file)
        .unwrap_or_default();
    let mut modules: Vec<String> = import_paths.iter().map(|path| path.join(".")).collect();
    modules.sort();
    modules.dedup();
    ImportClosureKey {
        modules,
        search_paths,
    }
}

/// Load a closure for `key`: prelude base, then the whole import batch through
/// the shared `.olean` loader (which itself falls back to Clean's built-in
/// stub preludes per module when no `.olean` is discoverable, mirroring the
/// `clean check` frontend).
fn load_import_closure(key: &ImportClosureKey) -> ImportClosureOutcome {
    let mut env = clean_kernel::Environment::try_with_prelude()
        .map_err(|e| format!("prelude initialization failed: {e}"))?;
    let paths: Vec<Vec<String>> = key
        .modules
        .iter()
        .map(|module| module.split('.').map(str::to_owned).collect())
        .collect();
    clean_elab::process_import_batch_with_search_paths(&mut env, &paths, &key.search_paths)
        .map_err(|e| e.to_string())?;
    Ok(Arc::new(env))
}

/// Test seam: pre-populate the process-wide cache for a synthetic import set
/// so failure shaping can be exercised without a real toolchain. Use module
/// names unique to the calling test — the cache is shared across the whole
/// test process.
#[cfg(test)]
pub(crate) fn inject_outcome_for_test(
    import_paths: &[Vec<String>],
    file_path: Option<&Path>,
    outcome: ImportClosureOutcome,
) {
    let key = closure_key(import_paths, file_path);
    cache_guard().insert(key, outcome);
}
