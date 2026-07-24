// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Load parsed .olean modules into the clean kernel environment.
//!
//! This bridges the low-level parsed structures into the kernel's
//! `Environment` by converting names, levels, and expressions.
//!
//! # Caching
//! Module loading involves two expensive operations:
//! 1. **Parsing**: Reading and interpreting the .olean binary format (~40% of time)
//! 2. **Loading**: Converting and registering constants in the environment (~60% of time)
//!
//! The `ModuleCache` can be used to cache parsed modules across multiple
//! `load_module_with_deps` calls, avoiding re-parsing when the same module
//! is needed by multiple dependents.

mod convert;
mod convert_direct;
mod convert_expr;
mod convert_expr_direct;
mod load;
mod load_parse;
mod load_register;
mod parse;
mod path;
mod policy;

#[cfg(test)]
mod module_cache_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_class_ext_import;
#[cfg(test)]
mod tests_external_packages;
#[cfg(test)]
mod tests_instance_ext_import;
#[cfg(test)]
mod tests_membership_carrier_import;

use crate::module::ParsedModule;
use hashbrown::HashMap;
use smallvec::SmallVec;
use std::path::Path;
use std::sync::{Arc, RwLock};

// Re-export public API
pub use convert::is_projection_fn_body;
pub use load::{
    load_module_with_deps, load_module_with_deps_bounded, load_module_with_deps_bounded_shared,
    load_module_with_deps_bounded_shared_with_policy, load_module_with_deps_cached,
    load_module_with_deps_parallel, load_module_with_deps_shared,
    load_module_with_deps_shared_with_policy, load_module_with_deps_with_import_policy,
    load_modules_with_deps, load_modules_with_deps_with_import_policy, load_olean_file,
    load_olean_file_with_import_policy,
};
pub use load_register::{
    is_compiler_ir_name, load_parsed_module, load_parsed_module_with_import_policy,
};
pub use parse::{
    discover_olean_parts, parse_imports_and_const_names_only, parse_imports_only, parse_module,
    parse_module_file, parse_module_incremental, parse_module_incremental_types_only,
    parse_module_parts, parse_module_types_only,
};
pub use path::{
    active_stdlib_toolchain, alias_resolvable_toolchain_versions, default_search_paths,
    default_toolchain_versions, find_module_olean, toolchain_versions_from_search_paths,
    ActiveStdlibToolchain, SearchPathBuilder,
};
pub use policy::{ImportKinds, OleanImportPolicy, UnpinnedOleanImportPolicy};

// Test-only re-exports: used by import/tests.rs via `use super::*`.
#[cfg(test)]
pub(crate) use convert::decl_to_constant_info;
pub use convert::{
    convert_parsed_constant_to_const_info, convert_parsed_constant_to_declaration,
    convert_parsed_constant_to_type_stub, ConstantConvertSession,
};
#[cfg(test)]
pub(crate) use convert_expr::convert_expr;
/// The canonical, deterministic FVar/MVar-name hash used by the EAGER olean
/// import (`convert_expr_direct::read_and_convert_expr`). Re-exported so the
/// lazy `.mathverse` shard builder can hash FVar names IDENTICALLY — any other
/// hasher gives a different `FVarId` for the same name, which diverges the
/// reconstructed `Expr` identity and breaks eager-vs-lazy verdict parity.
pub use convert_expr::hash_str;
#[cfg(test)]
pub(crate) use convert_expr_direct::read_and_convert_expr;
#[cfg(test)]
pub(crate) use load_parse::parse_load_module;
#[cfg(test)]
pub(crate) use load_register::load_module_direct_with_cache;
#[cfg(test)]
pub(crate) use path::{
    collect_default_search_paths, discover_lake_package_paths, module_name_from_path,
};

/// Errors that can arise while importing an .olean module into the kernel environment.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ImportError {
    /// Error parsing the .olean file.
    #[error("parse error: {0}")]
    Parse(#[from] crate::OleanError),
    /// Error adding declaration to environment.
    #[error("environment error: {0}")]
    Env(#[from] clean_kernel::env::EnvError),
    /// I/O error reading the file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// An .olean file could not be read from disk (the path is known).
    ///
    /// Unlike [`ImportError::Io`], this names WHICH file failed — a
    /// Mathlib-scale load touches thousands of `.olean` files and a pathless
    /// io error is undebuggable.
    #[error(
        "cannot read .olean file `{path}`: {source}; check that the toolchain/package \
         build output still exists (re-run `lake build`, or re-select the search path \
         via LEAN_PATH / MATHLIB_PATH)"
    )]
    FileUnreadable {
        /// Path of the .olean file that could not be read.
        path: std::path::PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },
    /// Module not found in search paths.
    #[error("module {module} not found{}", render_module_search(searched))]
    ModuleNotFound {
        /// Name of the module that was not found.
        module: String,
        /// Paths that were searched.
        searched: Vec<std::path::PathBuf>,
    },
    /// Module graph is outside the bounded import surface.
    #[error("unsupported module {module}: {reason}")]
    UnsupportedModule {
        /// Name of the requested root module.
        module: String,
        /// Human-readable explanation.
        reason: String,
    },
    /// Import policy rejected unpinned external `.olean` constants.
    #[error(
        "import policy rejected unpinned external .olean import for {module}: \
         {olean_constants} .olean constants, {clean_payload_constants} Clean payload constants; \
         no pin/hash verification was supplied"
    )]
    UnpinnedExternalOleanRejected {
        /// Module name, or `<unknown>` when the load path could not infer it.
        module: String,
        /// Number of Lean `.olean` constants that would have been registered.
        olean_constants: usize,
        /// Number of Clean payload constants that would have been registered.
        clean_payload_constants: usize,
    },
    /// Constant declaration missing its type.
    #[error("missing type for constant {0}")]
    MissingType(String),
    /// Constant declaration missing its value.
    #[error("missing value for constant {0}")]
    MissingValue(String),
    /// Constant contains unsupported metavariables.
    #[error("unsupported metavariable in constant {0}")]
    UnsupportedMVar(String),
    /// Expression conversion from parsed format failed.
    #[error("expression conversion failed for {name}: {message}")]
    ExprConversion {
        /// Name of the constant being converted.
        name: String,
        /// Error message.
        message: String,
    },
    /// Universe level conversion failed.
    #[error("level conversion failed for {name}: {message}")]
    LevelConversion {
        /// Name of the constant being converted.
        name: String,
        /// Error message.
        message: String,
    },
}

/// Render the searched-path tail of a `ModuleNotFound` message.
///
/// Distinguishes "no search paths were discovered at all" (an environment
/// problem, not a missing module) from "the module is absent from the paths
/// that were searched", and names the env vars that extend the search.
fn render_module_search(searched: &[std::path::PathBuf]) -> String {
    if searched.is_empty() {
        ": no .olean search paths were discovered — set LEAN_PATH or MATHLIB_PATH, point \
         LEAN_PACKAGES_PATH at a lake project root, or install a Lean 4 toolchain via elan"
            .to_string()
    } else {
        format!(
            " in {} searched path(s): {:?}; if the module belongs to another package, add \
             its build/lib directory to LEAN_PATH (or LEAN_PACKAGES_PATH for a lake root)",
            searched.len(),
            searched
        )
    }
}

/// Reason a constant was skipped during import.
#[derive(Debug, Clone)]
pub struct SkippedConstant {
    /// Name of the skipped constant.
    pub name: String,
    /// Reason for skipping.
    pub reason: String,
}

/// Shared intern cache for expression deduplication across all constants in a module.
///
/// Keyed by `Expr::hash_cached()` (u32), with small-vec buckets for hash collisions.
/// Promoted from per-`convert_expr` call to per-`load_parsed_module` call so that
/// identical sub-expressions across different constants (e.g. `Nat`, `Prop`) share
/// the same `Arc<Expr>` allocation (#2383).
///
/// Wraps a `HashMap` + a running `total_entries` counter so that computing the
/// cache size is O(1) instead of the previous O(n) `values().map(len).sum()`.
/// Part of #3133.
pub(crate) struct ExprInternCache {
    pub(crate) map: HashMap<u32, SmallVec<[Arc<clean_kernel::expr::Expr>; 1]>>,
    /// Running count of total entries across all buckets.
    pub(crate) total_entries: u64,
}

impl Default for ExprInternCache {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            total_entries: 0,
        }
    }
}

impl ExprInternCache {
    /// Create a new cache pre-sized for the expected number of unique hashes.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
            total_entries: 0,
        }
    }
}

/// Statistics about expression structure sharing achieved via hash-consing
/// during olean import (#2383).
#[derive(Debug, Clone, Default)]
pub struct ExprSharingStats {
    /// Total calls to intern_expr (one per sub-expression processed)
    pub total_intern_calls: u64,
    /// Cache hits: existing Arc<Expr> reused instead of allocating
    pub cache_hits: u64,
    /// Unique expressions stored in the intern cache
    pub unique_exprs: u64,
}

impl ExprSharingStats {
    pub(crate) fn merge(&mut self, other: &ExprSharingStats) {
        self.total_intern_calls += other.total_intern_calls;
        self.cache_hits += other.cache_hits;
        self.unique_exprs += other.unique_exprs;
    }

    /// Fraction of intern calls that were cache hits (0.0 to 1.0).
    pub fn hit_rate(&self) -> f64 {
        if self.total_intern_calls == 0 {
            0.0
        } else {
            self.cache_hits as f64 / self.total_intern_calls as f64
        }
    }

    /// Estimated Arc allocations saved by deduplication.
    pub fn allocations_saved(&self) -> u64 {
        self.cache_hits
    }
}

/// Summary of an import attempt.
#[derive(Debug, Clone)]
pub struct LoadSummary {
    /// Optional module name (deduced from path)
    pub module_name: Option<String>,
    /// Names of imported modules (as strings)
    pub imports: Vec<String>,
    /// Number of successfully added constants
    pub added_constants: usize,
    /// Constants skipped due to conversion issues
    pub skipped_constants: Vec<SkippedConstant>,
    /// Constants ignored because they already exist in the environment
    pub duplicate_constants: usize,
    /// Expression structure sharing statistics from hash-consing (#2383)
    pub expr_sharing: ExprSharingStats,
    /// Names added to the env by THIS load — constants, inductives, constructors,
    /// and recursors — captured at the `tag_inserted_constants` chokepoint. Lets
    /// the verify-batch new-constant scan stay O(new) instead of re-scanning the
    /// whole growing env per module. Empty for an already-visited (short-circuited)
    /// module; the regenerated no-confusion constants are folded in as a synthetic
    /// summary by `load_module_with_deps_bounded_shared`.
    pub added_names: Vec<clean_kernel::name::Name>,
    /// Persistent-extension entries a typed decoder recognized but could not
    /// decode for this module (see `ParsedExtension::undecoded_entries`).
    /// Such entries degrade to the pre-decoder behavior (absent from the
    /// restored state, never guessed at); a non-zero count here is the loud
    /// signal that extension state was lost.
    pub extension_undecoded_entries: usize,
    /// Human-readable descriptions of `Lean.classExtension` entries whose
    /// decoded `outParams` DISAGREE with a class already registered under the
    /// same name (a hand-registered kernel twin, or an earlier lane). The
    /// import bridge keeps the first registration (first-writer-wins) and does
    /// not overwrite; a non-empty list is the loud signal that Clean's
    /// hand-authored class metadata drifted from the real Lean `.olean` — a
    /// fidelity bug to reconcile, never a silent mismatch.
    pub class_out_param_mismatches: Vec<String>,
}

impl LoadSummary {
    pub(crate) fn empty() -> Self {
        Self {
            module_name: None,
            imports: Vec::new(),
            added_constants: 0,
            skipped_constants: Vec::new(),
            duplicate_constants: 0,
            expr_sharing: ExprSharingStats::default(),
            added_names: Vec::new(),
            extension_undecoded_entries: 0,
            class_out_param_mismatches: Vec::new(),
        }
    }
}

/// Cache entry for a parsed module
#[derive(Clone)]
pub(crate) struct CacheEntry {
    /// The parsed module data (Arc to avoid expensive clones)
    module: Arc<ParsedModule>,
    /// File modification time when cached
    mtime: Option<std::time::SystemTime>,
}

/// Maximum cached modules before eviction.
///
/// Mathlib has ~4000 .olean files. 8192 gives comfortable headroom for
/// Mathlib + Init + Std while preventing unbounded growth in long-running
/// server sessions that import from many lakefile projects.
const MAX_MODULE_CACHE_ENTRIES: usize = 8192;

/// Cache for parsed .olean modules.
///
/// This cache stores parsed modules to avoid re-parsing when the same
/// module is needed multiple times. It's particularly useful when loading
/// multiple modules that share dependencies.
///
/// Bounded to [`MAX_MODULE_CACHE_ENTRIES`]; oldest entries (by HashMap
/// iteration order) are evicted when the limit is reached.
///
/// # Example
///
/// ```text
/// use clean_olean::{ModuleCache, load_module_with_deps_cached, default_search_paths};
/// use clean_kernel::env::Environment;
///
/// let cache = ModuleCache::new();
/// let paths = default_search_paths();
///
/// // First load - parses all modules
/// let mut env1 = Environment::default();
/// load_module_with_deps_cached(&mut env1, "Init.Core", &paths, &cache)?;
///
/// // Second load - reuses cached modules
/// let mut env2 = Environment::default();
/// load_module_with_deps_cached(&mut env2, "Init.Data.List.Basic", &paths, &cache)?;
/// ```
#[derive(Default)]
pub struct ModuleCache {
    /// Map from module name to cached entry
    entries: RwLock<HashMap<String, CacheEntry>>,
}

impl ModuleCache {
    /// Create a new empty module cache.
    ///
    /// # ENSURES
    /// - Returns an empty cache with `len() == 0`
    /// - Thread-safe: can be shared across threads with `&ModuleCache`
    pub fn new() -> Self {
        Self {
            entries: RwLock::new(HashMap::new()),
        }
    }

    /// Get the number of cached modules.
    ///
    /// # ENSURES
    /// - Returns count of entries in cache (may be stale by return time)
    pub fn len(&self) -> usize {
        self.entries.read().unwrap_or_else(|e| e.into_inner()).len()
    }

    /// Check if the cache is empty.
    ///
    /// # ENSURES
    /// - Returns true iff `len() == 0` at time of call
    pub fn is_empty(&self) -> bool {
        self.entries
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .is_empty()
    }

    /// Clear all cached modules.
    ///
    /// # ENSURES
    /// - After return, `is_empty() == true`
    /// - All cached entries are dropped
    pub fn clear(&self) {
        self.entries
            .write()
            .unwrap_or_else(|e| e.into_inner())
            .clear();
    }

    /// Get cached module if available and not stale.
    /// Returns Arc to avoid expensive clones of ParsedModule.
    pub(crate) fn get(&self, module: &str, path: &Path) -> Option<Arc<ParsedModule>> {
        let mtime = std::fs::metadata(path)
            .ok()
            .and_then(|metadata| metadata.modified().ok());
        let mut entries = self.entries.write().unwrap_or_else(|e| e.into_inner());

        match entries.get(module) {
            Some(entry) if entry.mtime.is_some() && entry.mtime == mtime => {
                Some(Arc::clone(&entry.module))
            }
            Some(_) => {
                // Drop stale entries so follow-up loads don't keep retrying outdated data.
                entries.remove(module);
                None
            }
            None => None,
        }
    }

    /// Insert a module into the cache.
    ///
    /// If the cache exceeds [`MAX_MODULE_CACHE_ENTRIES`], 1/4 of entries are
    /// evicted to bound memory in long-running server sessions (#2054).
    ///
    /// Returns Arc to the inserted module to avoid re-cloning.
    pub(crate) fn insert(
        &self,
        module: &str,
        path: &Path,
        parsed: ParsedModule,
    ) -> Arc<ParsedModule> {
        let mtime = std::fs::metadata(path).ok().and_then(|m| m.modified().ok());
        let arc_module = Arc::new(parsed);

        let entry = CacheEntry {
            module: Arc::clone(&arc_module),
            mtime,
        };

        let mut entries = self.entries.write().unwrap_or_else(|e| e.into_inner());
        if entries.len() >= MAX_MODULE_CACHE_ENTRIES {
            let to_remove = entries.len() / 4;
            let keys: Vec<String> = entries.keys().take(to_remove).cloned().collect();
            for key in keys {
                entries.remove(&key);
            }
        }
        entries.insert(module.to_string(), entry);

        arc_module
    }
}

/// Estimate the total number of constants in a module's dependency graph.
///
/// Uses known sizes for Init/Std/Mathlib module trees to avoid HashMap
/// resizing during bulk loading. Returns 0 for unknown modules (caller
/// falls back to per-module `reserve_capacity`).
///
/// Empirical data (Lean 4.28.0):
/// - Init: ~320 modules, ~57K constants
/// - Std:  ~520 modules (including Init deps), ~80K constants
/// - Mathlib: ~200K+ constants
pub(crate) fn estimate_module_graph_size(module: &str) -> usize {
    if module == "Init" || module.starts_with("Init.") {
        60_000
    } else if module == "Std" || module.starts_with("Std.") {
        90_000
    } else if module == "Mathlib" || module.starts_with("Mathlib.") {
        250_000
    } else if module == "Lean" || module.starts_with("Lean.") {
        100_000
    } else {
        // Unknown module tree — let per-module reserve_capacity handle it
        0
    }
}
