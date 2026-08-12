// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathlib theorem import via the `.olean` bridge.
//!
//! Loads specific Mathlib theorems from `.olean` files into the kernel
//! `Environment`, verifies their presence and properties, and converts
//! them to `.mathverse` shard format. This provides a bridge from Mathlib's
//! 130K+ formalized theorems to the Mathverse Library.
//!
//! Target theorems for gamma-crown axiom proofs:
//! - Matrix multiplication associativity (`Matrix.mul_assoc`)
//! - Rat field properties (`Rat.add_comm`, `Rat.mul_comm`, etc.)
//! - Nat ordering (`Nat.le_refl`, `Nat.le_trans`)

use std::path::{Path, PathBuf};

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::{default_search_paths, load_module_with_deps, LoadSummary};

use crate::error::MathverseResult;
use crate::lean4::env_import::{import_environment, EnvImportConfig, EnvImportStats};
use crate::shard::ShardWriter;
use crate::types::ContentDomain;

// ---------------------------------------------------------------------------
// MathLib search path resolution
// ---------------------------------------------------------------------------

/// Find the Lean 4 stdlib `.olean` search path.
pub(crate) fn find_lean_lib_path() -> Option<PathBuf> {
    default_search_paths()
        .into_iter()
        .find(|p| p.join("Init/Prelude.olean").exists())
}

/// Environment variable that explicitly points at a Mathlib `.olean` build
/// directory (the `.lake/build/lib` produced by `lake build`, or by extracting
/// the `~/.cache/mathlib` `.ltar` cache). When set, it takes precedence over the
/// repo-relative / tmp fallbacks.
pub const MATHLIB_OLEAN_DIR_ENV: &str = "MATHLIB_OLEAN_DIR";

/// Return true if `dir` looks like a Mathlib `.olean` build library
/// (`Mathlib.olean` present, or a populated `Mathlib/` subdirectory).
fn is_mathlib_lib_dir(dir: &Path) -> bool {
    dir.join("Mathlib.olean").exists() || dir.join("Mathlib").is_dir()
}

/// Find Mathlib `.olean` build directory.
///
/// Resolution order:
/// 1. `MATHLIB_OLEAN_DIR` environment variable (an explicit `.lake/build/lib`,
///    such as one produced by extracting the `~/.cache/mathlib` `.ltar` cache
///    with `leantar`).
/// 2. `data/raw/mathlib4/.lake/build/lib/lean` (set up by
///    `scripts/setup_mathlib_oleans.sh`).
/// 3. `/tmp/mathlib4/.lake/build/lib/lean`.
pub(crate) fn find_mathlib_lib_path() -> Option<PathBuf> {
    if let Some(dir) = std::env::var_os(MATHLIB_OLEAN_DIR_ENV) {
        let dir = PathBuf::from(dir);
        if is_mathlib_lib_dir(&dir) {
            return Some(dir);
        }
    }

    let candidates = [
        // data/raw/mathlib4/.lake/build/lib/lean
        dirs_relative_to_repo("data/raw/mathlib4/.lake/build/lib/lean"),
        // Fallback: /tmp/mathlib4/.lake/build/lib/lean
        Some(PathBuf::from("/tmp/mathlib4/.lake/build/lib/lean")),
    ];

    candidates
        .into_iter()
        .flatten()
        .find(|candidate| is_mathlib_lib_dir(candidate))
}

/// Find all Mathlib `.olean` search paths including package dependencies.
///
/// Returns paths for the main Mathlib library plus all .lake/packages/*/
/// build outputs (Batteries, Aesop, Qq, etc.). This mirrors the MATHLIB_PATH
/// computed by `scripts/setup_mathlib_oleans.sh`.
pub(crate) fn find_mathlib_search_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();

    // Find the main Mathlib lib path
    let Some(mathlib_lib) = find_mathlib_lib_path() else {
        return paths;
    };
    paths.push(mathlib_lib.clone());

    // Walk up from the Mathlib lib dir to the enclosing `.lake` directory. This
    // is robust to both the `.lake/build/lib/lean` layout (repo checkout) and
    // the `.lake/build/lib` layout produced by extracting the `.ltar` cache.
    let lake_dir = mathlib_lib
        .ancestors()
        .find(|p| p.file_name().is_some_and(|n| n == ".lake"))
        .map(Path::to_path_buf);

    if let Some(lake_dir) = lake_dir {
        let packages_dir = lake_dir.join("packages");
        if packages_dir.is_dir() {
            if let Ok(entries) = std::fs::read_dir(&packages_dir) {
                for entry in entries.filter_map(|e| e.ok()) {
                    let pkg_lib = entry.path().join(".lake/build/lib/lean");
                    if pkg_lib.is_dir() {
                        paths.push(pkg_lib);
                        continue;
                    }
                    // Some packages may not have a /lean/ subdirectory
                    let pkg_lib_alt = entry.path().join(".lake/build/lib");
                    if pkg_lib_alt.is_dir() {
                        paths.push(pkg_lib_alt);
                    }
                }
            }
        }
    }

    paths
}

/// Resolve a path relative to the repo root (best-effort).
fn dirs_relative_to_repo(rel: &str) -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join("clean").join(rel);
    if path.exists() {
        Some(path)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Mathlib module loading
// ---------------------------------------------------------------------------

/// Result of loading Mathlib modules into an Environment.
#[derive(Clone, Debug, Default)]
pub struct MathlibLoadResult {
    /// Modules successfully loaded.
    pub loaded_modules: Vec<String>,
    /// Modules that failed to load (name, error message).
    pub failed_modules: Vec<(String, String)>,
    /// Total constants in the environment after loading.
    pub total_constants: usize,
    /// Load summaries for each module.
    pub summaries: Vec<LoadSummary>,
}

/// Load a set of Mathlib `.olean` modules into an Environment.
///
/// Requires both the Lean 4 stdlib path (for Init dependencies) and a set
/// of Mathlib search paths (main lib + package deps). Loads modules in
/// order, accumulating into one environment.
///
/// Modules that fail to load are recorded but do not abort the batch.
pub fn load_mathlib_modules(
    env: &mut Environment,
    modules: &[&str],
    lean_lib_path: &Path,
    mathlib_search_paths: &[PathBuf],
) -> MathlibLoadResult {
    let mut search_paths = vec![lean_lib_path.to_path_buf()];
    search_paths.extend_from_slice(mathlib_search_paths);
    let mut result = MathlibLoadResult::default();

    for &module in modules {
        match load_module_with_deps(env, module, &search_paths) {
            Ok(summaries) => {
                result.loaded_modules.push(module.to_string());
                result.summaries.extend(summaries);
            }
            Err(e) => {
                result
                    .failed_modules
                    .push((module.to_string(), format!("{e}")));
            }
        }
    }

    result.total_constants = env.num_constants();
    result
}

/// Load Init modules (always available from the Lean 4 toolchain) that contain
/// key theorems about Nat, ordering, and basic arithmetic.
pub fn load_init_modules(env: &mut Environment, lean_lib_path: &Path) -> MathlibLoadResult {
    let modules = &[
        "Init.Prelude",
        "Init.Core",
        "Init.Data.Nat.Basic",
        "Init.Data.Nat.Lemmas",
        "Init.Data.Int.Basic",
        "Init.Data.List.Basic",
        "Init.Data.List.Lemmas",
        "Init.PropLemmas",
        "Init.Classical",
    ];

    let search_paths = [lean_lib_path.to_path_buf()];
    let mut result = MathlibLoadResult::default();

    for &module in modules {
        match load_module_with_deps(env, module, &search_paths) {
            Ok(summaries) => {
                result.loaded_modules.push(module.to_string());
                result.summaries.extend(summaries);
            }
            Err(e) => {
                result
                    .failed_modules
                    .push((module.to_string(), format!("{e}")));
            }
        }
    }

    result.total_constants = env.num_constants();
    result
}

// ---------------------------------------------------------------------------
// Mathlib foundation module batches (Order.* / Algebra.* foundations)
// ---------------------------------------------------------------------------

/// Authoritative Mathlib **order-theory foundation** modules.
///
/// These are the lowest, most widely-depended-upon modules in Mathlib's order
/// hierarchy. Importing them as a coherent group unblocks downstream proof
/// automation that relies on `Preorder` / `PartialOrder` / `Lattice` and the
/// `le_trans` / `le_refl` / `le_antisymm` family of lemmas. Modules are listed
/// in dependency order (most fundamental first) so `load_module_with_deps`
/// resolves transitive imports predictably.
#[must_use]
pub fn mathlib_order_foundation_modules() -> &'static [&'static str] {
    &[
        "Mathlib.Order.Defs",
        "Mathlib.Order.Basic",
        "Mathlib.Order.Lattice",
        "Mathlib.Order.BoundedOrder",
    ]
}

/// Authoritative Mathlib **algebra-foundation** modules.
///
/// The core algebraic-hierarchy roots: `Monoid`, `Group`, and the basic
/// order-compatible algebra wiring. These replace the hand-written Rust algebra
/// stubs (`Semiring` / `Ring` / `CommRing` in `clean-kernel`) with real,
/// kernel-acceptable Mathlib declarations once Mathlib `.olean` files are
/// available. Listed most-fundamental first.
#[must_use]
pub fn mathlib_algebra_foundation_modules() -> &'static [&'static str] {
    &[
        "Mathlib.Algebra.Group.Defs",
        "Mathlib.Algebra.Group.Basic",
        "Mathlib.Algebra.GroupWithZero.Defs",
        "Mathlib.Algebra.Order.Monoid.Defs",
    ]
}

/// The complete Mathlib foundation batch: order foundations followed by
/// algebra foundations.
///
/// This is the highest-leverage coherent module group for proof-automation
/// unblocking (the EPIC 2 target). It is the authoritative replacement for the
/// scattered, gamma-crown-specific module list and is consumed by
/// [`load_mathlib_foundations`].
#[must_use]
pub fn mathlib_foundation_modules() -> Vec<&'static str> {
    let mut modules = Vec::new();
    modules.extend_from_slice(mathlib_order_foundation_modules());
    modules.extend_from_slice(mathlib_algebra_foundation_modules());
    modules
}

/// Foundation declarations expected to appear once the order/algebra batch is
/// imported. Each entry is `(declaration, candidate_names)` where any candidate
/// matching satisfies the expectation (Mathlib re-exports and root-namespace
/// aliases vary across versions).
///
/// Used by the fixture/real-import tests to assert that a meaningful set of
/// foundation declarations is actually present after import.
#[must_use]
pub fn mathlib_foundation_expected_decls() -> &'static [(&'static str, &'static [&'static str])] {
    &[
        ("Preorder", &["Preorder"]),
        ("PartialOrder", &["PartialOrder"]),
        ("le_trans", &["le_trans", "Preorder.le_trans"]),
        ("le_refl", &["le_refl", "Preorder.le_refl"]),
        ("le_antisymm", &["le_antisymm", "PartialOrder.le_antisymm"]),
        ("Lattice", &["Lattice"]),
        ("Monoid", &["Monoid"]),
        ("Group", &["Group"]),
        ("mul_assoc", &["mul_assoc", "Monoid.mul_assoc"]),
        ("one_mul", &["one_mul", "Monoid.one_mul"]),
    ]
}

/// Load the Mathlib order/algebra **foundation batch** into an environment.
///
/// Thin wrapper over [`load_mathlib_modules`] that loads exactly the modules in
/// [`mathlib_foundation_modules`]. Requires the Lean 4 stdlib path (for Init
/// deps) and the Mathlib search paths. Modules that fail to load are recorded
/// in the result but do not abort the batch.
pub fn load_mathlib_foundations(
    env: &mut Environment,
    lean_lib_path: &Path,
    mathlib_search_paths: &[PathBuf],
) -> MathlibLoadResult {
    let modules = mathlib_foundation_modules();
    load_mathlib_modules(env, &modules, lean_lib_path, mathlib_search_paths)
}

// ---------------------------------------------------------------------------
// Theorem verification helpers
// ---------------------------------------------------------------------------

/// Check if a specific theorem exists in the environment.
pub fn has_theorem(env: &Environment, name: &str) -> bool {
    let n = Name::from_string(name);
    env.get_const(&n).is_some()
}

/// Check if a theorem has a proof term (value) — distinguishing true theorems
/// from axioms.
pub fn has_proof(env: &Environment, name: &str) -> bool {
    let n = Name::from_string(name);
    env.get_const(&n)
        .map(|ci| ci.value.is_some())
        .unwrap_or(false)
}

/// Collect all constant names matching a prefix.
pub fn constants_with_prefix(env: &Environment, prefix: &str) -> Vec<String> {
    env.constants()
        .map(|ci| ci.name.to_string())
        .filter(|name| name.starts_with(prefix))
        .collect()
}

// ---------------------------------------------------------------------------
// Environment → .mathverse shard conversion
// ---------------------------------------------------------------------------

/// Convert a loaded Mathlib environment to an `.mathverse` shard.
///
/// Wraps `import_environment` with Mathlib-specific config (source metadata,
/// content domain).
pub fn mathlib_env_to_mathverse(
    env: &Environment,
    source_description: &str,
) -> MathverseResult<(Vec<u8>, EnvImportStats)> {
    let mut writer = ShardWriter::new();
    let config = EnvImportConfig {
        include_private: false,
        source_file: Some(source_description.to_string()),
        source_version: Some("Mathlib4".to_string()),
        content_domain: ContentDomain::PureMath,
    };

    let (stats, _records) = import_environment(env, &mut writer, &config)?;

    let mut buf = Vec::new();
    writer.write(&mut buf)?;

    Ok((buf, stats))
}

// ---------------------------------------------------------------------------
// Gamma-crown targeted Mathlib loading
// ---------------------------------------------------------------------------

/// Load gamma-crown-relevant Mathlib modules into an environment.
///
/// This is a targeted loader that loads Init modules plus the specific Mathlib
/// modules needed for gamma-crown axiom replacement. It provides a single
/// entry point for gamma-crown proof infrastructure to get an environment
/// with the maximum available theorem coverage.
///
/// Returns `None` if the Lean 4 toolchain is not available.
pub fn load_gamma_crown_environment() -> Option<GammaCrownLoadResult> {
    let lean_lib = find_lean_lib_path()?;
    let mathlib_paths = find_mathlib_search_paths();

    let mut env = Environment::default();

    // Phase 1: Load Init (always available)
    let init_result = load_init_modules(&mut env, &lean_lib);
    if init_result.loaded_modules.is_empty() {
        return None;
    }

    let init_constants = env.num_constants();
    let mut mathlib_loaded = Vec::new();
    let mut mathlib_failed = Vec::new();

    // Phase 2: Load gamma-crown Mathlib modules (if available)
    if !mathlib_paths.is_empty() {
        let gamma_modules = super::axiom_replacement::gamma_crown_mathlib_modules();
        for module in &gamma_modules {
            match load_module_with_deps(&mut env, module, &{
                let mut paths = vec![lean_lib.clone()];
                paths.extend_from_slice(&mathlib_paths);
                paths
            }) {
                Ok(_summaries) => {
                    mathlib_loaded.push(module.clone());
                }
                Err(e) => {
                    mathlib_failed.push((module.clone(), format!("{e}")));
                }
            }
        }
    }

    let total_constants = env.num_constants();

    Some(GammaCrownLoadResult {
        env,
        init_modules: init_result.loaded_modules,
        init_constants,
        mathlib_modules: mathlib_loaded,
        mathlib_failed,
        total_constants,
        has_mathlib: !mathlib_paths.is_empty(),
    })
}

/// Result of loading gamma-crown-relevant modules into an environment.
#[derive(Clone, Debug)]
pub struct GammaCrownLoadResult {
    /// The loaded environment with Init + available Mathlib modules.
    pub env: Environment,
    /// Init modules that were loaded.
    pub init_modules: Vec<String>,
    /// Number of constants from Init alone.
    pub init_constants: usize,
    /// Mathlib modules that were successfully loaded.
    pub mathlib_modules: Vec<String>,
    /// Mathlib modules that failed to load (name, error).
    pub mathlib_failed: Vec<(String, String)>,
    /// Total constants in the environment after all loading.
    pub total_constants: usize,
    /// Whether Mathlib `.olean` files were found on the system.
    pub has_mathlib: bool,
}

impl GammaCrownLoadResult {
    /// Number of constants contributed by Mathlib (beyond Init).
    pub fn mathlib_constants(&self) -> usize {
        self.total_constants.saturating_sub(self.init_constants)
    }

    /// Whether any Mathlib modules were loaded.
    pub fn has_mathlib_modules(&self) -> bool {
        !self.mathlib_modules.is_empty()
    }

    /// Summary string for diagnostics.
    pub fn summary(&self) -> String {
        format!(
            "Init: {} modules ({} constants), Mathlib: {} modules ({} constants), Total: {}",
            self.init_modules.len(),
            self.init_constants,
            self.mathlib_modules.len(),
            self.mathlib_constants(),
            self.total_constants,
        )
    }
}

/// Check the constant kind for a theorem in the environment.
///
/// Returns `Some(kind_str)` if the constant exists, describing whether it
/// is a `Theorem` (with proof), `Axiom`, `Definition`, `Opaque`, etc.
pub fn describe_constant(env: &Environment, name: &str) -> Option<String> {
    let n = Name::from_string(name);
    env.get_const(&n).map(|ci| {
        let has_value = ci.value.is_some();
        format!(
            "{:?}{}",
            ci.kind,
            if has_value { " [has proof]" } else { "" }
        )
    })
}

#[cfg(test)]
#[path = "mathlib_import_tests.rs"]
mod tests;
