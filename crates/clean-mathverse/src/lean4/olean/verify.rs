// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 `.olean` directory verification via kernel TypeChecker.
//!
//! Bridges `clean-olean`'s `verify_batch` pipeline into the Mathverse conversion
//! workflow. Discovers `.olean` files, builds a dependency graph, loads modules
//! into a cumulative environment, and type-checks every constant to produce
//! `KernelVerified` trust levels.
//!
//! Used by `mathverse_convert lean4-dir` and `mathverse_convert all`.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::env::Environment;
use clean_olean::default_search_paths;
use clean_olean::verify_batch::{
    build_dependency_order, build_summary, collect_new_env_names, discover_olean_files,
    preload_init_if_needed, relative_display, verify_one_module, BatchSummary,
};

// ---------------------------------------------------------------------------
// Single-directory verification
// ---------------------------------------------------------------------------

/// Verify and convert a single Lean 4 `.olean` directory with TypeChecker
/// verification. Returns the batch summary on success.
pub fn verify_lean4_dir(root: &Path) -> Option<BatchSummary> {
    if !root.is_dir() {
        return None;
    }

    let olean_files = discover_olean_files(root);
    if olean_files.is_empty() {
        return None;
    }

    let (ordered_modules, _parse_failures) = build_dependency_order(&olean_files, root);

    let mut search_paths = default_search_paths();
    search_paths.push(root.to_path_buf());

    let mut env = Environment::default();
    preload_init_if_needed(&mut env, root, &search_paths);

    let start = Instant::now();
    let mut results = Vec::with_capacity(ordered_modules.len());
    let mut known_names: HashSet<String> = HashSet::new();
    collect_new_env_names(&env, &mut known_names);

    for desc in &ordered_modules {
        let rel_path = relative_display(&desc.path, root);
        let result = verify_one_module(
            &mut env,
            &desc.module_name,
            &rel_path,
            &search_paths,
            &mut known_names,
            false,
        );
        results.push(result);
    }

    let elapsed = start.elapsed();
    Some(build_summary(
        root,
        olean_files.len(),
        ordered_modules.len(),
        results,
        elapsed,
    ))
}

// ---------------------------------------------------------------------------
// Discovery
// ---------------------------------------------------------------------------

/// Discover Lean 4 `.olean` directories from the elan toolchain path and from
/// any `.olean` directories present in `raw_dir`.
pub fn discover_lean4_dirs(raw_dir: &Path) -> Vec<PathBuf> {
    let mut dirs = Vec::new();

    // Elan toolchain libraries: ~/.elan/toolchains/*/lib/lean/
    let home = std::env::var("HOME").unwrap_or_default();
    let elan_toolchains = PathBuf::from(&home).join(".elan/toolchains");
    if elan_toolchains.is_dir() {
        if let Ok(rd) = std::fs::read_dir(&elan_toolchains) {
            for entry in rd.filter_map(|e| e.ok()) {
                let lib_lean = entry.path().join("lib/lean");
                if lib_lean.is_dir() {
                    dirs.push(lib_lean);
                }
            }
        }
    }

    // Data-dir subdirectories (lean4, lean4-src, batteries, mathlib4)
    if raw_dir.is_dir() {
        for name in &["lean4", "lean4-src", "lean4-std", "batteries"] {
            let candidate = raw_dir.join(name);
            if candidate.is_dir() {
                dirs.push(candidate);
            }
        }
        let mathlib_lib = raw_dir.join("mathlib4/.lake/build/lib");
        if mathlib_lib.is_dir() {
            dirs.push(mathlib_lib);
        }
    }

    dirs.sort();
    dirs.dedup();
    dirs
}
