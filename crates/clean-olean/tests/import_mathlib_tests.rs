// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for loading Mathlib modules into the kernel environment.
//!
//! These tests require Mathlib4 to be installed. If Mathlib is not found,
//! the tests will skip gracefully.
//!
//! To install Mathlib for testing:
//! ```bash
//! # Clone a Mathlib-using project
//! lake new test_mathlib math
//! cd test_mathlib
//! lake build  # This downloads and builds Mathlib
//! ```

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_olean::{default_search_paths, load_module_with_deps};
use std::path::{Path, PathBuf};

/// Get all paths from MATHLIB_PATH that contain Mathlib .olean files.
///
/// Checks common locations:
/// 1. Environment variable MATHLIB_PATH (supports multiple colon-separated paths)
/// 2. ~/.elan/toolchains/.../lib/lean/ directories
/// 3. Common lake build cache locations
fn get_mathlib_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();

    // Check environment variable first - supports multiple paths
    if let Ok(mathlib_path_env) = std::env::var("MATHLIB_PATH") {
        for path in std::env::split_paths(&mathlib_path_env) {
            if path.exists() {
                paths.push(path.clone());
                // Check if this path has Mathlib specifically
                if path.join("Mathlib.olean").exists()
                    || path.join("Mathlib/Data/Nat/Basic.olean").exists()
                {
                    // Found Mathlib, this is valid
                }
            }
        }
        if !paths.is_empty() {
            return paths;
        }
    }

    // Get home directory from environment
    let home = std::env::var("HOME")
        .ok()
        .map(PathBuf::from)
        .or_else(|| std::env::var("USERPROFILE").ok().map(PathBuf::from));

    if let Some(ref home) = home {
        // Lake package cache (Mathlib installed as dependency)
        let lake_packages = home.join(".elan/toolchains");
        if lake_packages.exists() {
            // Look for any toolchain with Mathlib
            if let Ok(entries) = std::fs::read_dir(&lake_packages) {
                for entry in entries.flatten() {
                    let mathlib_path = entry.path().join("lib/lean/Mathlib");
                    if mathlib_path.exists() {
                        return vec![entry.path().join("lib/lean")];
                    }
                }
            }
        }
    }

    // Check for local Mathlib checkout with lake build output
    if let Ok(current_dir) = std::env::current_dir() {
        let lake_packages_dir = current_dir.join(".lake/packages/mathlib/.lake/build/lib");
        if lake_packages_dir.exists() {
            return vec![lake_packages_dir];
        }
    }

    // Check data/raw/mathlib4/ in repo tree (downloaded Mathlib oleans)
    if let Some(paths) = find_mathlib_in_data_raw() {
        return paths;
    }

    vec![]
}

/// Discover Mathlib oleans in data/raw/mathlib4/ by traversing repo ancestors.
fn find_mathlib_in_data_raw() -> Option<Vec<PathBuf>> {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    if let Some(ancestor) = manifest_dir.ancestors().next() {
        let mathlib_root = ancestor.join("data/raw/mathlib4");
        let root = find_mathlib_lib_root(&mathlib_root)?;
        let mut all_paths = vec![root];
        collect_package_paths(&mathlib_root, &mut all_paths);
        return Some(all_paths);
    }
    None
}

/// Find the Mathlib .olean root within a lake project directory.
fn find_mathlib_lib_root(mathlib_root: &Path) -> Option<PathBuf> {
    for subdir in &[".lake/build/lib/lean", ".lake/build/lib"] {
        let candidate = mathlib_root.join(subdir);
        if candidate.join("Mathlib.olean").exists()
            || candidate.join("Mathlib/Data/Nat/Basic.olean").exists()
        {
            return Some(candidate);
        }
    }
    None
}

/// Collect package dependency paths (Batteries, Aesop, etc.) from .lake/packages/.
fn collect_package_paths(mathlib_root: &Path, paths: &mut Vec<PathBuf>) {
    let packages_dir = mathlib_root.join(".lake/packages");
    let Ok(entries) = std::fs::read_dir(packages_dir) else {
        return;
    };
    for entry in entries.flatten() {
        let pkg = entry.path();
        for base in &[
            "build/lib",
            "build/lib/lean",
            ".lake/build/lib",
            ".lake/build/lib/lean",
        ] {
            let p = pkg.join(base);
            if p.exists() {
                paths.push(p);
            }
        }
    }
}

/// Get combined search paths including both standard library and Mathlib.
fn get_combined_search_paths() -> Option<Vec<PathBuf>> {
    let mathlib_paths = get_mathlib_paths();
    if mathlib_paths.is_empty() {
        return None;
    }
    let mut paths = mathlib_paths;
    paths.extend(default_search_paths());
    Some(paths)
}

#[test]
fn test_load_mathlib_data_nat_basic() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        eprintln!("  Set MATHLIB_PATH environment variable to Mathlib .olean directory");
        eprintln!("  Or run `lake build` in a Mathlib-using project");
        return;
    };

    let mut env = Environment::default();
    let result = load_module_with_deps(&mut env, "Mathlib.Data.Nat.Basic", &search_paths);

    match result {
        Ok(summaries) => {
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let total_skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();

            println!(
                "Mathlib.Data.Nat.Basic: {} modules, {} added, {} skipped",
                summaries.len(),
                total_added,
                total_skipped
            );

            // Verify key constants exist
            let nat_add_comm = Name::from_string("Nat.add_comm");
            if let Some(const_info) = env.get_const(&nat_add_comm) {
                println!("  Found Nat.add_comm: {:?}", const_info.type_);
            } else {
                println!("  Nat.add_comm not found (may be in different module)");
            }

            assert!(total_added > 0, "Expected constants to be added");
        }
        Err(e) => {
            panic!("Mathlib discoverable but load failed for Mathlib.Data.Nat.Basic: {e}");
        }
    }
}

#[test]
fn test_load_mathlib_algebra_group_basic() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        return;
    };

    let mut env = Environment::default();
    let result = load_module_with_deps(&mut env, "Mathlib.Algebra.Group.Basic", &search_paths);

    match result {
        Ok(summaries) => {
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let total_skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();

            println!(
                "Mathlib.Algebra.Group.Basic: {} modules, {} added, {} skipped",
                summaries.len(),
                total_added,
                total_skipped
            );

            // Check for common group theory definitions
            let test_names = [
                "mul_assoc",
                "one_mul",
                "mul_one",
                "inv_mul_cancel",
                "Group",
                "AddGroup",
            ];

            for name in test_names {
                let n = Name::from_string(name);
                if env.get_const(&n).is_some() {
                    println!("  Found: {name}");
                }
            }

            assert!(total_added > 0, "Expected constants to be added");
        }
        Err(e) => {
            panic!("Mathlib discoverable but load failed for Mathlib.Algebra.Group.Basic: {e}");
        }
    }
}

#[test]
fn test_load_mathlib_topology_basic() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        return;
    };

    let mut env = Environment::default();
    let result = load_module_with_deps(&mut env, "Mathlib.Topology.Basic", &search_paths);

    match result {
        Ok(summaries) => {
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let total_skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();

            println!(
                "Mathlib.Topology.Basic: {} modules, {} added, {} skipped",
                summaries.len(),
                total_added,
                total_skipped
            );

            // Check for topology definitions
            let test_names = ["TopologicalSpace", "IsOpen", "IsClosed", "Continuous"];

            for name in test_names {
                let n = Name::from_string(name);
                if env.get_const(&n).is_some() {
                    println!("  Found: {name}");
                }
            }

            assert!(total_added > 0, "Expected constants to be added");
        }
        Err(e) => {
            panic!("Mathlib discoverable but load failed for Mathlib.Topology.Basic: {e}");
        }
    }
}

#[test]
fn test_load_mathlib_analysis_calculus() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        return;
    };

    let mut env = Environment::default();
    // Try loading a calculus module - this tests deep dependency chains
    let result = load_module_with_deps(
        &mut env,
        "Mathlib.Analysis.Calculus.Deriv.Basic",
        &search_paths,
    );

    match result {
        Ok(summaries) => {
            let total_modules = summaries.len();
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let total_skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();

            println!(
                "Mathlib.Analysis.Calculus.Deriv.Basic: {total_modules} modules, {total_added} added, {total_skipped} skipped"
            );

            // This is a large module tree - expect many constants
            println!(
                "  Average constants per module: {:.1}",
                total_added as f64 / total_modules as f64
            );

            assert!(total_added > 0, "Expected constants to be added");
        }
        Err(e) => {
            panic!("Mathlib discoverable but load failed for Mathlib.Analysis.Calculus.Deriv.Basic: {e}");
        }
    }
}

/// Issue #177 Acceptance Criterion 1: Verify Mathlib.Data.Real.Basic loads from .olean
///
/// This test confirms the core acceptance criterion that real .olean loading works
/// for the specific module mentioned in #177.
#[test]
fn test_load_mathlib_data_real_basic() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        eprintln!("  Set MATHLIB_PATH environment variable to Mathlib .olean directory");
        return;
    };

    let mut env = Environment::default();
    let result = load_module_with_deps(&mut env, "Mathlib.Data.Real.Basic", &search_paths);

    match result {
        Ok(summaries) => {
            let total_modules = summaries.len();
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let total_skipped: usize = summaries.iter().map(|s| s.skipped_constants.len()).sum();

            println!(
                "Mathlib.Data.Real.Basic: {total_modules} modules, {total_added} added, {total_skipped} skipped"
            );

            // Check for Real number definitions
            let test_names = ["Real", "Real.add", "Real.mul", "Real.lt", "Real.ofNat"];

            for name in test_names {
                let n = Name::from_string(name);
                if env.get_const(&n).is_some() {
                    println!("  Found: {name}");
                }
            }

            // This module loads from .olean files, NOT stubs
            // The stub system would not produce this many modules
            assert!(
                total_modules > 100,
                "#177 AC1: Expected .olean loading to pull > 100 dependency modules for Real.Basic, got {total_modules}"
            );
            assert!(
                total_added > 10000,
                "#177 AC1: Expected .olean loading to produce > 10,000 constants, got {total_added}"
            );
        }
        Err(e) => {
            panic!("#177 AC1 FAIL: Mathlib.Data.Real.Basic should load from .olean: {e}");
        }
    }
}

#[test]
fn test_mathlib_loading_performance() {
    let Some(search_paths) = get_combined_search_paths() else {
        eprintln!("Skipping test: Mathlib not found");
        return;
    };

    // Measure loading time for a representative Mathlib module
    let start = std::time::Instant::now();

    let mut env = Environment::default();
    let result = load_module_with_deps(&mut env, "Mathlib.Data.Nat.Basic", &search_paths);

    let elapsed = start.elapsed();

    match result {
        Ok(summaries) => {
            let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
            let constants_per_sec = total_added as f64 / elapsed.as_secs_f64();

            println!("\n=== Mathlib Loading Performance ===");
            println!("Module: Mathlib.Data.Nat.Basic");
            println!("Time: {elapsed:?}");
            println!("Constants: {total_added}");
            println!("Constants/sec: {constants_per_sec:.0}");
            println!("Modules loaded: {}", summaries.len());

            // Performance baseline - should load at reasonable speed
            // Mathlib modules are larger so may be slower than Init
            assert!(
                constants_per_sec > 100.0,
                "Expected > 100 constants/sec, got {constants_per_sec:.0}"
            );
        }
        Err(e) => {
            panic!(
                "Mathlib discoverable but load failed for Mathlib.Data.Nat.Basic (perf test): {e}"
            );
        }
    }
}
