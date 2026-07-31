// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for external package path resolution (#2525).
//!
//! Validates lake package discovery, `LEAN_PACKAGES_PATH` environment variable,
//! `SearchPathBuilder` API, and module name extraction from lake build output paths.

use super::{discover_lake_package_paths, module_name_from_path, SearchPathBuilder};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use tempfile::TempDir;

// ════════════════════════════════════════════════════════════════════════════
// discover_lake_package_paths tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_discover_lake_package_paths_finds_own_build() {
    let temp = TempDir::new().expect("tempdir");
    let build_lib = temp.path().join("build/lib");
    fs::create_dir_all(&build_lib).unwrap();

    let paths = discover_lake_package_paths(temp.path(), |p| fs::read_dir(p));
    assert_eq!(
        paths,
        vec![build_lib],
        "should find project's own build/lib"
    );
}

#[test]
fn test_discover_lake_package_paths_finds_dependencies() {
    let temp = TempDir::new().expect("tempdir");

    // Create fake lake package structure
    let torch_lean_lib = temp.path().join(".lake/packages/TorchLean/build/lib");
    let mathlib_lib = temp.path().join(".lake/packages/Mathlib/build/lib");
    let no_build = temp.path().join(".lake/packages/NoBuild");
    fs::create_dir_all(&torch_lean_lib).unwrap();
    fs::create_dir_all(&mathlib_lib).unwrap();
    fs::create_dir_all(&no_build).unwrap();

    let paths = discover_lake_package_paths(temp.path(), |p| fs::read_dir(p));

    assert!(
        paths.contains(&torch_lean_lib),
        "should find TorchLean: {paths:?}"
    );
    assert!(
        paths.contains(&mathlib_lib),
        "should find Mathlib: {paths:?}"
    );
    // NoBuild has no build/lib subdir, so should not appear
    assert!(
        !paths
            .iter()
            .any(|p: &PathBuf| p.to_string_lossy().contains("NoBuild")),
        "NoBuild should not appear: {paths:?}"
    );
}

#[test]
fn test_discover_lake_package_paths_finds_modern_lake_v4_layout() {
    // Lake v4 (toolchain v4.30.0-rc2, `lake exe cache get`) writes the project's
    // own oleans to `<root>/.lake/build/lib/lean/` and each dependency's to
    // `<root>/.lake/packages/<pkg>/.lake/build/lib/lean/` — NOT the legacy
    // `build/lib`. A real Mathlib tree keeps Batteries/Std oleans only here, so
    // discovery must recognize this layout or those deps are invisible and the
    // front-end re-elaborates their source.
    let temp = TempDir::new().expect("tempdir");
    let own_modern = temp.path().join(".lake/build/lib/lean");
    let batteries_modern = temp
        .path()
        .join(".lake/packages/batteries/.lake/build/lib/lean");
    let std_modern = temp.path().join(".lake/packages/std/.lake/build/lib/lean");
    fs::create_dir_all(&own_modern).unwrap();
    fs::create_dir_all(&batteries_modern).unwrap();
    fs::create_dir_all(&std_modern).unwrap();

    let paths = discover_lake_package_paths(temp.path(), |p| fs::read_dir(p));

    assert!(
        paths.contains(&own_modern),
        "should find own modern .lake/build/lib/lean: {paths:?}"
    );
    assert!(
        paths.contains(&batteries_modern),
        "should find dependency batteries modern layout: {paths:?}"
    );
    assert!(
        paths.contains(&std_modern),
        "should find dependency std modern layout: {paths:?}"
    );
}

#[test]
fn test_discover_lake_package_paths_empty_for_nonexistent() {
    let nonexistent = PathBuf::from("/tmp/definitely_does_not_exist_clean_test");
    let paths = discover_lake_package_paths(&nonexistent, |p| fs::read_dir(p));
    assert!(
        paths.is_empty(),
        "nonexistent path should yield empty: {paths:?}"
    );
}

#[test]
fn test_discover_lake_package_paths_finds_both_own_and_deps() {
    let temp = TempDir::new().expect("tempdir");

    let own_build = temp.path().join("build/lib");
    let dep_build = temp.path().join(".lake/packages/Dep/build/lib");
    fs::create_dir_all(&own_build).unwrap();
    fs::create_dir_all(&dep_build).unwrap();

    let paths = discover_lake_package_paths(temp.path(), |p| fs::read_dir(p));

    assert_eq!(
        paths.len(),
        2,
        "should find both own build and dep: {paths:?}"
    );
    assert_eq!(paths[0], own_build, "own build should come first");
    assert_eq!(paths[1], dep_build, "dep build should come second");
}

// ════════════════════════════════════════════════════════════════════════════
// LEAN_PACKAGES_PATH environment variable tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_lean_packages_path_env_var_discovers_package_libs() {
    let temp = TempDir::new().expect("tempdir");

    // Simulate a lake project root with a dependency
    let torch_lean_root = temp.path().join("torch_lean_project");
    let torch_lean_lib = torch_lean_root.join("build/lib");
    fs::create_dir_all(&torch_lean_lib).unwrap();

    let packages_path = env::join_paths([&torch_lean_root]).unwrap();

    let mut env_map = HashMap::new();
    env_map.insert("LEAN_PACKAGES_PATH", packages_path);
    env_map.insert("HOME", temp.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    assert!(
        paths.contains(&torch_lean_lib),
        "LEAN_PACKAGES_PATH should discover build/lib: {paths:?}"
    );
}

#[test]
fn test_lean_packages_path_discovers_nested_lake_deps() {
    let temp = TempDir::new().expect("tempdir");

    let project_root = temp.path().join("my_project");
    let dep_lib = project_root.join(".lake/packages/TorchLean/build/lib");
    fs::create_dir_all(&dep_lib).unwrap();

    let packages_path = env::join_paths([&project_root]).unwrap();

    let mut env_map = HashMap::new();
    env_map.insert("LEAN_PACKAGES_PATH", packages_path);
    env_map.insert("HOME", temp.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    assert!(
        paths.contains(&dep_lib),
        "should discover .lake/packages/TorchLean/build/lib: {paths:?}"
    );
}

#[test]
fn test_lean_packages_path_ordering_after_lean_path() {
    let temp = TempDir::new().expect("tempdir");

    let lean_dir = temp.path().join("lean_lib");
    let pkg_root = temp.path().join("pkg_root");
    let pkg_lib = pkg_root.join("build/lib");
    fs::create_dir_all(&lean_dir).unwrap();
    fs::create_dir_all(&pkg_lib).unwrap();

    let lean_path = env::join_paths([&lean_dir]).unwrap();
    let packages_path = env::join_paths([&pkg_root]).unwrap();

    let mut env_map = HashMap::new();
    env_map.insert("LEAN_PATH", lean_path);
    env_map.insert("LEAN_PACKAGES_PATH", packages_path);
    env_map.insert("HOME", temp.path().as_os_str().to_os_string());

    let paths = super::collect_default_search_paths(
        |key| env_map.get(key).cloned(),
        |path| fs::read_dir(path),
    );

    let lean_idx = paths.iter().position(|p| p == &lean_dir);
    let pkg_idx = paths.iter().position(|p| p == &pkg_lib);

    assert!(
        lean_idx.is_some() && pkg_idx.is_some(),
        "both paths should be present: {paths:?}"
    );
    assert!(
        lean_idx.unwrap() < pkg_idx.unwrap(),
        "LEAN_PATH should come before LEAN_PACKAGES_PATH: {paths:?}"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// SearchPathBuilder tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_search_path_builder_new_is_empty() {
    let builder = SearchPathBuilder::new();
    let paths = builder.build();
    assert!(paths.is_empty(), "new builder should produce empty paths");
}

#[test]
fn test_search_path_builder_add_lib_path() {
    let temp = TempDir::new().expect("tempdir");
    let lib_dir = temp.path().join("lib");
    fs::create_dir_all(&lib_dir).unwrap();

    let paths = SearchPathBuilder::new().add_lib_path(&lib_dir).build();

    assert_eq!(paths, vec![lib_dir]);
}

#[test]
fn test_search_path_builder_add_lib_path_skips_nonexistent() {
    let paths = SearchPathBuilder::new()
        .add_lib_path("/nonexistent/path/clean_test_12345")
        .build();

    assert!(paths.is_empty(), "nonexistent path should be skipped");
}

#[test]
fn test_search_path_builder_deduplicates() {
    let temp = TempDir::new().expect("tempdir");
    let lib_dir = temp.path().join("lib");
    fs::create_dir_all(&lib_dir).unwrap();

    let paths = SearchPathBuilder::new()
        .add_lib_path(&lib_dir)
        .add_lib_path(&lib_dir)
        .build();

    assert_eq!(paths.len(), 1, "should deduplicate: {paths:?}");
}

#[test]
fn test_search_path_builder_add_package_root() {
    let temp = TempDir::new().expect("tempdir");

    let pkg_root = temp.path().join("TorchLean");
    let own_lib = pkg_root.join("build/lib");
    let dep_lib = pkg_root.join(".lake/packages/Mathlib/build/lib");
    fs::create_dir_all(&own_lib).unwrap();
    fs::create_dir_all(&dep_lib).unwrap();

    let paths = SearchPathBuilder::new().add_package_root(&pkg_root).build();

    assert!(
        paths.contains(&own_lib),
        "should find own build/lib: {paths:?}"
    );
    assert!(
        paths.contains(&dep_lib),
        "should find dep build/lib: {paths:?}"
    );
}

#[test]
fn test_search_path_builder_combined() {
    let temp = TempDir::new().expect("tempdir");

    let explicit_lib = temp.path().join("explicit");
    let pkg_root = temp.path().join("pkg");
    let pkg_lib = pkg_root.join("build/lib");
    fs::create_dir_all(&explicit_lib).unwrap();
    fs::create_dir_all(&pkg_lib).unwrap();

    let paths = SearchPathBuilder::new()
        .add_lib_path(&explicit_lib)
        .add_package_root(&pkg_root)
        .build();

    assert_eq!(paths.len(), 2, "should have 2 paths: {paths:?}");
    assert_eq!(paths[0], explicit_lib, "explicit lib should be first");
    assert_eq!(paths[1], pkg_lib, "package lib should be second");
}

// ════════════════════════════════════════════════════════════════════════════
// Module name extraction and resolution tests
// ════════════════════════════════════════════════════════════════════════════

#[test]
fn test_module_name_from_path_with_build_lib() {
    // TorchLean-style path: .lake/packages/TorchLean/build/lib/TorchLean/IBP/Soundness.olean
    let path = Path::new("/tmp/.lake/packages/TorchLean/build/lib/TorchLean/IBP/Soundness.olean");
    let name = module_name_from_path(path);
    assert_eq!(
        name.as_deref(),
        Some("TorchLean.IBP.Soundness"),
        "should extract module name from lake build output path"
    );
}

#[test]
fn test_module_name_from_path_with_lean_lib() {
    // Standard toolchain path
    let path = Path::new("./.elan/toolchains/lean4-v4.3.0/lib/lean/Init/Prelude.olean");
    let name = module_name_from_path(path);
    assert_eq!(name.as_deref(), Some("Init.Prelude"));
}

#[test]
fn test_resolve_module_in_package_search_path() {
    let temp = TempDir::new().expect("tempdir");

    // Create a fake TorchLean module
    let lib_dir = temp.path().join("build/lib");
    let module_dir = lib_dir.join("TorchLean/IBP");
    fs::create_dir_all(&module_dir).unwrap();
    let olean_path = module_dir.join("Soundness.olean");
    fs::write(&olean_path, b"fake olean").unwrap();

    // Build search paths using the builder
    let search_paths = SearchPathBuilder::new().add_lib_path(&lib_dir).build();

    // Resolve the module
    let resolved = super::path::resolve_module_path("TorchLean.IBP.Soundness", &search_paths);

    assert!(
        resolved.is_ok(),
        "should resolve TorchLean module: {resolved:?}"
    );
    assert_eq!(resolved.unwrap(), olean_path);
}

#[test]
fn test_resolve_module_not_found_reports_searched_paths() {
    let temp = TempDir::new().expect("tempdir");
    let lib_dir = temp.path().join("lib");
    fs::create_dir_all(&lib_dir).unwrap();

    let search_paths = vec![lib_dir];
    let result = super::path::resolve_module_path("TorchLean.NonExistent", &search_paths);

    match result {
        Err(super::ImportError::ModuleNotFound { module, searched }) => {
            assert_eq!(module, "TorchLean.NonExistent");
            assert!(!searched.is_empty(), "should report searched paths");
        }
        other => panic!("expected ModuleNotFound, got {other:?}"),
    }
}

#[test]
fn test_module_not_found_message_names_paths_and_env_vars() {
    let temp = TempDir::new().expect("tempdir");
    let lib_dir = temp.path().join("lib");
    fs::create_dir_all(&lib_dir).unwrap();

    let msg = super::path::resolve_module_path("TorchLean.NonExistent", &[lib_dir])
        .expect_err("module must not resolve")
        .to_string();
    // Four-question standard: WHAT (module), WHY (absent from the searched
    // paths, which are listed), WHAT NOW (the env vars that extend search).
    assert!(msg.contains("TorchLean.NonExistent"), "got: {msg}");
    assert!(msg.contains("1 searched path(s)"), "got: {msg}");
    assert!(msg.contains("LEAN_PATH"), "remediation missing: {msg}");
}

#[test]
fn test_module_not_found_empty_search_names_discovery_remediation() {
    let msg = super::path::resolve_module_path("Init.Prelude", &[])
        .expect_err("no search paths must fail")
        .to_string();
    assert!(
        msg.contains("no .olean search paths were discovered"),
        "empty search must be diagnosed as a discovery problem, got: {msg}"
    );
    assert!(
        msg.contains("MATHLIB_PATH") && msg.contains("elan"),
        "remediation missing: {msg}"
    );
}

#[test]
fn test_malformed_module_name_is_unsupported_not_missing() {
    let err = super::path::resolve_module_path("..", &[]).expect_err("malformed name");
    match err {
        super::ImportError::UnsupportedModule { module, reason } => {
            assert_eq!(module, "..");
            assert!(reason.contains("cannot be mapped"), "got: {reason}");
        }
        other => panic!("expected UnsupportedModule, got {other:?}"),
    }
}

#[test]
fn test_load_olean_file_missing_names_path() {
    let mut env = clean_kernel::Environment::new();
    let missing = Path::new("/nonexistent/dir/Foo.olean");
    let msg = super::load_olean_file(&mut env, missing)
        .expect_err("missing .olean must fail")
        .to_string();
    assert!(
        msg.contains("/nonexistent/dir/Foo.olean"),
        ".olean read failure must name the file, got: {msg}"
    );
    assert!(
        msg.contains("lake build") || msg.contains("LEAN_PATH"),
        ".olean read failure must carry a remediation, got: {msg}"
    );
}
