// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Mathlib → Mathverse build pipeline.

use std::path::{Path, PathBuf};

use super::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn lean4_lib_available() -> bool {
    auto_detect_toolchain().is_some()
}

fn mathlib_olean_available() -> bool {
    Path::new(DEFAULT_MATHLIB_OLEAN_ROOT).exists()
}

// ---------------------------------------------------------------------------
// Root discovery
// ---------------------------------------------------------------------------

#[test]
fn test_build_mathlib_discovers_all_roots() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let root = tmp.path();

    // Fake mathlib olean root.
    let mathlib_root = root.join("mathlib4/.lake/build/lib");
    std::fs::create_dir_all(mathlib_root.join("Mathlib/Algebra")).unwrap();
    std::fs::write(
        mathlib_root.join("Mathlib/Algebra/Group.olean"),
        b"fake-olean",
    )
    .unwrap();

    // Fake batteries package.
    let pkgs = root.join("mathlib4/.lake/packages");
    let bat_lib = pkgs.join("batteries/lib/lean");
    std::fs::create_dir_all(&bat_lib).unwrap();
    std::fs::write(bat_lib.join("Batteries.olean"), b"fake").unwrap();

    // Fake Qq package (build/lib layout).
    let qq_lib = pkgs.join("Qq/build/lib");
    std::fs::create_dir_all(&qq_lib).unwrap();
    std::fs::write(qq_lib.join("Qq.olean"), b"fake").unwrap();

    let config = MathlibBuildConfig {
        mathlib_olean_root: mathlib_root,
        packages_root: pkgs,
        toolchain_lib: None,
        output_dir: root.join("output"),
        ..Default::default()
    };

    let roots = discover_olean_roots(&config);
    let labels: Vec<&str> = roots.iter().map(|(l, _)| l.as_str()).collect();

    assert!(
        labels.contains(&"mathlib"),
        "should discover mathlib, got: {labels:?}"
    );
    assert!(
        labels.iter().any(|l| l.starts_with("pkg:batteries")),
        "should discover batteries, got: {labels:?}"
    );
    assert!(
        labels.iter().any(|l| l.starts_with("pkg:Qq")),
        "should discover Qq, got: {labels:?}"
    );
}

// ---------------------------------------------------------------------------
// Config defaults
// ---------------------------------------------------------------------------

#[test]
fn test_build_mathlib_config_defaults() {
    let config = MathlibBuildConfig::default();

    assert_eq!(config.shard_size_limit, 10_000);
    assert_eq!(config.max_file_size, 2_500_000);
    assert_eq!(config.file_limit, 0);
    assert!(!config.verbose);
    assert!(config.toolchain_lib.is_none());
    assert_eq!(config.output_dir, PathBuf::from(DEFAULT_OUTPUT_DIR));
}

// ---------------------------------------------------------------------------
// Small sample build (toolchain only, limited to 10 files)
// ---------------------------------------------------------------------------

#[test]
fn test_build_mathlib_small_sample() {
    if !lean4_lib_available() {
        eprintln!("SKIP: no Lean 4 toolchain detected");
        return;
    }

    let tmp = tempfile::tempdir().expect("tempdir");
    let config = MathlibBuildConfig {
        mathlib_olean_root: PathBuf::from("/nonexistent"),
        packages_root: PathBuf::from("/nonexistent"),
        toolchain_lib: auto_detect_toolchain(),
        output_dir: tmp.path().join("mathverse"),
        shard_size_limit: 5000,
        max_file_size: 2_500_000,
        file_limit: 0,
        verbose: true,
    };

    let result = build_mathlib_library(&config).expect("build should succeed");

    assert!(
        !result.root_results.is_empty(),
        "should have at least one root result"
    );
    assert_eq!(result.root_results[0].label, "toolchain");
    assert!(
        result.total_constants > 0,
        "should produce constants from toolchain"
    );
}

// ---------------------------------------------------------------------------
// No roots → error
// ---------------------------------------------------------------------------

#[test]
fn test_build_mathlib_no_roots_returns_error() {
    let config = MathlibBuildConfig {
        mathlib_olean_root: PathBuf::from("/nonexistent/mathlib"),
        packages_root: PathBuf::from("/nonexistent/packages"),
        toolchain_lib: Some(PathBuf::from("/nonexistent/toolchain")),
        output_dir: PathBuf::from("/tmp/test-mathverse"),
        ..Default::default()
    };

    let result = build_mathlib_library(&config);
    assert!(result.is_err(), "should fail when no roots exist");
    let err = result.unwrap_err().to_string();
    assert!(err.contains("no .olean roots found"), "got: {err}");
    // Four-question standard: the error must name WHICH paths were checked
    // and HOW to populate them, not just that discovery came up empty.
    assert!(
        err.contains("/nonexistent/mathlib")
            && err.contains("/nonexistent/packages")
            && err.contains("/nonexistent/toolchain"),
        "no-roots error must name every checked path, got: {err}"
    );
    assert!(
        err.contains("setup_mathlib_oleans.sh"),
        "no-roots error must name the setup remediation, got: {err}"
    );
}

// ---------------------------------------------------------------------------
// Full Mathlib build (skipped if not installed)
// ---------------------------------------------------------------------------

#[test]
fn test_build_mathlib_full() {
    if !mathlib_olean_available() {
        eprintln!(
            "SKIP: Mathlib .olean not found at {}",
            DEFAULT_MATHLIB_OLEAN_ROOT
        );
        return;
    }

    let tmp = tempfile::tempdir().expect("tempdir");
    let config = MathlibBuildConfig {
        output_dir: tmp.path().join("mathverse"),
        verbose: true,
        ..Default::default()
    };

    let result = build_mathlib_library(&config).expect("build should succeed");

    assert!(
        result.total_files_parsed > 1000,
        "expected >1000 parsed, got {}",
        result.total_files_parsed
    );
    assert!(
        result.total_constants > 50_000,
        "expected >50K constants, got {}",
        result.total_constants
    );
    assert!(result.total_shards > 0, "should write at least one shard");
}
