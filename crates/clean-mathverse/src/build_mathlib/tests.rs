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

// ---------------------------------------------------------------------------
// Multi-root shard namespacing (regression: earlier roots were clobbered)
// ---------------------------------------------------------------------------

#[test]
fn test_shard_prefix_for_label_sanitizes_and_is_distinct() {
    // Alphanumeric labels pass through unchanged.
    assert_eq!(shard_prefix_for_label("toolchain"), "toolchain");
    assert_eq!(shard_prefix_for_label("mathlib"), "mathlib");
    // `:` (and any non-alphanumeric) becomes `_` so it is filesystem-safe.
    assert_eq!(shard_prefix_for_label("pkg:batteries"), "pkg_batteries");
    assert_eq!(shard_prefix_for_label("pkg:Qq"), "pkg_Qq");
    // An all-punctuation label falls back rather than collapsing to empty.
    assert_eq!(shard_prefix_for_label(":::"), "root");

    // The standard root labels must map to DISTINCT prefixes — this is exactly
    // the property that prevents one root's `_0000..` shards from overwriting
    // another's on disk.
    let labels = [
        "toolchain",
        "pkg:batteries",
        "pkg:Qq",
        "pkg:aesop",
        "mathlib",
    ];
    let prefixes: std::collections::HashSet<String> =
        labels.iter().map(|l| shard_prefix_for_label(l)).collect();
    assert_eq!(
        prefixes.len(),
        labels.len(),
        "each root label must map to a distinct shard prefix, got {prefixes:?}"
    );
}

/// Regression for the multi-root clobber bug: initializing the manifest ONCE
/// and then appending each root's shards (distinct prefixes,
/// `reset_manifest: false`) must leave every root's shards registered — the
/// previous code re-`init()`ed per root and left only the last root's shards.
#[test]
fn test_multiroot_manifest_accumulates_without_clobber() {
    use crate::manifest::LibraryLoader;
    use crate::shard::ShardWriter;

    let tmp = tempfile::tempdir().expect("tempdir");
    let loader = LibraryLoader::new(tmp.path().to_path_buf());

    // Mirror `build_mathlib_library`: init the shared manifest exactly once.
    loader.init().expect("init shared library once");

    // Three roots, each appending a shard under its own prefix (the
    // `reset_manifest: false` path — no re-init between roots).
    for name in ["toolchain_0000", "pkg_batteries_0000", "mathlib_0000"] {
        let writer = ShardWriter::new();
        loader
            .write_shard(&writer, name, false)
            .unwrap_or_else(|e| panic!("write shard {name}: {e}"));
    }

    let manifest = loader.load_manifest().expect("load merged manifest");
    let paths: Vec<String> = manifest
        .all_shards()
        .iter()
        .map(|s| s.path.clone())
        .collect();

    assert_eq!(
        paths.len(),
        3,
        "all three roots' shards must survive in the manifest, got {paths:?}"
    );
    for expect in ["toolchain_0000", "pkg_batteries_0000", "mathlib_0000"] {
        assert!(
            paths.iter().any(|p| p.contains(expect)),
            "manifest must retain {expect} (not clobbered), got {paths:?}"
        );
    }
}
