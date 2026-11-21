// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared production-source scanning helpers for ratchet and hygiene tests.
//!
//! Consolidates the recursive Rust-file walker and test-file/directory
//! filtering that were previously duplicated across `bypass_ratchet.rs`,
//! `ay_contract_ratchet_tests.rs`, and `tests_source_hygiene.rs`.
//!
//! The comment/literal blanker and the inline `#[cfg(test)] mod` detection
//! (`blank_noncode`, `production_code_lines`, `cfg_test_mod_line_ranges`,
//! `line_is_inside_cfg_test_mod`) are re-exported from
//! `crates/clean-evidence/src/source_scan.rs`, the one implementation in the
//! tree since design unit EV0 (2026-11-17); their arms live there. The copy
//! that used to sit here was the original the promoted one was made from.
//!
//! Part of #2764.

pub(crate) use clean_evidence::source_scan::{
    blank_noncode, cfg_test_mod_line_ranges, line_is_inside_cfg_test_mod, production_code_lines,
};
use std::path::{Path, PathBuf};

/// Caller-controlled rules for collecting Rust source files.
///
/// All exclusion lists use simple string matching. Directory names can be
/// matched exactly or by suffix; file names use exact/prefix/suffix matching.
pub(crate) struct SourceScanRules<'a> {
    /// Directory names to skip entirely (e.g., `"tests"`).
    pub excluded_dir_names: &'a [&'a str],
    /// Directory name suffixes to skip (e.g., `"_tests"` matches `ay_proof_tests/`).
    pub excluded_dir_suffixes: &'a [&'a str],
    /// Exact file names to skip (e.g., `"tests.rs"`).
    pub excluded_file_names: &'a [&'a str],
    /// File name prefixes to skip (e.g., `"tests_"`).
    pub excluded_file_prefixes: &'a [&'a str],
    /// File name suffixes to skip (e.g., `"_tests.rs"`).
    pub excluded_file_suffixes: &'a [&'a str],
}

/// Default rules matching the original `bypass_ratchet.rs` production-file policy:
/// skip `tests/` and `*_tests/` dirs, `tests.rs` files, and `*_tests.rs` files.
pub(crate) const DEFAULT_PRODUCTION_RULES: SourceScanRules<'static> = SourceScanRules {
    excluded_dir_names: &["tests"],
    excluded_dir_suffixes: &["_tests"],
    excluded_file_names: &["tests.rs"],
    excluded_file_prefixes: &[],
    excluded_file_suffixes: &["_tests.rs"],
};

/// Recursively collect `.rs` files under `root`, respecting `rules`.
///
/// Results are sorted by path for deterministic output.
pub(crate) fn collect_rust_source_files(root: &Path, rules: &SourceScanRules<'_>) -> Vec<PathBuf> {
    let mut files = Vec::new();
    collect_recursive(root, rules, &mut files);
    files.sort();
    files
}

fn collect_recursive(dir: &Path, rules: &SourceScanRules<'_>, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    let mut sorted: Vec<_> = entries.filter_map(|e| e.ok()).collect();
    sorted.sort_by_key(|e| e.path());

    for entry in sorted {
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if rules.excluded_dir_names.contains(&name) {
                continue;
            }
            if rules
                .excluded_dir_suffixes
                .iter()
                .any(|suffix| name.ends_with(suffix))
            {
                continue;
            }
            collect_recursive(&path, rules, out);
        } else if is_included_source_file(&path, rules) {
            out.push(path);
        }
    }
}

fn is_included_source_file(path: &Path, rules: &SourceScanRules<'_>) -> bool {
    let ext_is_rs = path.extension().and_then(|e| e.to_str()) == Some("rs");
    if !ext_is_rs {
        return false;
    }
    let Some(file_name) = path.file_name().and_then(|n| n.to_str()) else {
        return false;
    };
    if rules.excluded_file_names.contains(&file_name) {
        return false;
    }
    if rules
        .excluded_file_prefixes
        .iter()
        .any(|prefix| file_name.starts_with(prefix))
    {
        return false;
    }
    if rules
        .excluded_file_suffixes
        .iter()
        .any(|suffix| file_name.ends_with(suffix))
    {
        return false;
    }
    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn collect_rust_source_files_skips_test_dirs_and_test_files() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let root = temp.path();
    let smt_dir = root.join("smt");
    let tests_dir = root.join("tests");
    let proof_tests_dir = smt_dir.join("ay_proof_tests");
    std::fs::create_dir_all(&smt_dir).expect("create smt dir");
    std::fs::create_dir_all(&tests_dir).expect("create tests dir");
    std::fs::create_dir_all(&proof_tests_dir).expect("create proof tests dir");

    std::fs::write(root.join("prod.rs"), "fn prod() {}\n").expect("write prod.rs");
    std::fs::write(root.join("tests.rs"), "#[test] fn unit() {}\n").expect("write tests.rs");
    std::fs::write(
        smt_dir.join("selected_proof_accounting_tests.rs"),
        "#[test] fn ratchet() {}\n",
    )
    .expect("write smt tests file");
    std::fs::write(tests_dir.join("helper.rs"), "#[test] fn helper() {}\n")
        .expect("write tests/helper.rs");
    std::fs::write(
        proof_tests_dir.join("support.rs"),
        "fn legacy_fixture() {}\n",
    )
    .expect("write smt/ay_proof_tests/support.rs");

    let files = collect_rust_source_files(root, &DEFAULT_PRODUCTION_RULES);

    assert!(
        files.iter().any(|p| p.ends_with("prod.rs")),
        "collector should retain production source files"
    );
    assert!(
        !files.iter().any(|p| p.ends_with("tests.rs")),
        "collector should skip tests.rs"
    );
    assert!(
        !files
            .iter()
            .any(|p| p.ends_with("selected_proof_accounting_tests.rs")),
        "collector should skip *_tests.rs"
    );
    assert!(
        !files.iter().any(|p| p.ends_with("helper.rs")),
        "collector should skip files under tests/"
    );
    assert!(
        !files.iter().any(|p| p.ends_with("support.rs")),
        "collector should skip files under *_tests/ directories"
    );
}

#[test]
fn collect_rust_source_files_respects_custom_rules() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let root = temp.path();
    std::fs::write(root.join("mod.rs"), "mod foo;\n").expect("write mod.rs");
    std::fs::write(root.join("foo.rs"), "fn foo() {}\n").expect("write foo.rs");
    std::fs::write(
        root.join("ay_contract_ratchet_tests.rs"),
        "#[test] fn check() {}\n",
    )
    .expect("write ratchet tests");
    std::fs::write(
        root.join("tests_source_hygiene.rs"),
        "#[test] fn hyg() {}\n",
    )
    .expect("write tests_ prefixed file");

    let rules = SourceScanRules {
        excluded_dir_names: &["tests"],
        excluded_dir_suffixes: &["_tests"],
        excluded_file_names: &["ay_contract_ratchet_tests.rs", "tests.rs"],
        excluded_file_prefixes: &["tests_"],
        excluded_file_suffixes: &["_tests.rs"],
    };
    let files = collect_rust_source_files(root, &rules);

    assert!(files.iter().any(|p| p.ends_with("mod.rs")));
    assert!(files.iter().any(|p| p.ends_with("foo.rs")));
    assert!(!files
        .iter()
        .any(|p| p.ends_with("ay_contract_ratchet_tests.rs")));
    assert!(!files.iter().any(|p| p.ends_with("tests_source_hygiene.rs")));
}

#[test]
fn collect_rust_source_files_skips_dirs_by_suffix() {
    let temp = tempfile::tempdir().expect("create temp dir");
    let root = temp.path();
    let proof_tests_dir = root.join("ay_proof_tests");
    std::fs::create_dir_all(&proof_tests_dir).expect("create ay_proof_tests dir");
    std::fs::write(root.join("prod.rs"), "fn prod() {}\n").expect("write prod.rs");
    std::fs::write(
        proof_tests_dir.join("mod.rs"),
        "use legacy::ay_backend::AyLogic;\n",
    )
    .expect("write ay_proof_tests/mod.rs");

    let rules = SourceScanRules {
        excluded_dir_names: &["tests"],
        excluded_dir_suffixes: &["_tests"],
        excluded_file_names: &[],
        excluded_file_prefixes: &[],
        excluded_file_suffixes: &[],
    };
    let files = collect_rust_source_files(root, &rules);

    assert!(
        files.iter().any(|p| p.ends_with("prod.rs")),
        "production files should be collected"
    );
    assert!(
        !files.iter().any(|p| p.ends_with("mod.rs")),
        "files inside *_tests/ directories should be excluded by suffix rule"
    );
}
