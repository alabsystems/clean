// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared production-source scanning helpers for ratchet and hygiene tests.
//!
//! Consolidates the recursive Rust-file walker, test-file/directory filtering,
//! inline `#[cfg(test)] mod` block detection, and comment stripping that were
//! previously duplicated across `bypass_ratchet.rs`, `ay_contract_ratchet_tests.rs`,
//! and `tests_source_hygiene.rs`.
//!
//! Part of #2764.

use std::ops::RangeInclusive;
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
// Inline #[cfg(test)] mod block detection
// ---------------------------------------------------------------------------

/// Return the inclusive 0-indexed line ranges covered by inline `#[cfg(test)] mod` blocks.
///
/// Distinguishes inline test modules from conditional imports such as
/// `#[cfg(test)] use ...` and lets ratchet scanners resume after the test
/// block ends instead of treating the entire file tail as test-only.
pub(crate) fn cfg_test_mod_line_ranges(content: &str) -> Vec<RangeInclusive<usize>> {
    let lines: Vec<&str> = content.lines().collect();
    let mut ranges = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let Some(mod_line) = cfg_test_mod_declaration_line(&lines, i) else {
            i += 1;
            continue;
        };
        let Some(end_line) = find_block_end_line(&lines, mod_line) else {
            i += 1;
            continue;
        };
        ranges.push(i..=end_line);
        i = end_line + 1;
    }

    ranges
}

/// Check whether a given line index falls inside any `#[cfg(test)] mod` block.
pub(crate) fn line_is_inside_cfg_test_mod(
    ranges: &[RangeInclusive<usize>],
    line_idx: usize,
) -> bool {
    ranges.iter().any(|range| range.contains(&line_idx))
}

fn cfg_test_mod_declaration_line(lines: &[&str], attr_line: usize) -> Option<usize> {
    let trimmed = lines[attr_line].trim_start();
    if !trimmed.starts_with("#[cfg(test)]") {
        return None;
    }

    if let Some(rest) = trimmed.strip_prefix("#[cfg(test)]") {
        if is_mod_declaration_line(rest.trim_start()) {
            return Some(attr_line);
        }
    }

    let mut j = attr_line + 1;
    while j < lines.len() {
        let next = lines[j].trim_start();
        if next.is_empty() || next.starts_with("#[") || is_comment_preamble_line(next) {
            j += 1;
            continue;
        }
        return is_mod_declaration_line(next).then_some(j);
    }

    None
}

fn is_mod_declaration_line(trimmed: &str) -> bool {
    trimmed.starts_with("mod ")
        || trimmed.starts_with("pub mod ")
        || trimmed.starts_with("pub(crate) mod ")
        || trimmed.starts_with("pub(super) mod ")
        || trimmed.starts_with("pub(self) mod ")
        || visibility_restricted_mod_line(trimmed)
}

fn visibility_restricted_mod_line(trimmed: &str) -> bool {
    let Some(rest) = trimmed.strip_prefix("pub(in ") else {
        return false;
    };
    let Some((_, after_visibility)) = rest.split_once(')') else {
        return false;
    };
    after_visibility.trim_start().starts_with("mod ")
}

fn is_comment_preamble_line(trimmed: &str) -> bool {
    trimmed.starts_with("//")
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
        || trimmed.starts_with("*/")
}

fn find_block_end_line(lines: &[&str], start_line: usize) -> Option<usize> {
    let mut depth = 0_i32;
    let mut saw_open = false;

    for (idx, line) in lines.iter().enumerate().skip(start_line) {
        let code = line.split("//").next().unwrap_or("");
        for ch in code.chars() {
            match ch {
                '{' => {
                    depth += 1;
                    saw_open = true;
                }
                '}' if saw_open => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(idx);
                    }
                }
                _ => {}
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Line-level helpers
// ---------------------------------------------------------------------------

/// Return the portion of `line` before the first `//` line comment.
pub(crate) fn code_before_line_comment(line: &str) -> &str {
    line.split("//").next().unwrap_or("")
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[test]
fn cfg_test_mod_line_ranges_ignore_conditional_imports_and_resume_after_module() {
    let content = r#"#[cfg(test)]
use super::helper;

fn before() {
    metas.assign();
}

#[cfg(test)]
mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(ranges, vec![7..=12]);
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 1),
        "conditional imports are not inline test modules"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 4),
        "production code before the test module must still count"
    );
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 10),
        "code inside the inline test module must be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 15),
        "production code after the test module must still count"
    );
}

#[test]
fn cfg_test_mod_line_ranges_distinguish_pub_in_use_from_pub_in_mod() {
    let content = r#"#[cfg(test)]
pub(in crate::tests) use super::helper;

fn before() {
    metas.assign();
}

#[cfg(test)]
pub(in crate::tests) mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(ranges, vec![7..=12]);
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 1),
        "conditional pub(in ...) imports are not inline test modules"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 4),
        "production code before a pub(in ...) test module must still count"
    );
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 9),
        "pub(in ...) mod tests blocks must still be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 15),
        "production code after the test module must still count"
    );
}

#[test]
fn cfg_test_mod_line_ranges_ignore_comment_preamble_before_module() {
    let content = r#"#[cfg(test)]
// Helper note for the test-only module.
/// Extra docs before the item.
#[allow(dead_code)]
mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after_tests() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(ranges, vec![0..=8]);
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 6),
        "lines inside comment-preamble cfg(test) modules must be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 11),
        "production code after the test module must still count"
    );
}

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

#[test]
fn code_before_line_comment_strips_trailing_comments() {
    assert_eq!(
        code_before_line_comment("let x = 1; // comment"),
        "let x = 1; "
    );
    assert_eq!(code_before_line_comment("// full line comment"), "");
    assert_eq!(
        code_before_line_comment("no comment here"),
        "no comment here"
    );
}
