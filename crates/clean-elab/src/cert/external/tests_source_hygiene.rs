// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;

use crate::test_support::source_scan::{
    cfg_test_mod_line_ranges, code_before_line_comment, collect_rust_source_files,
    line_is_inside_cfg_test_mod, SourceScanRules,
};

/// External cert production-file rules: skip `tests/` and `*_tests/` dirs plus
/// any file whose name starts with `tests` (covers `tests.rs`,
/// `tests_source_hygiene.rs`, `tests_fixtures.rs`).
const EXTERNAL_CERT_RULES: SourceScanRules<'static> = SourceScanRules {
    excluded_dir_names: &["tests"],
    excluded_dir_suffixes: &["_tests"],
    excluded_file_names: &[],
    excluded_file_prefixes: &["tests"],
    excluded_file_suffixes: &[],
};

fn contains_unwrap_call(line: &str) -> bool {
    let mut rest = line;
    while let Some(pos) = rest.find(".unwrap") {
        let after = rest[pos + ".unwrap".len()..].trim_start();
        if after.starts_with('(') {
            return true;
        }
        rest = after;
    }
    false
}

/// Find production lines containing `.unwrap()` calls, skipping lines inside
/// `#[cfg(test)] mod` blocks via the shared cfg-test range detector.
fn production_unwrap_lines(source: &str) -> Vec<(usize, String)> {
    let ranges = cfg_test_mod_line_ranges(source);
    let mut offenders = Vec::new();

    for (line_idx, line) in source.lines().enumerate() {
        if line_is_inside_cfg_test_mod(&ranges, line_idx) {
            continue;
        }
        let code = code_before_line_comment(line).trim_end();
        if contains_unwrap_call(code) {
            offenders.push((line_idx + 1, line.trim().to_string()));
        }
    }

    offenders
}

#[test]
fn test_production_unwrap_lines_ignore_cfg_test_blocks() {
    let source = r#"
fn production_ok() {
    let value = maybe_value.expect("invariant: demo");
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_demo() {
        let value = maybe_value.unwrap();
        assert_eq!(value, 1);
    }
}

fn after_tests() {
    let other = fallback.unwrap();
}
"#;

    let offenders = production_unwrap_lines(source);
    assert_eq!(
        offenders,
        vec![(16, "let other = fallback.unwrap();".to_string())]
    );
}

#[test]
fn test_production_unwrap_lines_ignore_cfg_test_blocks_with_comment_preamble() {
    let source = r#"
#[cfg(test)]
// Helper note for the test-only module.
/// Extra docs before the item.
#[allow(dead_code)]
mod tests {
    fn test_demo() {
        let value = maybe_value.unwrap();
        assert_eq!(value, 1);
    }
}

fn after_tests() {
    let other = fallback.unwrap();
}
"#;

    let offenders = production_unwrap_lines(source);
    assert_eq!(
        offenders,
        vec![(14, "let other = fallback.unwrap();".to_string())]
    );
}

#[test]
fn test_external_cert_source_has_no_production_unwraps() {
    let cert_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("cert")
        .join("external");
    let source_files = collect_rust_source_files(&cert_root, &EXTERNAL_CERT_RULES);
    assert!(
        !source_files.is_empty(),
        "external cert source scan should discover production files"
    );

    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut offenders = Vec::new();

    for path in source_files {
        let source =
            fs::read_to_string(&path).expect("external cert source file should be readable");
        let relative = path.strip_prefix(repo_root).unwrap_or(path.as_path());
        for (line_no, line) in production_unwrap_lines(&source) {
            offenders.push(format!("{}:{}: {}", relative.display(), line_no, line));
        }
    }

    assert!(
        offenders.is_empty(),
        "production external cert code must not call unwrap():\n{}",
        offenders.join("\n")
    );
}
