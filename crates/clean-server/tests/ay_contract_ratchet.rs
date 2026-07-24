// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ratchet test: `clean-server` must import ay items from the curated
//! `clean_auto::bridge::ay_contract` path, not the raw
//! `clean_auto::bridge::ay_backend` module.
//!
//! Part of #2763.

use std::{
    path::{Path, PathBuf},
    process::Command,
};

const LEGACY_AY_BACKEND_LINE_PATTERN: &str = "ay_backend::";
const LEGACY_AY_BACKEND_PREFIX: &str = "clean_auto::bridge::ay_backend";

fn collect_tracked_rs_files(dir: &Path) -> Vec<PathBuf> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new("git")
        .arg("-C")
        .arg(manifest_dir)
        .args(["ls-files", "-z", "--"])
        .arg(dir)
        .output()
        .unwrap_or_else(|e| panic!("failed to list tracked files under {}: {e}", dir.display()));
    assert!(
        output.status.success(),
        "git ls-files failed for {}: status={:?}, stderr={}",
        dir.display(),
        output.status.code(),
        String::from_utf8_lossy(&output.stderr),
    );

    let mut files: Vec<PathBuf> = output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
        .map(|entry| {
            PathBuf::from(
                std::str::from_utf8(entry)
                    .unwrap_or_else(|e| panic!("git ls-files emitted non-utf8 path: {e}")),
            )
        })
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("rs"))
        .map(|relative| manifest_dir.join(relative))
        .collect();
    files.sort();
    files
}

fn raw_string_prefix(bytes: &[u8], start: usize) -> Option<(usize, usize)> {
    let mut i = start;
    if bytes.get(i) == Some(&b'b') {
        i += 1;
    }
    if bytes.get(i) != Some(&b'r') {
        return None;
    }
    i += 1;

    let hash_start = i;
    while bytes.get(i) == Some(&b'#') {
        i += 1;
    }

    (bytes.get(i) == Some(&b'"')).then_some((i - hash_start, i + 1 - start))
}

fn skip_raw_string(bytes: &[u8], mut i: usize, hashes: usize, stripped: &mut String) -> usize {
    while i < bytes.len() {
        if bytes[i] == b'\n' {
            stripped.push('\n');
            i += 1;
            continue;
        }
        if bytes[i] == b'"'
            && i + hashes < bytes.len()
            && bytes[i + 1..=i + hashes].iter().all(|byte| *byte == b'#')
        {
            return i + hashes + 1;
        }
        i += 1;
    }
    bytes.len()
}

fn skip_string(bytes: &[u8], mut i: usize, stripped: &mut String) -> usize {
    let mut escaped = false;
    while i < bytes.len() {
        let byte = bytes[i];
        if byte == b'\n' {
            stripped.push('\n');
            return i + 1;
        }
        if escaped {
            escaped = false;
            i += 1;
            continue;
        }
        if byte == b'\\' {
            escaped = true;
            i += 1;
            continue;
        }
        if byte == b'"' {
            return i + 1;
        }
        i += 1;
    }
    bytes.len()
}

fn starts_with_pair(bytes: &[u8], i: usize, first: u8, second: u8) -> bool {
    i + 1 < bytes.len() && bytes[i] == first && bytes[i + 1] == second
}

fn skip_line_comment(bytes: &[u8], mut i: usize) -> usize {
    i += 2;
    while i < bytes.len() && bytes[i] != b'\n' {
        i += 1;
    }
    i
}

fn advance_block_comment(
    bytes: &[u8],
    mut i: usize,
    mut block_comment_depth: usize,
    stripped: &mut String,
) -> (usize, usize) {
    if starts_with_pair(bytes, i, b'/', b'*') {
        block_comment_depth += 1;
        i += 2;
    } else if starts_with_pair(bytes, i, b'*', b'/') {
        block_comment_depth -= 1;
        i += 2;
    } else {
        if bytes[i] == b'\n' {
            stripped.push('\n');
        }
        i += 1;
    }
    (i, block_comment_depth)
}

fn skip_non_code_token(bytes: &[u8], i: usize, stripped: &mut String) -> Option<(usize, usize)> {
    if starts_with_pair(bytes, i, b'/', b'/') {
        return Some((skip_line_comment(bytes, i), 0));
    }
    if starts_with_pair(bytes, i, b'/', b'*') {
        return Some((i + 2, 1));
    }
    if let Some((hashes, prefix_len)) = raw_string_prefix(bytes, i) {
        return Some((skip_raw_string(bytes, i + prefix_len, hashes, stripped), 0));
    }
    if bytes[i] == b'"' {
        return Some((skip_string(bytes, i + 1, stripped), 0));
    }
    if bytes[i] == b'b' && i + 1 < bytes.len() && bytes[i + 1] == b'"' {
        return Some((skip_string(bytes, i + 2, stripped), 0));
    }
    None
}

fn strip_comments_and_string_literals(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut stripped = String::with_capacity(source.len());
    let mut i = 0;
    let mut block_comment_depth = 0usize;

    while i < bytes.len() {
        if block_comment_depth > 0 {
            (i, block_comment_depth) =
                advance_block_comment(bytes, i, block_comment_depth, &mut stripped);
            continue;
        }

        if let Some((next_i, next_block_depth)) = skip_non_code_token(bytes, i, &mut stripped) {
            i = next_i;
            block_comment_depth = next_block_depth;
            continue;
        }

        stripped.push(bytes[i] as char);
        i += 1;
    }

    stripped
}

fn normalize_for_legacy_path_scan(source: &str) -> String {
    let mut normalized: String = strip_comments_and_string_literals(source)
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect();

    while normalized.contains("::{") {
        normalized = normalized.replace("::{", "::");
    }

    normalized
}

fn source_contains_legacy_ay_backend(source: &str) -> bool {
    normalize_for_legacy_path_scan(source).contains(LEGACY_AY_BACKEND_PREFIX)
}

fn legacy_ay_backend_lines(source: &str) -> Vec<(usize, String)> {
    let stripped = strip_comments_and_string_literals(source);
    stripped
        .lines()
        .zip(source.lines())
        .enumerate()
        .filter_map(|(line_no, (code, original))| {
            let normalized: String = code.chars().filter(|ch| !ch.is_whitespace()).collect();
            normalized
                .contains(LEGACY_AY_BACKEND_LINE_PATTERN)
                .then(|| (line_no + 1, original.trim().to_string()))
        })
        .collect()
}

#[test]
fn test_clean_server_uses_curated_ay_contract_path() {
    let src_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let files = collect_tracked_rs_files(Path::new("src"));

    let mut offenders: Vec<String> = Vec::new();
    for file in &files {
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", file.display()));
        if source_contains_legacy_ay_backend(&content) {
            let rel = file.strip_prefix(&src_root).unwrap_or(file);
            let lines = legacy_ay_backend_lines(&content);
            if lines.is_empty() {
                offenders.push(format!(
                    "  {}: legacy `ay_backend` dependency detected",
                    rel.display()
                ));
                continue;
            }
            for (line_no, line) in lines {
                offenders.push(format!("  {}:{}: {}", rel.display(), line_no, line));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "clean-server source must import ay items from \
         clean_auto::bridge::ay_contract, not the raw ay_backend path.\n\
         Offending lines:\n{}",
        offenders.join("\n"),
    );
}

#[test]
fn test_legacy_ay_backend_detection_ignores_string_literals() {
    let source = r##"
const LEGACY_BACKEND_PATH: &str = "clean_auto::bridge::ay_backend";
let fixture = r#"
match clean_auto::bridge::ay_backend::AyLogic::QfUf {
    clean_auto::bridge::ay_backend::AyLogic::QfUf => "qfuf",
    _ => "other",
}
"#;
"##;

    assert!(
        !source_contains_legacy_ay_backend(source),
        "string fixtures must not trigger the ratchet"
    );
    assert_eq!(
        legacy_ay_backend_lines(source),
        Vec::<(usize, String)>::new(),
        "string fixtures should not produce line-level offenders",
    );
}

#[test]
fn test_legacy_ay_backend_detection_catches_grouped_use_tree() {
    let source = r#"
use clean_auto::{
    bridge::{ay_backend::AyLogic, ay_contract::AyProofResult},
};
"#;

    assert!(
        source_contains_legacy_ay_backend(source),
        "grouped use trees must not evade the ratchet"
    );
    assert_eq!(
        legacy_ay_backend_lines(source),
        vec![(
            3,
            "bridge::{ay_backend::AyLogic, ay_contract::AyProofResult},".to_string()
        )],
    );
}
