// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ratchet test: `clean-server` must import ay items from the curated
//! `clean_auto::bridge::ay_contract` path, not the raw
//! `clean_auto::bridge::ay_backend` module.
//!
//! Part of #2763.

use std::path::{Path, PathBuf};

const LEGACY_AY_BACKEND_PATH: &str = "clean_auto::bridge::ay_backend::";
const LEGACY_AY_BACKEND_PREFIX: &str = "clean_auto::bridge::ay_backend";
const SELF_FILE_NAME: &str = "ay_contract_ratchet.rs";

fn collect_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if !dir.is_dir() {
        return files;
    }
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.is_dir() {
            files.extend(collect_rs_files(&path));
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs")
            && path.file_name().and_then(|name| name.to_str()) != Some(SELF_FILE_NAME)
        {
            files.push(path);
        }
    }
    files.sort();
    files
}

fn strip_comments(source: &str) -> String {
    let mut stripped = String::with_capacity(source.len());
    let bytes = source.as_bytes();
    let mut i = 0;
    let mut block_depth = 0usize;

    while i < bytes.len() {
        if block_depth == 0 && i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            block_depth += 1;
            i += 2;
            continue;
        }

        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'*' && bytes[i + 1] == b'/' {
                block_depth -= 1;
                i += 2;
                continue;
            }
            if bytes[i] == b'\n' {
                stripped.push('\n');
            }
            i += 1;
            continue;
        }

        stripped.push(bytes[i] as char);
        i += 1;
    }

    stripped
}

fn normalize_for_legacy_path_scan(source: &str) -> String {
    let mut normalized: String = strip_comments(source)
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
    source
        .lines()
        .enumerate()
        .filter_map(|(line_no, line)| {
            let code = line.split("//").next().unwrap_or("");
            code.contains("ay_backend::")
                .then(|| (line_no + 1, line.trim().to_string()))
        })
        .collect()
}

#[test]
fn test_clean_server_uses_curated_ay_contract_path() {
    let src_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let files = collect_rs_files(&src_root);

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
}

#[test]
fn test_legacy_ay_backend_detection_catches_direct_path_usage() {
    let source = r#"
fn logic_name() -> &'static str {
    match clean_auto::bridge::ay_backend::AyLogic::QfUf {
        clean_auto::bridge::ay_backend::AyLogic::QfUf => "qfuf",
        _ => "other",
    }
}
"#;

    assert!(
        source_contains_legacy_ay_backend(source),
        "direct legacy backend paths must be detected"
    );
}

#[test]
fn test_legacy_ay_backend_detection_ignores_curated_contract_path() {
    let source = r#"
use clean_auto::{
    bridge::{ay_contract::AyLogic, ay_contract::AyProofResult},
};

fn logic_name() -> &'static str {
    match clean_auto::bridge::ay_contract::AyLogic::QfUf {
        clean_auto::bridge::ay_contract::AyLogic::QfUf => "qfuf",
        _ => "other",
    }
}
"#;

    assert!(
        !source_contains_legacy_ay_backend(source),
        "curated contract usage must remain allowed"
    );
    assert_eq!(
        legacy_ay_backend_lines(source),
        Vec::<(usize, String)>::new()
    );
    assert!(
        !source.contains(LEGACY_AY_BACKEND_PATH),
        "curated-path fixture should not accidentally include the legacy path"
    );
}

#[test]
fn test_legacy_ay_backend_detection_ignores_comments() {
    let source = r#"
// use clean_auto::bridge::ay_backend::AyLogic;
/* clean_auto::{bridge::{ay_backend::AyLogic}} */
use clean_auto::bridge::ay_contract::AyLogic;
"#;

    assert!(
        !source_contains_legacy_ay_backend(source),
        "comments must not trigger the ratchet"
    );
}
