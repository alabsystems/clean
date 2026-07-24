// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::{Path, PathBuf};

fn collect_cert_source_files(dir: &Path, files: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .expect("cert source directory should be readable")
        .map(|entry| entry.expect("cert source entry should be readable"))
        .collect();
    entries.sort_by_key(|entry| entry.path());

    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .expect("cert source entry type should be readable");

        if file_type.is_dir() {
            if path.file_name().and_then(|name| name.to_str()) == Some("tests") {
                continue;
            }
            collect_cert_source_files(&path, files);
            continue;
        }

        let is_rust = path.extension().and_then(|ext| ext.to_str()) == Some("rs");
        let is_test_file = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(|name| name == "tests.rs" || name.contains("test"))
            .unwrap_or(false);
        if is_rust && !is_test_file {
            files.push(path);
        }
    }
}

fn brace_delta(line: &str) -> i32 {
    line.bytes().fold(0, |delta, byte| match byte {
        b'{' => delta + 1,
        b'}' => delta - 1,
        _ => delta,
    })
}

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

fn is_cfg_test_preamble_line(trimmed: &str) -> bool {
    trimmed.is_empty()
        || trimmed.starts_with("#[")
        || trimmed.starts_with("//")
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*')
}

fn production_unwrap_lines(source: &str) -> Vec<(usize, String)> {
    let mut offenders = Vec::new();
    let mut brace_depth = 0i32;
    let mut pending_test_cfg = false;
    let mut skip_cfg_test_until_depth: Option<i32> = None;

    for (line_idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        let code = line.split("//").next().unwrap_or("").trim_end();

        if let Some(target_depth) = skip_cfg_test_until_depth {
            brace_depth += brace_delta(code);
            if brace_depth <= target_depth {
                skip_cfg_test_until_depth = None;
            }
            continue;
        }

        if let Some(after_attr) = trimmed.strip_prefix("#[cfg(test)]") {
            let after_attr = after_attr.trim();
            if after_attr.is_empty() {
                pending_test_cfg = true;
                continue;
            }
            if after_attr.ends_with(';') {
                continue;
            }
            skip_cfg_test_until_depth = Some(brace_depth);
            brace_depth += brace_delta(after_attr);
            if brace_depth <= skip_cfg_test_until_depth.expect("cfg(test) target depth set") {
                skip_cfg_test_until_depth = None;
            }
            continue;
        }

        if pending_test_cfg {
            if is_cfg_test_preamble_line(trimmed) {
                continue;
            }
            pending_test_cfg = false;
            if trimmed.ends_with(';') {
                continue;
            }
            skip_cfg_test_until_depth = Some(brace_depth);
            brace_depth += brace_delta(code);
            if brace_depth <= skip_cfg_test_until_depth.expect("cfg(test) target depth set") {
                skip_cfg_test_until_depth = None;
            }
            continue;
        }

        if contains_unwrap_call(code) {
            offenders.push((line_idx + 1, line.trim().to_string()));
        }

        brace_depth += brace_delta(code);
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
    // The leading newline of the raw string is line 1, so `after_tests`'s
    // `.unwrap()` lands on line 13 (the three-line `#[cfg(test)]` + comment
    // preamble before `mod tests` is skipped, not the unwrap inside it).
    assert_eq!(
        offenders,
        vec![(13, "let other = fallback.unwrap();".to_string())]
    );
}

#[test]
fn test_cert_source_has_no_production_unwraps() {
    let cert_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join("cert");
    let mut source_files = Vec::new();
    collect_cert_source_files(&cert_root, &mut source_files);
    assert!(
        !source_files.is_empty(),
        "cert source scan should discover production files"
    );

    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut offenders = Vec::new();

    for path in source_files {
        let source = fs::read_to_string(&path).expect("cert source file should be readable");
        let relative = path.strip_prefix(repo_root).unwrap_or(path.as_path());
        for (line_no, line) in production_unwrap_lines(&source) {
            offenders.push(format!("{}:{}: {}", relative.display(), line_no, line));
        }
    }

    assert!(
        offenders.is_empty(),
        "production cert code must not call unwrap():\n{}",
        offenders.join("\n")
    );
}
