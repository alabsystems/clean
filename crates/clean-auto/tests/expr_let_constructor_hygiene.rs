// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::{Path, PathBuf};

const DEPRECATED_EXPR_LET_CALL: &str = concat!("Expr::", "let_", "(");

fn collect_rust_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };

    let mut sorted: Vec<_> = entries.filter_map(|entry| entry.ok()).collect();
    sorted.sort_by_key(|entry| entry.path());

    for entry in sorted {
        let path = entry.path();
        if path.is_dir() {
            collect_rust_files(&path, out);
            continue;
        }

        let is_rust = path.extension().and_then(|ext| ext.to_str()) == Some("rs");
        if is_rust {
            out.push(path);
        }
    }
}

fn deprecated_expr_let_lines(source: &str) -> Vec<(usize, String)> {
    source
        .lines()
        .enumerate()
        .filter_map(|(line_no, line)| {
            let code = line.split("//").next().unwrap_or("");
            code.contains(DEPRECATED_EXPR_LET_CALL)
                .then(|| (line_no + 1, line.trim().to_string()))
        })
        .collect()
}

#[test]
fn test_clean_auto_source_avoids_deprecated_expr_let_constructor() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut source_files = Vec::new();
    collect_rust_files(&manifest_dir.join("src"), &mut source_files);
    collect_rust_files(&manifest_dir.join("tests"), &mut source_files);
    source_files.sort();
    source_files.retain(|path| {
        path.file_name().and_then(|name| name.to_str()) != Some("expr_let_constructor_hygiene.rs")
    });

    assert!(
        !source_files.is_empty(),
        "clean-auto source scan should discover src/ and tests/ files"
    );

    let mut offenders = Vec::new();

    for path in source_files {
        let source =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
        let relative = path.strip_prefix(manifest_dir).unwrap_or(path.as_path());
        for (line_no, line) in deprecated_expr_let_lines(&source) {
            offenders.push(format!("{}:{}: {}", relative.display(), line_no, line));
        }
    }

    assert!(
        offenders.is_empty(),
        "clean-auto source and tests must use Expr::let_named(...), not the deprecated Expr::let_(...):\n{}",
        offenders.join("\n")
    );
}
