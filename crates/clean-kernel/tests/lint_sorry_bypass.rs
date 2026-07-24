// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Repo-scanning lint: forbid direct sorry constant construction.
//!
//! All sorry term creation must go through
//! [`clean_kernel::sorry::create_sorry_term`] so the global counter,
//! `DENY_SORRY` enforcement, and location tracking are respected.
//!
//! This test catches three direct-construction patterns that bypass that
//! infrastructure:
//!
//! 1. `mk_const_str("sorry")`
//! 2. `Expr::const_str("sorry", ...)` / `Expr::const_str_levels("sorry", ...)`
//! 3. `Expr::const_(Name::from_string("sorry"), ...)` (path-qualified
//!    `Name::from_string` accepted, e.g. `clean_kernel::Name::from_string`)
//!
//! This replaces `scripts/lint_sorry_bypass.sh` (Wave 72 migration). Part of
//! #1144. See [`docs/SCRIPTS_MIGRATION.md`](../../../docs/SCRIPTS_MIGRATION.md).
//!
//! Run: `cargo test --locked -p clean-kernel --test lint_sorry_bypass`

use std::fs;
use std::path::{Path, PathBuf};

/// Files that are allowed to construct sorry constants directly because they
/// implement the canonical `create_sorry_term` API or scan for it.
const ALLOWED_FILES: &[&str] = &[
    "crates/clean-kernel/src/sorry/build.rs",
    "crates/clean-kernel/src/sorry/tests.rs",
    "crates/clean-kernel/src/sorry/mod.rs",
    "crates/clean-kernel/src/expr/sorry.rs",
    "crates/clean-kernel/src/env/core.rs",
    // A `#[cfg(test)]` block builds a `sorry`-headed proof term ON PURPOSE to
    // verify `audit_certification` DETECTS it (the auditor's positive case);
    // the construction is test-only and never a real proof.
    "crates/clean-kernel/src/env/axiom_audit.rs",
    "crates/clean-kernel/tests/sorry_scan_equivalence.rs",
    // This test itself contains the patterns as string literals in
    // documentation and probe data; allowlist it so it doesn't self-fail.
    "crates/clean-kernel/tests/lint_sorry_bypass.rs",
];

/// Resolve the repo root from `CARGO_MANIFEST_DIR` (= `crates/clean-kernel`).
fn repo_root() -> PathBuf {
    let manifest = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest)
        .parent()
        .and_then(Path::parent)
        .expect("repo root resolvable from CARGO_MANIFEST_DIR")
        .to_path_buf()
}

/// Recursively walk a directory, collecting `*.rs` file paths.
fn collect_rs_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            // Skip `target/` if a stray one shows up under crates/.
            if path.file_name().is_some_and(|n| n == "target") {
                continue;
            }
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Skip leading whitespace and return the trimmed-left slice.
fn trim_start(s: &str) -> &str {
    s.trim_start()
}

/// Match `<ident>(` after optional whitespace, where `<ident>` is a Rust
/// identifier (letters, digits, underscores, starting non-digit).
fn match_call(s: &str, name: &str) -> Option<usize> {
    let mut idx = 0;
    let bytes = s.as_bytes();
    while idx < bytes.len() {
        // Find candidate start position of `name`.
        let found = s[idx..].find(name)?;
        let pos = idx + found;
        // Word-boundary on the left: previous char must not be ident-char.
        if pos > 0 {
            let prev = bytes[pos - 1];
            if prev.is_ascii_alphanumeric() || prev == b'_' {
                idx = pos + 1;
                continue;
            }
        }
        // After name, skip whitespace then expect '('.
        let after = pos + name.len();
        let mut j = after;
        while j < bytes.len() && bytes[j].is_ascii_whitespace() {
            j += 1;
        }
        if j < bytes.len() && bytes[j] == b'(' {
            return Some(j + 1);
        }
        idx = pos + 1;
    }
    None
}

/// Return true if, after the open-paren at `pos`, the next non-whitespace
/// content is the literal `"sorry"` (with optional trailing whitespace then
/// `,` or `)`).
fn next_arg_is_sorry_literal(s: &str, pos: usize) -> bool {
    let bytes = s.as_bytes();
    let mut j = pos;
    while j < bytes.len() && bytes[j].is_ascii_whitespace() {
        j += 1;
    }
    let needle = b"\"sorry\"";
    if j + needle.len() > bytes.len() {
        return false;
    }
    if &bytes[j..j + needle.len()] != needle {
        return false;
    }
    let mut k = j + needle.len();
    while k < bytes.len() && bytes[k].is_ascii_whitespace() {
        k += 1;
    }
    matches!(bytes.get(k), Some(b',') | Some(b')'))
}

/// Detect pattern 1: `mk_const_str("sorry")`.
fn detects_mk_const_str_sorry(line: &str) -> bool {
    if let Some(after_paren) = match_call(line, "mk_const_str") {
        if next_arg_is_sorry_literal(line, after_paren) {
            return true;
        }
    }
    false
}

/// Detect pattern 2: `Expr::const_str("sorry", ...)` or
/// `Expr::const_str_levels("sorry", ...)`.
fn detects_expr_const_str_sorry(line: &str) -> bool {
    for needle in ["Expr::const_str_levels", "Expr::const_str"] {
        if let Some(after_paren) = match_call(line, needle) {
            if next_arg_is_sorry_literal(line, after_paren) {
                return true;
            }
        }
    }
    false
}

/// Detect pattern 3: `Expr::const_( ...Name::from_string("sorry") ... )`.
///
/// The path leading up to `Name::from_string` may include `::`-qualified
/// prefixes (e.g. `clean_kernel::Name::from_string`). The bypass pattern is
/// "an `Expr::const_(` call whose first argument is `Name::from_string("sorry")`".
fn detects_expr_const_name_from_string_sorry(line: &str) -> bool {
    let Some(after_paren) = match_call(line, "Expr::const_") else {
        return false;
    };
    // Within the same line after the open paren, look for
    // `Name::from_string ( "sorry" )`. Path prefixes are accepted because
    // they appear before `Name::from_string` and we only need to find the
    // substring; word-boundary on `Name` is enforced by match_call.
    let tail = &line[after_paren..];
    let Some(call_pos) = match_call(tail, "Name::from_string") else {
        return false;
    };
    next_arg_is_sorry_literal(tail, call_pos)
}

fn is_comment_only(line: &str) -> bool {
    trim_start(line).starts_with("//")
}

/// Normalize a path to a forward-slash, repo-relative string (e.g.
/// `crates/clean-kernel/src/foo.rs`).
fn normalize(repo_root: &Path, path: &Path) -> String {
    let rel = path.strip_prefix(repo_root).unwrap_or(path);
    rel.to_string_lossy().replace('\\', "/")
}

#[test]
fn lint_sorry_bypass_finds_no_direct_constructions() {
    let root = repo_root();
    let crates_dir = root.join("crates");
    assert!(
        crates_dir.is_dir(),
        "crates/ directory must exist at repo root: {}",
        crates_dir.display(),
    );

    let mut files = Vec::new();
    collect_rs_files(&crates_dir, &mut files);
    files.sort();
    assert!(
        !files.is_empty(),
        "expected to find Rust source files under crates/",
    );

    let mut violations: Vec<String> = Vec::new();

    for path in &files {
        let rel = normalize(&root, path);
        if ALLOWED_FILES.contains(&rel.as_str()) {
            continue;
        }
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        for (idx, raw) in text.lines().enumerate() {
            if is_comment_only(raw) {
                continue;
            }
            let lineno = idx + 1;
            if detects_mk_const_str_sorry(raw)
                || detects_expr_const_str_sorry(raw)
                || detects_expr_const_name_from_string_sorry(raw)
            {
                violations.push(format!("{rel}:{lineno}: {}", raw.trim_end()));
            }
        }
    }

    if !violations.is_empty() {
        let count = violations.len();
        let body = violations.join("\n");
        panic!(
            "SORRY BYPASS: {count} direct sorry construction(s) detected. All sorry \
creation must use clean_kernel::sorry::create_sorry_term(). If a use is \
legitimate, add the file to ALLOWED_FILES in this test.\n{body}",
        );
    }
}

// --- Self-tests for the matchers --------------------------------------------

#[cfg(test)]
mod matcher_tests {
    use super::*;

    #[test]
    fn mk_const_str_positive() {
        assert!(detects_mk_const_str_sorry(
            "    let s = mk_const_str(\"sorry\");"
        ));
        assert!(detects_mk_const_str_sorry("mk_const_str ( \"sorry\" )"));
    }

    #[test]
    fn mk_const_str_negative_not_sorry() {
        assert!(!detects_mk_const_str_sorry("mk_const_str(\"axiom\")"));
    }

    #[test]
    fn mk_const_str_negative_substring_in_other_ident() {
        assert!(!detects_mk_const_str_sorry("my_mk_const_str(\"sorry\")"));
    }

    #[test]
    fn expr_const_str_positive() {
        assert!(detects_expr_const_str_sorry(
            "Expr::const_str(\"sorry\", vec![])"
        ));
        assert!(detects_expr_const_str_sorry(
            "Expr::const_str_levels(\"sorry\", vec![])"
        ));
    }

    #[test]
    fn expr_const_str_negative() {
        assert!(!detects_expr_const_str_sorry(
            "Expr::const_str(\"propext\", vec![])"
        ));
    }

    #[test]
    fn expr_const_name_from_string_positive() {
        assert!(detects_expr_const_name_from_string_sorry(
            "Expr::const_(Name::from_string(\"sorry\"), vec![])"
        ));
        assert!(detects_expr_const_name_from_string_sorry(
            "Expr::const_(clean_kernel::Name::from_string(\"sorry\"), vec![])"
        ));
    }

    #[test]
    fn expr_const_name_from_string_negative() {
        assert!(!detects_expr_const_name_from_string_sorry(
            "Expr::const_(Name::from_string(\"axiom\"), vec![])"
        ));
        assert!(!detects_expr_const_name_from_string_sorry(
            "Expr::const_(names::QUOT.clone(), vec![])"
        ));
    }

    #[test]
    fn comment_lines_ignored_by_main_test_path() {
        assert!(is_comment_only("    // mk_const_str(\"sorry\")"));
        assert!(is_comment_only("// Expr::const_str(\"sorry\")"));
        assert!(!is_comment_only("let x = 1; // mk_const_str(\"sorry\")"));
    }
}
