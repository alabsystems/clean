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
    // LEXED FIRST (lane LOOSE, 2026-08-25). The brace tracker below decides
    // where a `#[cfg(test)] mod` block ENDS, so a `{` or `}` inside a string
    // literal or a block comment moved that boundary and silently reclassified
    // production lines as test lines -- a FAIL-OPEN direction, unlike the
    // false-RED this lane started from. Callers that already hold blanked text
    // (`production_code_lines`) pay an idempotent second pass.
    let blanked = blank_noncode(content);
    let lines: Vec<&str> = blanked.lines().collect();
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

    // `lines` arrives already blanked from `cfg_test_mod_line_ranges`, so
    // comments and literal bodies contribute no braces here.
    for (idx, line) in lines.iter().enumerate().skip(start_line) {
        for ch in line.chars() {
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
// Non-code blanking (the anti-correlation fix, lane ANTICORR 2026-08-25)
// ---------------------------------------------------------------------------

/// Replace every comment and every string/char-literal body with spaces,
/// preserving byte length, line count and column geometry.
///
/// WHY THIS EXISTS. A ratchet that greps RAW LINES for a forbidden call does
/// not count calls — it counts MENTIONS. In this tree the two are systematically
/// different, and the difference has a sign: the mentions live in the comments
/// that EXPLAIN why the forbidden call is not being made. `metas.assign(` and
/// `.close_goal_unchecked(` are both ratcheted to 0, so a single
/// `// SOUNDNESS:` line naming either one — the exact prose CLAUDE.md's
/// soundness rule asks for — turned the ratchet red without a line of behaviour
/// changing. That is ANTI-CORRELATION: the gate punishes the behaviour it exists
/// to encourage, and the cheapest way to make it green is to delete the
/// explanation. Same defect that retired `prover_phase_0_audit.sh` (see the
/// `retired` list in data/gate_registry.json), same fix as
/// `scripts/check_add_decl_ratchet.py`: lex first, then count.
///
/// A character state machine, not a Rust parser: line comments, NESTING block
/// comments, strings with escapes, raw strings with hash delimiters, and char
/// literals distinguished from lifetimes. Deterministic and monotone, which is
/// what a ratchet needs; it is not required to be perfectly precise.
pub(crate) fn blank_noncode(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0usize;
    // Push `n` blank bytes, keeping newlines so line numbers survive.
    let push_blank = |out: &mut String, from: usize, to: usize| {
        for &b in &bytes[from..to] {
            out.push(if b == b'\n' { '\n' } else { ' ' });
        }
    };
    while i < bytes.len() {
        let b = bytes[i];
        // line comment
        if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            let mut j = i;
            while j < bytes.len() && bytes[j] != b'\n' {
                j += 1;
            }
            push_blank(&mut out, i, j);
            i = j;
            continue;
        }
        // block comment (Rust block comments nest)
        if b == b'/' && bytes.get(i + 1) == Some(&b'*') {
            let mut depth = 1usize;
            let mut j = i + 2;
            while j < bytes.len() && depth > 0 {
                if bytes[j] == b'/' && bytes.get(j + 1) == Some(&b'*') {
                    depth += 1;
                    j += 2;
                } else if bytes[j] == b'*' && bytes.get(j + 1) == Some(&b'/') {
                    depth -= 1;
                    j += 2;
                } else {
                    j += 1;
                }
            }
            push_blank(&mut out, i, j.min(bytes.len()));
            i = j.min(bytes.len());
            continue;
        }
        // raw string: r"..." / r#"..."# / br#"..."#
        if let Some(hashes) = raw_string_open(bytes, i) {
            let quote_at = i + raw_prefix_len(bytes, i) + hashes;
            let mut j = quote_at + 1;
            let mut end = bytes.len();
            while j < bytes.len() {
                if bytes[j] == b'"' && bytes[j + 1..].iter().take(hashes).all(|&h| h == b'#') {
                    end = (j + 1 + hashes).min(bytes.len());
                    break;
                }
                j += 1;
            }
            push_blank(&mut out, i, end);
            i = end;
            continue;
        }
        // string literal: "..." / b"..."
        if b == b'"' || (b == b'b' && bytes.get(i + 1) == Some(&b'"')) {
            let open = if b == b'"' { i } else { i + 1 };
            let mut j = open + 1;
            while j < bytes.len() {
                match bytes[j] {
                    b'\\' => j += 2,
                    b'"' => {
                        j += 1;
                        break;
                    }
                    _ => j += 1,
                }
            }
            let end = j.min(bytes.len());
            push_blank(&mut out, i, end);
            i = end;
            continue;
        }
        // char literal, distinguished from a lifetime (`'a`, `'static`).
        if b == b'\'' {
            if let Some(end) = char_literal_end(bytes, i) {
                push_blank(&mut out, i, end);
                i = end;
                continue;
            }
        }
        out.push(b as char);
        i += 1;
    }
    out
}

fn raw_prefix_len(bytes: &[u8], i: usize) -> usize {
    if bytes.get(i) == Some(&b'b') && bytes.get(i + 1) == Some(&b'r') {
        2
    } else if bytes.get(i) == Some(&b'r') {
        1
    } else {
        0
    }
}

/// If a raw-string literal starts at `i`, return its `#` count.
fn raw_string_open(bytes: &[u8], i: usize) -> Option<usize> {
    let prefix = raw_prefix_len(bytes, i);
    if prefix == 0 {
        return None;
    }
    // `r` must not be the tail of an identifier (`for`, `char`, `expr`).
    if i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_') {
        return None;
    }
    let mut j = i + prefix;
    let mut hashes = 0usize;
    while bytes.get(j) == Some(&b'#') {
        hashes += 1;
        j += 1;
    }
    (bytes.get(j) == Some(&b'"')).then_some(hashes)
}

/// If a char literal starts at `i`, return the index one past its closing quote.
/// `'a` / `'static` (lifetimes) and `'a: loop` (labels) return `None`.
fn char_literal_end(bytes: &[u8], i: usize) -> Option<usize> {
    match bytes.get(i + 1)? {
        b'\\' => {
            // Skip the ESCAPE SEQUENCE, then require the closing quote.
            // Scanning forward to the next `'` instead (lane LOOSE, 2026-08-25)
            // mis-lexed `'\\''`: it stopped on the ESCAPED quote and left the
            // real closing quote behind as stray code, which can then open a
            // spurious literal further down the line. `\\u{...}` is
            // variable-length, so it is scanned to its `}`.
            let mut j = i + 2;
            if bytes.get(j) == Some(&b'u') {
                while j < bytes.len() && bytes[j] != b'}' {
                    j += 1;
                }
                j += 1;
            } else {
                j += 1;
            }
            (bytes.get(j) == Some(&b'\'')).then(|| j + 1)
        }
        _ => (bytes.get(i + 2) == Some(&b'\'')).then_some(i + 3),
    }
}

/// The production, code-only lines of a Rust file: comments and literal bodies
/// blanked, inline `#[cfg(test)]` module bodies dropped.
///
/// Returns `(1-indexed line number, code-only line)` so a caller can still
/// report the offending source location.
pub(crate) fn production_code_lines(content: &str) -> Vec<(usize, String)> {
    let blanked = blank_noncode(content);
    let ranges = cfg_test_mod_line_ranges(&blanked);
    blanked
        .lines()
        .enumerate()
        .filter(|(idx, _)| !line_is_inside_cfg_test_mod(&ranges, *idx))
        .map(|(idx, line)| (idx + 1, line.to_string()))
        .collect()
}

// ---------------------------------------------------------------------------
// Line-level helpers
// ---------------------------------------------------------------------------

// `code_before_line_comment` (a `line.split("//").next()` one-liner) was DELETED
// 2026-08-25 by lane LOOSE, after its last two callers
// (crates/clean-elab/src/cert/external/tests_source_hygiene.rs and, in spirit,
// crates/clean-auto/tests/expr_let_constructor_hygiene.rs) moved onto
// [`production_code_lines`]. It was wrong in BOTH directions and neither is
// obvious from the call site, which is why it is gone rather than deprecated:
//
//   FALSE RED   a block comment, a doc comment or a string literal that merely
//               NAMES a forbidden call reads as code.
//   FALSE GREEN it truncates at the first `//` ANYWHERE, string literals
//               included, so a real call after `let u = "http://host";` on the
//               same line is never scanned.
//
// `scripts/check_gate_registry.py` no longer accepts its name as evidence of
// `source_scan.kind == "lexed"` either. Use [`production_code_lines`].

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
fn blank_noncode_erases_comments_strings_and_char_literals() {
    let src = r###"// metas.assign(hidden)
/* block metas.assign(hidden) */
/** doc metas.assign(hidden) */
let s = "metas.assign(hidden)";
let r = r#"metas.assign(hidden)"#;
let c = '"';
state.metas.assign(goal, proof); // trailing metas.assign(hidden)
"###;
    let blanked = blank_noncode(src);
    assert_eq!(
        blanked.matches("metas.assign(").count(),
        1,
        "only the real call survives blanking; got:\n{blanked}"
    );
    assert_eq!(
        blanked.lines().count(),
        src.lines().count(),
        "blanking must preserve line geometry"
    );
}

#[test]
fn blank_noncode_handles_nested_block_comments_and_lifetimes() {
    let src = "/* outer /* inner metas.assign( */ still comment */ fn f<'a>(x: &'a str) {}\n";
    let blanked = blank_noncode(src);
    assert_eq!(blanked.matches("metas.assign(").count(), 0);
    assert!(
        blanked.contains("fn f<'a>(x: &'a str)"),
        "lifetimes are not char literals; got: {blanked}"
    );
}

#[test]
fn production_code_lines_drops_cfg_test_bodies_and_reports_line_numbers() {
    let src = "fn before() {\n    metas.assign();\n}\n\n#[cfg(test)]\nmod tests {\n    fn t() { metas.assign(); }\n}\n\nfn after() {\n    metas.assign();\n}\n";
    let lines = production_code_lines(src);
    let hits: Vec<usize> = lines
        .iter()
        .filter(|(_, code)| code.contains("metas.assign("))
        .map(|(n, _)| *n)
        .collect();
    assert_eq!(
        hits,
        vec![2, 11],
        "cfg(test) body excluded, 1-indexed lines kept"
    );
}

/// Lane LOOSE, 2026-08-25: `'\''` must be blanked WHOLE.
///
/// The original escape branch scanned forward to the next `'`, which is the
/// ESCAPED quote — so it stopped one byte early and left the real closing quote
/// behind as stray code. A stray quote can open a spurious char literal further
/// along the line and blank real code after it (a FAIL-OPEN direction).
#[test]
fn blank_noncode_blanks_escaped_char_literals_whole() {
    let src = "let c = '\\'';\nlet n = '\\n';\nlet u = '\\u{1F600}';\nfoo.bar();\n";
    let blanked = blank_noncode(src);

    assert!(
        !blanked.contains('\''),
        "no quote may survive an escaped char literal: {blanked:?}"
    );
    assert_eq!(
        blanked.lines().count(),
        src.lines().count(),
        "line geometry must survive"
    );
    assert!(
        blanked.contains("foo.bar();"),
        "real code after the literals must survive: {blanked:?}"
    );
}

/// Lane LOOSE, 2026-08-25: a brace inside a string literal or a block comment
/// must not move the end of a `#[cfg(test)] mod` block.
///
/// This is the FAIL-OPEN half of the raw-text defect: the tracker used to count
/// every `{`/`}` outside a `//` comment, so an unbalanced brace in a string
/// swallowed the production code after the test module (or ended the module
/// early). Both directions are wrong; only one of them is silent.
#[test]
fn cfg_test_mod_line_ranges_ignore_braces_in_strings_and_block_comments() {
    let content = r####"#[cfg(test)]
mod tests {
    fn helper() {
        let brace = "an unbalanced { in a string";
        /* and a } in a block comment */
    }
}

fn production_after() {
    metas.assign();
}
"####;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(
        ranges,
        vec![0..=6],
        "the test module must end at its real closing brace"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 9),
        "production code after the module must not be swallowed by a brace \
         that lives inside a string literal"
    );

    let production: Vec<usize> = production_code_lines(content)
        .into_iter()
        .filter(|(_, code)| code.contains("metas.assign("))
        .map(|(n, _)| n)
        .collect();
    assert_eq!(
        production,
        vec![10],
        "the real production call must still be counted"
    );
}
