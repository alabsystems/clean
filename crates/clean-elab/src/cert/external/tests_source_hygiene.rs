// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;

use crate::test_support::source_scan::{
    collect_rust_source_files, production_code_lines, SourceScanRules,
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

/// Find production lines containing `.unwrap()` CALLS.
///
/// LEXED, not split on `//` (lane LOOSE, 2026-08-25). This scanner used to keep
/// `line.split("//").next()` and match on the remainder, which is wrong in both
/// directions:
///
/// * FALSE RED — a block comment or a string literal that merely NAMES
///   `.unwrap()` reads as a call. The prose that explains why a production path
///   does not unwrap is exactly the prose this gate then punishes; that is the
///   anti-correlation shape lane ANTICORR retired elsewhere in this tree.
/// * FALSE GREEN, and this is the dangerous one — `split("//")` truncates the
///   line at the first `//` ANYWHERE, string literals included. A real
///   `.unwrap()` sitting after `let u = "http://host";` on the same line was
///   never seen at all.
///
/// [`production_code_lines`] blanks line comments, NESTING block comments, and
/// string / raw-string / char-literal bodies with a character state machine,
/// then drops inline `#[cfg(test)] mod` bodies — so both directions close with
/// one call. Line numbers are 1-indexed and survive the blanking, so the
/// offender is still reported at its real source location with its RAW text.
fn production_unwrap_lines(source: &str) -> Vec<(usize, String)> {
    let raw: Vec<&str> = source.lines().collect();
    production_code_lines(source)
        .into_iter()
        .filter(|(_, code)| contains_unwrap_call(code.trim_end()))
        .map(|(line_no, _)| {
            let text = raw
                .get(line_no - 1)
                .map_or_else(String::new, |l| l.trim().to_string());
            (line_no, text)
        })
        .collect()
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

/// DIRECTION 1 of the lane-LOOSE two-way proof: the gate must STOP false-REDing.
///
/// Every arm below MENTIONS `.unwrap()` without calling it — a `// SOUNDNESS:`
/// style line comment, a doc comment, a block comment (including a nested one),
/// a string literal, a raw string with hashes, and a `#[doc = "..."]` attribute.
/// Under `split("//")` the block comments, the strings and the attribute all
/// counted. Expected: zero offenders.
#[test]
fn test_production_unwrap_lines_ignore_comments_and_string_literals() {
    let source = r####"
// SOUNDNESS: this path must never call .unwrap(); it returns Err instead.
/// Callers used to `.unwrap()` here. They no longer do.
/* A block comment naming .unwrap() and /* a nested one naming .unwrap() */ */
fn production_ok(raw: &str) -> Result<u32, String> {
    let hint = "do not call .unwrap() on this";
    let raw_hint = r#"a raw string hides .unwrap() too"#;
    let ch = '"';
    let _ = (hint, raw_hint, ch);
    raw.parse::<u32>().map_err(|e| e.to_string())
}

#[doc = "attribute docs naming .unwrap() are not code"]
fn also_ok() {}
"####;

    assert_eq!(
        production_unwrap_lines(source),
        Vec::<(usize, String)>::new(),
        "comments, string literals and doc attributes that merely NAME .unwrap() \
         must not count as calls"
    );
}

/// DIRECTION 2 of the lane-LOOSE two-way proof: the gate must KEEP true-REDing.
///
/// A gate that stops false-REDing and also stops true-REDing has not been
/// fixed, it has been deleted. Three real calls, each in a position the old
/// splitter got wrong or only got right by accident:
///
/// * a plain call with a trailing `// ...` comment (the old code got this one),
/// * a call AFTER a string literal containing `//` on the same line — the
///   FALSE-GREEN hole: `split("//")` truncated at `http:` and never saw it,
/// * a call on the line that CLOSES a block comment, which the old code could
///   not see at all because it never tracked block comments.
#[test]
fn test_production_unwrap_lines_still_catch_real_calls() {
    let source = r#"
fn offender_one() {
    let value = fallible().unwrap(); // trailing comment, still a call
}

fn offender_two() {
    let url = "http://example.invalid"; let value = fallible().unwrap();
}

/* a block comment
   spanning lines */ fn offender_three() { let v = fallible().unwrap(); }
"#;

    let offenders = production_unwrap_lines(source);
    let lines: Vec<usize> = offenders.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        lines,
        vec![3, 7, 11],
        "real .unwrap() calls must still be reported, including after a string \
         literal containing `//` and on a block-comment closing line: {offenders:?}"
    );
    assert!(
        offenders[0].1.contains("trailing comment"),
        "the reported text is the RAW source line, not the blanked one: {:?}",
        offenders[0]
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
