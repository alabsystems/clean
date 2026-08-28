// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hygiene gate: `clean-auto` must build `let` expressions through
//! `Expr::let_named(...)`, never the deprecated positional constructor.
//!
//! LEXED, not split on `//` (lane LOOSE, 2026-08-25). The scan used to keep
//! `line.split("//").next()` and match the remainder, which is wrong in BOTH
//! directions:
//!
//! * FALSE RED — a block comment or a string literal that merely NAMES the
//!   deprecated constructor reads as a call. The prose that explains why a
//!   path uses `let_named` instead is exactly what this gate would then
//!   punish, and the cheapest way to green is to delete the explanation. That
//!   is the anti-correlation shape lane ANTICORR retired across this tree.
//! * FALSE GREEN, and this one is dangerous — `split("//")` truncates at the
//!   first `//` ANYWHERE on the line, string literals included. A real call
//!   sitting after `let u = "http://host";` was never scanned at all.
//!
//! WHY THE LEXER IS DUPLICATED HERE. The canonical copy is `blank_noncode` in
//! `crates/clean-elab/src/test_support/source_scan.rs`. It cannot be shared:
//! `clean-elab` depends on `clean-auto` (crates/clean-elab/Cargo.toml), so a
//! `clean-auto` dev-dependency on `clean-elab` is a dependency cycle, and the
//! helper is `pub(crate)` besides. Both copies carry their own two-way arms;
//! keep them in step.

use std::fs;
use std::path::{Path, PathBuf};

const DEPRECATED_EXPR_LET_CALL: &str = concat!("Expr::", "let_", "(");

// The ONE copy of the lexer in this crate. An integration test is a separate
// crate and cannot see `pub(crate)` items, so it reaches the module by path
// rather than by a second copy; `crates/clean-auto/src/test_support/mod.rs`
// carries the full rationale, including why it cannot be shared with
// clean-elab (clean-elab DEPENDS on clean-auto -- sharing is a cycle).
#[path = "../src/test_support/source_scan.rs"]
mod source_scan;

use source_scan::blank_noncode;

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

/// Lines that actually CALL the deprecated constructor, as
/// `(1-indexed line number, raw source line)`.
fn deprecated_expr_let_lines(source: &str) -> Vec<(usize, String)> {
    let raw: Vec<&str> = source.lines().collect();
    blank_noncode(source)
        .lines()
        .enumerate()
        .filter(|(_, code)| code.contains(DEPRECATED_EXPR_LET_CALL))
        .map(|(idx, _)| {
            let text = raw
                .get(idx)
                .map_or_else(String::new, |l| l.trim().to_string());
            (idx + 1, text)
        })
        .collect()
}

/// DIRECTION 1 of the lane-LOOSE two-way proof: the gate must STOP false-REDing.
///
/// Each arm MENTIONS the deprecated constructor without calling it — a
/// `// SOUNDNESS:`-style line comment, a doc comment, a nested block comment, a
/// string literal, a raw string with hashes, and a `#[doc = "..."]` attribute.
/// Under `split("//")` every block comment, string and attribute here counted.
#[test]
fn test_deprecated_expr_let_lines_ignore_comments_and_string_literals() {
    let source = r####"
// SOUNDNESS: this path must not use Expr::let_( — it uses Expr::let_named.
/// Older revisions called `Expr::let_(` here; they no longer do.
/* mentions Expr::let_( and /* a nested Expr::let_( */ */
fn build() -> Expr {
    let hint = "do not call Expr::let_( any more";
    let raw_hint = r#"a raw string hides Expr::let_( too"#;
    let quote = '"';
    let _ = (hint, raw_hint, quote);
    Expr::let_named(name, ty, val, body)
}

#[doc = "attribute docs naming Expr::let_( are not code"]
fn also_ok() {}
"####;

    assert_eq!(
        deprecated_expr_let_lines(source),
        Vec::<(usize, String)>::new(),
        "comments, string literals and doc attributes that merely NAME the \
         deprecated constructor must not count as calls"
    );
}

/// DIRECTION 2 of the lane-LOOSE two-way proof: the gate must KEEP true-REDing.
///
/// A gate that stops false-REDing and also stops true-REDing has not been
/// fixed, it has been deleted. Three real calls, each in a position the old
/// splitter got wrong or right only by accident:
///
/// * a plain call with a trailing `// ...` comment (the old code caught this),
/// * a call AFTER a string literal containing `//` on the same line — the
///   FALSE-GREEN hole: `split("//")` truncated at `http:` and never saw it,
/// * a call on the line that CLOSES a block comment, invisible to the old code
///   because it never tracked block comments at all.
#[test]
fn test_deprecated_expr_let_lines_still_catch_real_calls() {
    let source = r####"
fn offender_one() -> Expr {
    Expr::let_(name, ty, val, body) // trailing comment, still a call
}

fn offender_two() -> Expr {
    let doc = "https://example.invalid/x"; Expr::let_(name, ty, val, body)
}

/* a block comment
   spanning lines */ fn offender_three() -> Expr { Expr::let_(n, t, v, b) }
"####;

    let offenders = deprecated_expr_let_lines(source);
    let lines: Vec<usize> = offenders.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        lines,
        vec![3, 7, 11],
        "real Expr::let_( calls must still be reported, including after a string \
         literal containing `//` and on a block-comment closing line: {offenders:?}"
    );
    assert!(
        offenders[0].1.contains("trailing comment"),
        "the reported text is the RAW source line, not the blanked one: {:?}",
        offenders[0]
    );
}

#[test]
fn test_blank_noncode_preserves_line_geometry_and_lifetimes() {
    let source = "fn f<'a>(s: &'a str) -> &'a str {\n    let c = '\\'';\n    s\n}\n";
    let blanked = blank_noncode(source);
    assert_eq!(
        blanked.lines().count(),
        source.lines().count(),
        "blanking must not change the number of lines"
    );
    assert!(
        blanked.contains("fn f<'a>(s: &'a str) -> &'a str {"),
        "lifetimes are not char literals and must survive: {blanked:?}"
    );
    assert_eq!(
        blanked.lines().nth(1).unwrap_or_default().trim_end(),
        "    let c =     ;",
        "an escaped char literal must be blanked WHOLE -- the pre-2026-08-25 \
         escape branch stopped on the escaped quote and left the real closing \
         quote behind as stray code: {blanked:?}"
    );
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
