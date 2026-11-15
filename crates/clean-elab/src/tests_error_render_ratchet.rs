// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ratchet: kernel terms must not reach a user-facing error message through
//! Rust's derived `Debug`.
//!
//! `Expr`, `Name`, `Level` and the kernel's `TypeError` all carry hand-written
//! `Display` impls meant for exactly this. `Debug` renders `Name` as
//!
//! ```text
//! Name { depth: 1, suffix: ["P"], lean4_hash: ec950bf51f77e6a0 }
//! ```
//!
//! to say `P`. Measured over the 497-entry 2026-08-25 source-elaboration corpus:
//! 80 of the 320 error entries contained a Debug-printed `Name`, 166
//! occurrences occupying 11,043 characters against ~719 for `Display` — 67
//! characters per name instead of 4 — and **43 of those 80 hit the report's
//! 400-character truncation**, losing their tail to struct punctuation rather
//! than to content. See `crate::error_render`.
//!
//! # What this counts
//!
//! Lines of PRODUCTION code that construct a `TacticError` / `ElabError` /
//! `UnifyResult::Failure` payload while Debug-formatting something. It is a
//! deliberately narrow, syntactic proxy: it cannot know a binding's type, so a
//! line Debug-formatting a `usize` in one of those constructors counts too.
//! That is the correct direction for a shrink-only ratchet — it over-counts,
//! never under-counts, and every accounted line is a line worth reading.
//!
//! # Why this does not use `blank_noncode`
//!
//! CLAUDE.md's source-scan rule says to blank comments AND string literals
//! before matching, because a scanner over raw text counts *mentions* — and in
//! this tree the mentions are the comments that explain a fix, so such a gate
//! moves the WRONG WAY on a genuine repair. That reasoning holds and is obeyed
//! for comments.
//!
//! It cannot be obeyed for string literals here, because **the artifact being
//! counted IS a string literal**: `format!("{e:?}")`. Blanking string literals
//! blanks the evidence — measured, it takes this scanner to zero hits on a tree
//! with fourteen of them.
//!
//! So this blanks comments only, with a string-aware scanner (a `//` inside a
//! literal is not a comment — the exact trap CLAUDE.md names when it forbids
//! `split("//")`). The residual false positive is a string literal that
//! contains a whole error-construction line including a Debug slot; no such
//! line exists in this tree, the arms below pin the comment case, and the
//! failure direction is over-counting, which is the safe one for a shrink-only
//! ratchet.

use std::path::Path;

use crate::test_support::source_scan::{
    blank_noncode, cfg_test_mod_line_ranges, collect_rust_source_files,
    line_is_inside_cfg_test_mod, DEFAULT_PRODUCTION_RULES,
};

/// Blank `//` comments, leaving string literals intact.
///
/// String-aware on purpose: a `//` inside a literal (a URL, a path) is not a
/// comment, and treating it as one truncates the real code after it. That is
/// the trap CLAUDE.md names when it forbids `split("//")`.
fn blank_comments(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut chars = line.char_indices().peekable();
    let mut in_str = false;
    let mut escaped = false;
    while let Some((i, c)) = chars.next() {
        if in_str {
            out.push(c);
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        if c == '"' {
            in_str = true;
            out.push(c);
            continue;
        }
        if c == '/' && matches!(chars.peek(), Some((_, '/'))) {
            let _ = i;
            break;
        }
        out.push(c);
    }
    out
}

/// Debug-formatting sites remaining inside user-facing error construction.
///
/// **Shrink-only.** Lower it when sites move to `crate::error_render`; never
/// raise it. A new error message that needs to show a term has a renderer to
/// use.
///
/// # It is ZERO, and that changes what the number means
///
/// While it was a shrink-only count, a new `{:?}` in an error path was a small
/// increment nobody looked at. At zero it is a rule: any Debug rendering
/// reaching a user-facing error message fails this test.
///
/// Getting here was not a sweep of easy cases. The 95 split three ways and each
/// third needed a different answer:
///
/// * **Kernel terms, levels, names, identifiers, user syntax** — real
///   renderers. `error_render::{term, level, levels, fvar, pattern, lit,
///   shape, kind_name}`. The compiler caught three misclassifications on the
///   way (a `SurfaceExpr` typed as an `Expr`, an `ACExpr`, an `Expr` typed as
///   a `Level`), which is the argument for typed renderers over a blanket
///   `{:?}`.
/// * **`std` containers and internal enums** — `error_render::opaque`, which
///   IS `{:?}` and says so. A `Range<usize>`, a `Vec<usize>` of slot indices, a
///   `Duration`: inventing a `Display` for them would be ceremony. Writing it
///   as a call rather than a format spec makes each one a decision somebody
///   made, greppable, and ratcheted in its own right so the hatch cannot become
///   the norm.
/// * **A false positive** — `derive.rs`'s
///   `format!("{:?}", ctor_name.to_string())` is not a diagnostic at all: it
///   emits an ESCAPED LEAN STRING LITERAL into generated source, and
///   "converting" it would have been a behavioural bug. It counted only because
///   it sat five lines below an unrelated error. `slot_is_inside_call` now
///   requires containment rather than proximity, so the count means what it
///   says.
///
/// An earlier version of this comment asserted the residue was unfixable and
/// told the reader not to try. It was wrong by ~45 sites. If a claim here goes
/// stale, re-derive it — that is the mistake this paragraph exists to record.
///
/// **Never raise this.** A new Debug rendering has a renderer to use, or
/// `opaque` to declare it with.
pub(crate) const ERROR_RENDER_DEBUG_SITE_RATCHET: usize = 0;

/// The error-payload constructors this ratchet watches.
const ERROR_CONSTRUCTORS: &[&str] = &["TacticError::", "ElabError::", "UnifyResult::Failure("];

/// Shapes that MATCH an error rather than construct one.
///
/// Without these the scan counts `matches!(err, TacticError::X { .. })` and
/// every `Err(TacticError::X { .. }) => …` arm — which name a constructor and
/// often Debug-format something nearby, but build no message. Measured: they
/// were the bulk of the raw hits before this filter.
const MATCH_CONTEXTS: &[&str] = &["matches!", ") =>", "if let ", "ref "];

/// How far below a constructor line a Debug slot still belongs to it.
///
/// Error payloads here are built over a handful of lines (`ElabError::X {` /
/// `detail: format!(` / the string / args / `}`).
///
/// This was 5, chosen as "past the longest real one". It was not: `conv.rs:337`
/// sits 6 lines below its owner and `conv.rs:388` sits 8 below, so both were
/// invisible — and the widest variant in the enum, `RewriteNoMatch`, is exactly
/// the shape whose payload overruns a short window. A ratchet that UNDER-counts
/// contradicts its own guarantee below, and under-counts worst on the errors
/// that carry the most. Ten is past every construction measured in this tree.
const CONSTRUCTION_WINDOW: usize = 10;

/// A Debug format specifier: `{:?}`, `{x:?}`, `{x:#?}`.
fn line_has_debug_format(code: &str) -> bool {
    let bytes = code.as_bytes();
    let mut i = 0;
    while let Some(pos) = code[i..].find(":?}") {
        let at = i + pos;
        // Walk back to the opening brace of this format slot; bail if the
        // segment between them looks like anything other than a name/width.
        if let Some(open) = code[..at].rfind('{') {
            let inner = &code[open + 1..at];
            if !inner.contains('}') && inner.len() < 40 {
                return true;
            }
        }
        i = at + 3;
        if i >= bytes.len() {
            break;
        }
    }
    false
}

/// Is the Debug slot on `slot_line` INSIDE the call opened on `owner_line`?
///
/// Proximity is not containment. `derive.rs` has a
/// `let rendered_name = format!("{:?}", ctor_name.to_string())` five lines
/// below an unrelated `InternalInvariant` — and that `{:?}` is not a diagnostic
/// at all: it emits an ESCAPED LEAN STRING LITERAL into generated source, so
/// "fixing" it would be a behavioural bug, not a message improvement. A
/// line-distance heuristic called it a hit.
///
/// Tracking paren depth from the owner line settles it: if the depth returns to
/// zero before the slot line, the owner's call already closed and the slot
/// belongs to a later statement. Quotes are respected so a paren inside a
/// string literal does not move the depth.
fn slot_is_inside_call(lines: &[&str], owner_line: usize, slot_line: usize) -> bool {
    let mut depth: i32 = 0;
    for (n, raw) in lines
        .iter()
        .enumerate()
        .take(slot_line + 1)
        .skip(owner_line)
    {
        let code = blank_comments(raw);
        let mut in_str = false;
        let mut escaped = false;
        for c in code.chars() {
            if in_str {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    in_str = false;
                }
                continue;
            }
            match c {
                '"' => in_str = true,
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
        }
        // Closed before we reached the slot's line: a different statement.
        if depth <= 0 && n < slot_line {
            return false;
        }
    }
    depth > 0
}

fn debug_sites() -> Vec<(String, usize, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let files = collect_rust_source_files(&root, &DEFAULT_PRODUCTION_RULES);
    let mut sites = Vec::new();
    for file in &files {
        // The renderer's own module documents the pattern it replaces, and
        // this file carries planted fixtures of it inside `#[test]` fns —
        // which are NOT inside a `#[cfg(test)] mod`, so the structure filter
        // does not reach them.
        if file.ends_with("error_render.rs") || file.ends_with("tests_error_render_ratchet.rs") {
            continue;
        }
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let rel = file
            .strip_prefix(&root)
            .unwrap_or(file)
            .display()
            .to_string();
        // `production_code_lines` is the sanctioned reader, and it cannot be
        // used here: it returns lines with literal BODIES blanked, which erases
        // exactly what this counts (measured — it takes the scan to zero). So
        // its `#[cfg(test)] mod` detection is reused verbatim, over the blanked
        // text where that detection is correct, and the matching then runs on
        // the RAW line. Line indices agree because `blank_noncode` preserves
        // line structure, which is the same property `production_code_lines`
        // relies on.
        let blanked = blank_noncode(&content);
        let test_mod_ranges = cfg_test_mod_line_ranges(&blanked);
        let all_lines: Vec<&str> = content.lines().collect();
        for (idx, raw) in all_lines.iter().copied().enumerate() {
            if line_is_inside_cfg_test_mod(&test_mod_ranges, idx) {
                continue;
            }
            let line_no = idx + 1;
            // SOURCE-SCAN RULE, adapted: strip comments so a `// … {e:?} …`
            // note is not a hit. String literals are deliberately KEPT — see
            // the module header; the format string is the evidence.
            let code = blank_comments(raw);
            if !line_has_debug_format(&code) {
                continue;
            }
            // Walk BACK to the constructor this slot belongs to. A payload is
            // routinely built across several lines, so the earlier scan — which
            // looked only at the constructor's own line — saw 4 sites where
            // there are 116.
            let start = idx.saturating_sub(CONSTRUCTION_WINDOW);
            let owner = (start..=idx).rev().find(|j| {
                let owner_code = blank_comments(all_lines[*j]);
                ERROR_CONSTRUCTORS.iter().any(|c| owner_code.contains(c))
                    && !MATCH_CONTEXTS.iter().any(|m| owner_code.contains(m))
                    && slot_is_inside_call(&all_lines, *j, idx)
            });
            let Some(owner) = owner else {
                continue;
            };
            // A construction always formats. Requiring it keeps a bare
            // `Err(TacticError::NoGoals)` followed by unrelated Debug code out.
            if (owner..=idx).any(|j| blank_comments(all_lines[j]).contains("format!")) {
                sites.push((rel.clone(), line_no, raw.trim().to_string()));
            }
        }
    }
    sites
}

#[test]
fn error_render_debug_site_ratchet() {
    let sites = debug_sites();
    assert_eq!(
        sites.len(),
        ERROR_RENDER_DEBUG_SITE_RATCHET,
        "error-render ratchet: found {} Debug-formatted sites in user-facing \
         error construction, ratchet allows {}.\n\
         Kernel terms in an error message go through `crate::error_render`, not \
         `{{:?}}` — see that module for the measured cost of not doing so.\n\
         Sites:\n{}",
        sites.len(),
        ERROR_RENDER_DEBUG_SITE_RATCHET,
        sites
            .iter()
            .map(|(p, l, s)| format!("  {p}:{l}: {s}"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

/// The scanner reads CODE, not prose.
///
/// CLAUDE.md's rule exists because a scanner matching raw text counts
/// *mentions* — and in this tree the mentions are the very comments that
/// explain the fix, so such a gate moves the WRONG WAY on a genuine repair.
/// This arm plants a bare comment and a trailing comment behind a string
/// containing `//`, and requires exactly the real construction line to count —
/// so neither prose nor the `split("//")` truncation trap can move the number.
#[test]
fn error_render_scanner_does_not_count_prose_or_string_literals() {
    let planted = r#"
// a comment naming ElabError::TypeMismatch with {expr:?} in it
let url = "https://example.invalid//not-a-comment"; // ElabError::TypeMismatch {x:?}
return Err(ElabError::TypeMismatch { expected: format!("{a:?}"), actual: b });
"#;
    let hits: Vec<_> = planted
        .lines()
        .filter(|raw| {
            let code = blank_comments(raw);
            line_has_debug_format(&code) && ERROR_CONSTRUCTORS.iter().any(|c| code.contains(c))
        })
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "exactly the real construction line must count; got {hits:?}"
    );
    assert!(
        hits[0].contains("return Err"),
        "the counted line must be the real one, got: {hits:?}"
    );
}

/// A plain `{x}` slot is not a Debug site, and a `{:?}` outside an error
/// constructor is not this ratchet's business.
#[test]
fn error_render_scanner_does_not_over_match() {
    assert!(!line_has_debug_format(
        "format!(\"{expected} vs {actual}\")"
    ));
    assert!(line_has_debug_format("format!(\"{e:?}\")"));
    assert!(line_has_debug_format("format!(\"{:?}\", e)"));

    let outside = "eprintln!(\"trace: {expr:?}\");";
    let code = blank_comments(outside);
    assert!(
        line_has_debug_format(&code) && !ERROR_CONSTRUCTORS.iter().any(|c| code.contains(c)),
        "a debug trace is a Debug format but not an error-construction site"
    );
}

/// Declared-opaque renderings: `error_render::opaque` call sites.
///
/// This is the escape hatch's own ratchet. `opaque` IS `{:?}`, so without a
/// second count the first ratchet could be driven to zero by relabelling
/// everything — the number would be true and worthless. Shrink-only: every one
/// of these is a value whose `Debug` was judged its best rendering, and if that
/// judgement is ever wrong for one of them, the fix lowers this.
pub(crate) const OPAQUE_RENDER_SITE_RATCHET: usize = 49;

/// Count `error_render::opaque(` call sites in production code.
fn opaque_sites() -> Vec<(String, usize)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let files = collect_rust_source_files(&root, &DEFAULT_PRODUCTION_RULES);
    let mut sites = Vec::new();
    for file in &files {
        if file.ends_with("error_render.rs") || file.ends_with("tests_error_render_ratchet.rs") {
            continue;
        }
        let content = std::fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("failed to read {}: {}", file.display(), e));
        let rel = file
            .strip_prefix(&root)
            .unwrap_or(file)
            .display()
            .to_string();
        let blanked = blank_noncode(&content);
        let ranges = cfg_test_mod_line_ranges(&blanked);
        for (idx, raw) in content.lines().enumerate() {
            if line_is_inside_cfg_test_mod(&ranges, idx) {
                continue;
            }
            let code = blank_comments(raw);
            let mut from = 0;
            while let Some(at) = code[from..].find("error_render::opaque(") {
                sites.push((rel.clone(), idx + 1));
                from += at + 1;
            }
        }
    }
    sites
}

#[test]
fn opaque_render_site_ratchet() {
    let sites = opaque_sites();
    assert_eq!(
        sites.len(),
        OPAQUE_RENDER_SITE_RATCHET,
        "declared-opaque ratchet: found {} `error_render::opaque` sites, ratchet \
         allows {}.\n\
         `opaque` is `{{:?}}` with a name on it. Growing this is how a zeroed \
         Debug ratchet becomes a lie — reach for a real renderer first.\n\
         Sites:\n{}",
        sites.len(),
        OPAQUE_RENDER_SITE_RATCHET,
        sites
            .iter()
            .map(|(p, l)| format!("  {p}:{l}"))
            .collect::<Vec<_>>()
            .join("\n"),
    );
}
