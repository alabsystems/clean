// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The ONE Rust-source lexer in `clean-auto`, for the ratchets and hygiene
//! gates in this crate that read `.rs` files and count call sites.
//!
//! WHY IT IS NOT SHARED WITH `clean-elab`. The canonical copy is
//! `blank_noncode` in `crates/clean-elab/src/test_support/source_scan.rs`.
//! `clean-elab` DEPENDS on `clean-auto` (crates/clean-elab/Cargo.toml), so a
//! `clean-auto` dev-dependency on `clean-elab` is a dependency cycle, and the
//! helper is `pub(crate)` besides. One copy per crate is the language
//! constraint; keep the two in step.
//!
//! WHY IT EXISTS AT ALL (lane LOOSE, 2026-08-25). Two ratchets in this crate
//! decided a soundness question from RAW SOURCE TEXT:
//!
//! * `tests/expr_let_constructor_hygiene.rs` kept
//!   `line.split("//").next()` and matched the remainder;
//! * `src/bridge/ay_backend/proof_reconstruct/tests_boundary.rs` skipped only
//!   lines whose `trim()` STARTS with `//`, then counted patterns on the RAW
//!   line -- so a TRAILING comment naming a forbidden type counted, against a
//!   baseline of literal 0.
//!
//! Both are wrong in two directions. They count PROSE -- and in this tree the
//! prose is the `// SOUNDNESS:`-style note explaining why the forbidden thing
//! is not being done, so the cheapest green is to delete the explanation. And
//! `split("//")` also TRUNCATES the line at the first `//` anywhere, string
//! literals included, so a real call after `let u = "http://host";` was never
//! scanned. Measured over-count in production scope at HEAD: 0 for both --
//! which is the wrong direction to be dangerous, and says nothing at all about
//! the silent direction.
//!
//! The integration test in `tests/` reaches this file through
//! `#[path = "../src/test_support/source_scan.rs"]`: an integration test is a
//! separate crate and cannot see `pub(crate)` items, and a second copy of the
//! lexer is exactly what this module exists to prevent. For the same reason
//! `clean-cli`'s `clean check` census (`crates/clean-cli/src/cmd_core_driver_tests.rs`)
//! includes this file by path, so it must stay self-contained: `std` only, no
//! `crate::` paths.

/// Blank every non-code byte of `text`, preserving line geometry.
///
/// A character state machine, not a Rust parser: line comments, NESTING block
/// comments, strings with escapes, raw strings with hash delimiters, byte
/// strings, and char literals distinguished from lifetimes. Every blanked byte
/// becomes a space, and every newline is kept, so 1-indexed line numbers in the
/// output are the line numbers of the input.
#[allow(dead_code)]
pub(crate) fn blank_noncode(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0usize;
    let push_blank = |out: &mut String, from: usize, to: usize| {
        for &b in &bytes[from..to] {
            out.push(if b == b'\n' { '\n' } else { ' ' });
        }
    };
    while i < bytes.len() {
        let b = bytes[i];
        // line comment (covers `//`, `///`, `//!`)
        if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            let mut j = i;
            while j < bytes.len() && bytes[j] != b'\n' {
                j += 1;
            }
            push_blank(&mut out, i, j);
            i = j;
            continue;
        }
        // block comment — Rust block comments nest
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
            let end = j.min(bytes.len());
            push_blank(&mut out, i, end);
            i = end;
            continue;
        }
        // raw string: r"..." / r#"..."# / br##"..."##
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
        // char literal, distinguished from a lifetime (`'a`, `'static`)
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

#[allow(dead_code)]
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
#[allow(dead_code)]
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

/// If a char literal starts at `i`, return the index one past its closing
/// quote. `'a` / `'static` (lifetimes) and `'a: loop` (labels) return `None`.
#[allow(dead_code)]
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

#[cfg(test)]
mod arms {
    use super::*;

    /// DIRECTION 1: comments and literal bodies that merely NAME a forbidden
    /// call must not survive blanking.
    #[test]
    fn blank_noncode_erases_comments_and_literals() {
        let src = concat!(
            "// SOUNDNESS: never call forbidden(\n",
            "/// doc naming forbidden(\n",
            "/* block naming forbidden( and /* nested forbidden( */ */\n",
            "fn ok() { let s = \"forbidden(\"; let _ = s; }\n",
        );
        let blanked = blank_noncode(src);
        assert!(
            !blanked.contains("forbidden("),
            "prose and literals must be blanked: {blanked:?}"
        );
        assert_eq!(blanked.lines().count(), src.lines().count());
    }

    /// DIRECTION 2: real code survives, including after a string that contains
    /// `//` -- the case `split("//")` truncated away entirely.
    #[test]
    fn blank_noncode_keeps_code_after_a_string_containing_slashes() {
        let src = "let u = \"https://example.invalid\"; forbidden(x);\n";
        let blanked = blank_noncode(src);
        assert!(
            blanked.contains("forbidden(x);"),
            "a real call after a string containing `//` must survive: {blanked:?}"
        );
        assert!(
            !blanked.contains("https"),
            "the string body must be blanked"
        );
    }

    /// An escaped char literal is blanked WHOLE; a lifetime is not a literal.
    #[test]
    fn blank_noncode_handles_escapes_and_lifetimes() {
        let src = "fn f<'a>(s: &'a str) { let c = '\\''; let _ = (s, c); }\n";
        let blanked = blank_noncode(src);
        assert!(
            blanked.contains("fn f<'a>(s: &'a str)"),
            "lifetimes must survive: {blanked:?}"
        );
        assert!(
            !blanked.contains("'\\'"),
            "the escaped char literal must be blanked whole: {blanked:?}"
        );
    }
}
