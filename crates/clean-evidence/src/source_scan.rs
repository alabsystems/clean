// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source matching for evidence ratchets, promoted from the elaborator's
//! source hygiene checks.
//!
//! The Rust scanner is shared: `clean-elab`'s and
//! `clean-auto`'s `test_support::source_scan` re-export it (design unit EV0),
//! so a ratchet test and an evidence producer cannot read the same file two
//! ways.

use std::ops::RangeInclusive;

pub mod cpp;

/// Return the inclusive 0-indexed line ranges covered by inline `#[cfg(test)] mod` blocks.
///
/// Distinguishes inline test modules from conditional imports such as
/// `#[cfg(test)] use ...` and lets ratchet scanners resume after the test
/// block ends instead of treating the entire file tail as test-only.
///
/// `content` is raw source: it is blanked first ([`blank_noncode`] is
/// idempotent), so a brace inside a string literal or a comment can never move
/// a module boundary, whatever the caller passes.
#[must_use]
pub fn cfg_test_mod_line_ranges(content: &str) -> Vec<RangeInclusive<usize>> {
    blanked_cfg_test_mod_line_ranges(&blank_noncode(content))
}

/// [`cfg_test_mod_line_ranges`] over text that is already blanked.
fn blanked_cfg_test_mod_line_ranges(blanked: &str) -> Vec<RangeInclusive<usize>> {
    // Braces in comments and literals must not hide production lines after a
    // test module or expose lines from inside it.
    let lines: Vec<&str> = blanked.lines().collect();
    let mut ranges = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let Some(mod_line) = cfg_test_mod_declaration_line(&lines, i) else {
            i += 1;
            continue;
        };
        let Some((end_line, has_code_after)) = find_block_end_line(&lines, mod_line) else {
            i += 1;
            continue;
        };
        // Keep a mixed boundary line so a test module cannot hide production
        // code written after its closing brace.
        let end_exclusive = if has_code_after {
            end_line
        } else {
            end_line + 1
        };
        if end_exclusive > i {
            ranges.push(i..=end_exclusive - 1);
        }
        i = end_line + 1;
    }

    ranges
}

/// Check whether a given line index falls inside any `#[cfg(test)] mod` block.
#[must_use]
pub fn line_is_inside_cfg_test_mod(ranges: &[RangeInclusive<usize>], line_idx: usize) -> bool {
    ranges.iter().any(|range| range.contains(&line_idx))
}

fn cfg_test_mod_declaration_line(lines: &[&str], attr_line: usize) -> Option<usize> {
    let rest = lines[attr_line]
        .trim_start()
        .strip_prefix("#[cfg(test)]")?
        .trim_start();
    if is_mod_declaration_line(rest) {
        return Some(attr_line);
    }
    if !rest.is_empty() {
        // This attribute already belongs to something on this line, or the
        // rest of the line is ambiguous. Never claim the next item.
        return None;
    }

    let mut j = attr_line + 1;
    while j < lines.len() {
        let next = lines[j].trim_start();
        if next.is_empty() || is_attribute_only_line(next) || is_comment_preamble_line(next) {
            j += 1;
            continue;
        }
        return is_mod_declaration_line(next).then_some(j);
    }

    None
}

/// Whether a blanked, trimmed line holds only outer attributes (`#[...]`,
/// possibly several). An attribute followed by an item on the same line, or
/// one that does not close on this line, is not: the `#[cfg(test)]` above it
/// then belongs to that item, never to a module further down.
fn is_attribute_only_line(trimmed: &str) -> bool {
    let mut rest = trimmed;
    while let Some(attribute) = rest.strip_prefix('#') {
        let mut depth = 0_usize;
        let mut close = None;
        for (offset, ch) in attribute.char_indices() {
            match ch {
                '[' => depth += 1,
                ']' if depth > 0 => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(offset);
                        break;
                    }
                }
                _ if depth == 0 => return false,
                _ => {}
            }
        }
        let Some(close) = close else {
            return false;
        };
        rest = attribute[close + 1..].trim_start();
        if rest.is_empty() {
            return true;
        }
    }
    false
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

fn find_block_end_line(lines: &[&str], start_line: usize) -> Option<(usize, bool)> {
    let mut depth = 0_i32;
    let mut saw_open = false;

    // `lines` arrives already blanked from `cfg_test_mod_line_ranges`, so
    // comments and literal bodies contribute no braces here.
    for (idx, line) in lines.iter().enumerate().skip(start_line) {
        for (offset, ch) in line.char_indices() {
            match ch {
                ';' if !saw_open => return None,
                '{' => {
                    depth += 1;
                    saw_open = true;
                }
                '}' if saw_open => {
                    depth -= 1;
                    if depth == 0 {
                        return Some((idx, !line[offset + 1..].trim().is_empty()));
                    }
                }
                _ => {}
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Non-code blanking
// ---------------------------------------------------------------------------

/// Blank line comments, nested block comments, and recognized Rust string and
/// character literals. The result keeps every line break and the byte length
/// of the input: each blanked byte becomes one space, and code, non-ASCII
/// text included, is copied through unchanged. This is a source matcher for
/// ratchets, not a Rust parser.
#[must_use]
pub fn blank_noncode(text: &str) -> String {
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
        // raw string: r"..." / r#"..."# / br#"..."# / cr#"..."#
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
        // Code: copy one whole character. Every branch above ends on a
        // character boundary, so a non-ASCII character is copied intact
        // instead of being widened byte by byte into other characters.
        match text.get(i..).and_then(|rest| rest.chars().next()) {
            Some(ch) => {
                out.push(ch);
                i += ch.len_utf8();
            }
            None => {
                out.push(' ');
                i += 1;
            }
        }
    }
    out
}

fn raw_prefix_len(bytes: &[u8], i: usize) -> usize {
    match (bytes.get(i), bytes.get(i + 1)) {
        (Some(b'b' | b'c'), Some(b'r')) => 2,
        (Some(b'r'), _) => 1,
        _ => 0,
    }
}

/// If a raw-string literal (`r`, `br` or `cr` prefix) starts at `i`, return
/// its `#` count.
fn raw_string_open(bytes: &[u8], i: usize) -> Option<usize> {
    let prefix = raw_prefix_len(bytes, i);
    if prefix == 0 {
        return None;
    }
    // The prefix must start a token. An `r` or `c` that ends an identifier
    // (`for`, `xr`, a non-ASCII name), a literal suffix (`1r`) or a lifetime
    // (`'r`) is followed by an ordinary string, which ends at an unescaped
    // quote rather than at a raw string's terminator.
    if let Some(&before) = i.checked_sub(1).and_then(|at| bytes.get(at)) {
        if before.is_ascii_alphanumeric() || matches!(before, b'_' | b'\'') || !before.is_ascii() {
            return None;
        }
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
    let close = match *bytes.get(i + 1)? {
        // Skip the ESCAPE SEQUENCE, then require the closing quote.
        // Scanning forward to the next `'` instead (lane LOOSE, 2026-08-25)
        // mis-lexed `'\\''`: it stopped on the ESCAPED quote and left the
        // real closing quote behind as stray code, which can then open a
        // spurious literal further down the line.
        b'\\' => match *bytes.get(i + 2)? {
            // `\u{...}` holds one to six hex digits before its `}`.
            b'u' => {
                if bytes.get(i + 3) != Some(&b'{') {
                    return None;
                }
                let body = bytes.get(i + 4..)?;
                i + 4 + body.iter().take(7).position(|&byte| byte == b'}')? + 1
            }
            // `\xHH`: the escape letter and exactly two hex digits.
            b'x' => {
                let digits = bytes.get(i + 3..i + 5)?;
                if !digits.iter().all(u8::is_ascii_hexdigit) {
                    return None;
                }
                i + 5
            }
            _ => i + 3,
        },
        b'\'' | b'\n' | b'\r' => return None,
        // One Unicode scalar value, whose UTF-8 length its lead byte gives.
        lead => i + 1 + utf8_sequence_len(lead)?,
    };
    (bytes.get(close) == Some(&b'\'')).then_some(close + 1)
}

/// The byte length of a UTF-8 sequence that starts with `lead`, or `None`
/// for a continuation byte or a byte UTF-8 never uses.
fn utf8_sequence_len(lead: u8) -> Option<usize> {
    match lead {
        0x00..=0x7f => Some(1),
        0xc2..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf4 => Some(4),
        _ => None,
    }
}

/// The production, code-only lines of a Rust file: comments and literal bodies
/// blanked, ordinary inline `#[cfg(test)]` modules dropped. A line that also
/// contains production code is kept in full.
///
/// Returns `(1-indexed line number, code-only line)` so a caller can still
/// report the offending source location.
#[must_use]
pub fn production_code_lines(content: &str) -> Vec<(usize, String)> {
    let blanked = blank_noncode(content);
    let ranges = blanked_cfg_test_mod_line_ranges(&blanked);
    blanked
        .lines()
        .enumerate()
        .filter(|(idx, _)| !line_is_inside_cfg_test_mod(&ranges, *idx))
        .map(|(idx, line)| (idx + 1, line.to_string()))
        .collect()
}

#[cfg(test)]
#[path = "source_scan_tests.rs"]
mod tests;
