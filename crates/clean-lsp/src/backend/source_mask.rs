// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which bytes of a Lean source text are CODE, and which belong to a comment
//! or a string literal.
//!
//! `find_references` — and therefore `documentHighlight`, `prepareRename` and
//! `rename`, all of which are built on it — scans the raw document text for
//! whole-identifier occurrences. With identifier-boundary checks and nothing
//! else, `rename` rewrites the name inside `-- myLemma is the interesting one`
//! and inside `"myLemma"`, which is a silent edit to text the user never
//! meant to touch. This mask is the exclusion those scans were missing.
//!
//! # What it masks, and what it deliberately does not
//!
//! * **Line comments** — `--` to end of line. Lean starts one at `--`
//!   wherever it appears in code, with or without surrounding whitespace.
//! * **Block comments** — `/- … -/`, and they **nest**, so this counts depth
//!   rather than looking for the first `-/`. Lean's doc-comment forms `/-- … -/`
//!   and `/-! … -/` need no special case: both open with `/-`.
//! * **String literals** — `"…"`, with `\` escaping the next byte, so `"a\"b"`
//!   is one string.
//! * **Character literals are NOT masked, and that is deliberate.** `'` is an
//!   identifier-CONTINUE character in this language (`is_identifier_continue`,
//!   `navigation.rs`), so a scanner that treated `'` as a delimiter would read
//!   `h'` as opening a literal and swallow the rest of the file. It also costs
//!   nothing to omit: for the name `a`, the occurrence in `'a'` is bounded by
//!   `'` on both sides, and `'` being identifier-continue means the existing
//!   boundary check already rejects it. Measured by
//!   `char_literal_is_excluded_by_the_identifier_boundary_not_by_this_mask`.
//!
//! # Unterminated regions
//!
//! A file ending inside a comment or a string leaves the remainder masked as
//! non-code. That is the conservative direction for every consumer here: an
//! occurrence that is not returned is a reference the user does not see, while
//! one that is wrongly returned is a *rename that corrupts their file*.
//!
//! # Byte scanning is correct here
//!
//! Every delimiter this looks at — `/`, `-`, `"`, `\`, `\n` — is ASCII, and a
//! UTF-8 continuation byte is always `>= 0x80`, so no multi-byte character can
//! contain one. Scanning bytes therefore cannot cut a character in half or
//! match a delimiter that is not really there.

/// A per-byte code/non-code classification of one document's text.
pub(crate) struct SourceMask {
    code: Vec<bool>,
}

impl SourceMask {
    /// Classify every byte of `text`.
    pub(crate) fn new(text: &str) -> Self {
        let bytes = text.as_bytes();
        let len = bytes.len();
        let mut code = vec![true; len];

        let mut i = 0usize;
        let mut block_depth = 0usize;
        let mut in_string = false;
        let mut in_line_comment = false;

        // Mask `n` bytes starting at `at`, clamped to the text.
        let mask = |code: &mut Vec<bool>, at: usize, n: usize| {
            for slot in code.iter_mut().skip(at).take(n) {
                *slot = false;
            }
        };

        while i < len {
            if block_depth > 0 {
                if bytes[i..].starts_with(b"/-") {
                    block_depth += 1;
                    mask(&mut code, i, 2);
                    i += 2;
                    continue;
                }
                if bytes[i..].starts_with(b"-/") {
                    block_depth -= 1;
                    mask(&mut code, i, 2);
                    i += 2;
                    continue;
                }
                code[i] = false;
                i += 1;
                continue;
            }

            if in_string {
                code[i] = false;
                if bytes[i] == b'\\' {
                    mask(&mut code, i, 2);
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    in_string = false;
                }
                i += 1;
                continue;
            }

            if in_line_comment {
                code[i] = false;
                if bytes[i] == b'\n' {
                    in_line_comment = false;
                }
                i += 1;
                continue;
            }

            if bytes[i..].starts_with(b"/-") {
                block_depth = 1;
                mask(&mut code, i, 2);
                i += 2;
                continue;
            }
            if bytes[i..].starts_with(b"--") {
                in_line_comment = true;
                mask(&mut code, i, 2);
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_string = true;
                code[i] = false;
                i += 1;
                continue;
            }

            i += 1;
        }

        Self { code }
    }

    /// Is every byte of `start..end` code?
    ///
    /// Checks the whole span rather than its first byte: a span that starts in
    /// code and runs into a comment is not a reference either, and the spans
    /// this is asked about are one identifier long.
    pub(crate) fn span_is_code(&self, start: usize, end: usize) -> bool {
        if start >= end || end > self.code.len() {
            return false;
        }
        self.code[start..end].iter().all(|c| *c)
    }
}

#[cfg(test)]
#[path = "source_mask_tests.rs"]
mod tests;
