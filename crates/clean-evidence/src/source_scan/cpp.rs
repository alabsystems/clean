// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Masking and extraction for the pinned C++ inventory.

use regex::Regex;
use std::{ops::Range, sync::LazyLock};

mod arms;
mod constants;
mod functions;
mod headers;

pub use arms::CppCaseArm;
pub use constants::CppConstantUse;
pub use functions::{CppFunction, CppFunctionError};

/// C++ source masked with the incumbent inventory scanner's character rules.
///
/// The mask has the same number of Unicode scalars as the original source.
/// Replacing a non-ASCII scalar with a space changes its UTF-8 byte length.
/// The sparse offset table records those changes without per-byte storage.
pub struct CppSource<'a> {
    raw: &'a str,
    masked: String,
    byte_deltas: Vec<(usize, usize)>,
    line_boundaries: Vec<usize>,
}

impl<'a> CppSource<'a> {
    #[must_use]
    pub fn new(raw: &'a str) -> Self {
        let mut characters: Vec<char> = raw.chars().collect();
        mask_noncode(&mut characters);
        mask_directives(&mut characters);

        let mut masked = String::with_capacity(raw.len());
        let mut byte_deltas = Vec::new();
        for ((at, original), replacement) in raw.char_indices().zip(characters) {
            masked.push(replacement);
            if original.len_utf8() != replacement.len_utf8() {
                byte_deltas.push((masked.len(), at + original.len_utf8() - masked.len()));
            }
        }
        Self {
            raw,
            masked,
            byte_deltas,
            line_boundaries: raw_line_boundaries(raw),
        }
    }

    #[must_use]
    pub fn masked(&self) -> &str {
        &self.masked
    }

    /// Slice the original one-based inclusive line range, keeping terminators.
    /// The boundaries are those of Python's splitlines(keepends=True).
    #[must_use]
    pub fn raw_lines(&self, lo: usize, hi: usize) -> Option<&'a str> {
        if hi < lo {
            return None;
        }
        let &start = self.line_boundaries.get(lo.checked_sub(1)?)?;
        let &end = self.line_boundaries.get(hi)?;
        self.raw.get(start..end)
    }

    /// Map a half-open masked byte range back to the exact original bytes.
    /// Both endpoints must be UTF-8 character boundaries in the mask.
    #[must_use]
    pub fn raw_slice(&self, masked: Range<usize>) -> Option<&'a str> {
        self.masked.get(masked.clone())?;
        self.raw
            .get(self.raw_offset(masked.start)..self.raw_offset(masked.end))
    }

    fn raw_offset(&self, masked: usize) -> usize {
        let count = self.byte_deltas.partition_point(|&(at, _)| at <= masked);
        let delta = count.checked_sub(1).map_or(0, |i| self.byte_deltas[i].1);
        masked + delta
    }
}

fn mask_noncode(code: &mut [char]) {
    let mut offset = 0;
    while offset < code.len() {
        let rest = &mut code[offset..];
        // Comments in the incumbent C++ mask do not nest.
        let consumed = if rest.starts_with(&['/', '/']) {
            let end = rest.iter().position(|&ch| ch == '\n').unwrap_or(rest.len());
            rest[..end].fill(' ');
            end
        } else if rest.starts_with(&['/', '*']) {
            let end = rest[2..]
                .windows(2)
                .position(|pair| pair == ['*', '/'])
                .map_or(rest.len(), |at| at + 4);
            blank_preserving_lf(&mut rest[..end]);
            end
        } else if rest[0] == '"' {
            mask_string(rest)
        } else if let Some(end) = char_literal_end(rest) {
            // The regular expression's escape alternative can span a LF.
            // Unlike comments and strings, it blanks that LF as well.
            rest[1..end - 1].fill(' ');
            end
        } else {
            1
        };
        offset += consumed;
    }
}

fn blank_preserving_lf(text: &mut [char]) {
    for ch in text {
        if *ch != '\n' {
            *ch = ' ';
        }
    }
}

fn mask_string(text: &mut [char]) -> usize {
    let mut end_quote = 1;
    while end_quote < text.len() && text[end_quote] != '"' {
        end_quote += if text[end_quote] == '\\' { 2 } else { 1 };
    }
    let end = (end_quote + 1).min(text.len());
    if end == 1 {
        text[0] = ' ';
    } else {
        blank_preserving_lf(&mut text[1..end - 1]);
        // At EOF the incumbent still puts a quote at the last character.
        text[end - 1] = '"';
    }
    end
}

/// Implements the incumbent local char-literal regex. Its escaped branch
/// consumes one backslash and one non-LF character, then all non-apostrophes.
fn char_literal_end(text: &[char]) -> Option<usize> {
    match text {
        ['\'', '\\', escaped, rest @ ..] if *escaped != '\n' => {
            rest.iter().position(|&ch| ch == '\'').map(|at| at + 4)
        }
        ['\'', ch, '\'', ..] if !matches!(*ch, '\'' | '\\' | '\n') => Some(3),
        _ => None,
    }
}

fn mask_directives(code: &mut [char]) {
    let mut continued = false;
    for line in code.split_mut(|&ch| ch == '\n') {
        let leading = line.iter().find(|&&ch| !python_whitespace(ch));
        if continued || leading == Some(&'#') {
            continued = line.iter().rfind(|&&ch| !python_whitespace(ch)) == Some(&'\\');
            line.fill(' ');
        }
    }
}

fn python_whitespace(ch: char) -> bool {
    ch.is_whitespace() || matches!(ch, '\u{1c}'..='\u{1f}')
}

fn python_word(ch: char) -> bool {
    static WORD_CHAR: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(&format!(r"\A[{}]\z", headers::WORD)).expect("word character pattern")
    });
    if ch.is_ascii() {
        ch.is_ascii_alphanumeric() || ch == '_'
    } else {
        let mut bytes = [0; 4];
        WORD_CHAR.is_match(ch.encode_utf8(&mut bytes))
    }
}

fn raw_line_boundaries(raw: &str) -> Vec<usize> {
    let mut boundaries = vec![0];
    let mut chars = raw.char_indices().peekable();
    while let Some((at, ch)) = chars.next() {
        if ch == '\r' && chars.peek().is_some_and(|&(_, next)| next == '\n') {
            // CRLF is one terminator, counted when LF is visited.
            continue;
        }
        if matches!(
            ch,
            '\n' | '\r'
                | '\x0b'
                | '\x0c'
                | '\x1c'
                | '\x1d'
                | '\x1e'
                | '\u{85}'
                | '\u{2028}'
                | '\u{2029}'
        ) {
            boundaries.push(at + ch.len_utf8());
        }
    }
    if boundaries.last() != Some(&raw.len()) {
        boundaries.push(raw.len());
    }
    boundaries
}

#[cfg(test)]
mod tests {
    use super::CppSource;

    #[test]
    fn comments_are_nonnesting_and_keep_only_lf() {
        let raw = "a/*x/* tail */b*/c //α\r\nz /*a\nα";
        assert_eq!(
            CppSource::new(raw).masked(),
            "a             b*/c     \nz    \n "
        );
    }

    #[test]
    fn literals_match_the_incumbent_escape_and_eof_behavior() {
        for (raw, expected) in [
            ("\"a\\\"bé\" out", "\"     \" out"),
            ("\"α\n", "\" \""),
            ("\"", " "),
            ("\"\\", "\"\""),
            ("'«'", "' '"),
            ("'xy'", "'xy'"),
            ("'\\xray\ny'", "'       '"),
            ("'\\\nq'", "'\\\nq'"),
            ("'\\''", "'  '"),
        ] {
            let source = CppSource::new(raw);
            assert_eq!(source.masked(), expected, "{raw:?}");
            assert_eq!(source.raw_slice(0..expected.len()), Some(raw));
        }
    }

    #[test]
    fn directives_use_python_trim_after_comment_masking() {
        let raw = "\u{1c}\u{2003}#a\\ /*gone*/ \r\nβ\\\u{1f}\nγ\n#b // fake continuation\\\nδ";
        let source = CppSource::new(raw);
        assert_eq!(
            source.masked(),
            "                \n   \n \n                        \nδ"
        );
        assert_eq!(source.raw_slice(0..source.masked().len()), Some(raw));
    }

    #[test]
    fn raw_lines_keep_python_terminators_and_reject_invalid_ranges() {
        let lines = [
            "α\r\n",
            "β\r",
            "γ\n",
            "δ\x0b",
            "ε\x0c",
            "ζ\x1c",
            "η\x1d",
            "θ\x1e",
            "ι\u{85}",
            "κ\u{2028}",
            "λ\u{2029}",
            "μ",
        ];
        let raw = lines.concat();
        let source = CppSource::new(&raw);
        for (index, line) in lines.into_iter().enumerate() {
            assert_eq!(source.raw_lines(index + 1, index + 1), Some(line));
        }
        assert_eq!(source.raw_lines(1, 3), Some("α\r\nβ\rγ\n"));
        assert_eq!(source.raw_lines(1, 12), Some(raw.as_str()));
        assert_eq!(source.raw_lines(0, 1), None);
        assert_eq!(source.raw_lines(4, 3), None);
        assert_eq!(source.raw_lines(12, 13), None);
        assert_eq!(CppSource::new("").raw_lines(1, 1), None);
        let ended = CppSource::new("a\n\n");
        assert_eq!(ended.raw_lines(2, 2), Some("\n"));
        assert_eq!(ended.raw_lines(3, 3), None);
    }

    #[test]
    fn raw_slice_maps_collapsed_scalars_and_checks_masked_boundaries() {
        let raw = "é/*β*/\"μ\"終";
        let source = CppSource::new(raw);
        let masked = source.masked();
        assert_eq!(masked, "é     \" \"終");
        assert_eq!(source.raw_slice(2..7), Some("/*β*/"));
        assert_eq!(source.raw_slice(4..5), Some("β"));
        assert_eq!(source.raw_slice(8..9), Some("μ"));
        assert_eq!(source.raw_slice(10..masked.len()), Some("終"));
        assert_eq!(source.raw_slice(0..masked.len()), Some(raw));
        assert_eq!(source.raw_slice(1..2), None);
        assert_eq!(source.raw_slice(10..11), None);
        assert_eq!(source.raw_slice(0..masked.len() + 1), None);
        assert_eq!(source.raw_slice(masked.len()..masked.len()), Some(""));
        assert_eq!(CppSource::new("\"α\n").raw_slice(2..3), Some("\n"));
    }
}
