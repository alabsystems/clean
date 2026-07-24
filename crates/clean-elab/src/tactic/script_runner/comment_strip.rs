// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean block-comment stripping for tactic scripts and file scanning.
//!
//! Handles nested `/- ... -/` block comments while preserving newline structure
//! so that byte offsets and line numbers remain valid after stripping.

/// Replace all `/- ... -/` block comments (including nested) with spaces,
/// preserving newline characters so line numbers remain stable.
///
/// Line comments (`-- ...`) are NOT stripped here — that's handled separately
/// by `strip_line_comment` in the call sites.
pub fn strip_block_comments(input: &str) -> String {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum State {
        Normal,
        InString { escaped: bool },
        InBlockComment { depth: u32 },
    }

    let mut chars = input.chars().peekable();
    let mut result = String::with_capacity(input.len());
    let mut state = State::Normal;

    while let Some(ch) = chars.next() {
        state = match state {
            State::Normal => {
                if ch == '/' && chars.peek() == Some(&'-') {
                    chars.next();
                    result.push(' ');
                    result.push(' ');
                    State::InBlockComment { depth: 1 }
                } else if ch == '"' {
                    result.push(ch);
                    State::InString { escaped: false }
                } else {
                    result.push(ch);
                    State::Normal
                }
            }
            State::InString { escaped } => {
                result.push(ch);
                if escaped {
                    State::InString { escaped: false }
                } else if ch == '\\' {
                    State::InString { escaped: true }
                } else if ch == '"' {
                    State::Normal
                } else {
                    State::InString { escaped: false }
                }
            }
            State::InBlockComment { depth } => {
                if ch == '/' && chars.peek() == Some(&'-') {
                    chars.next();
                    result.push(' ');
                    result.push(' ');
                    State::InBlockComment { depth: depth + 1 }
                } else if ch == '-' && chars.peek() == Some(&'/') {
                    chars.next();
                    result.push(' ');
                    result.push(' ');
                    if depth == 1 {
                        State::Normal
                    } else {
                        State::InBlockComment { depth: depth - 1 }
                    }
                } else {
                    if ch == '\n' {
                        result.push('\n');
                    } else {
                        for _ in 0..ch.len_utf8() {
                            result.push(' ');
                        }
                    }
                    State::InBlockComment { depth }
                }
            }
        };
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_no_comments() {
        assert_eq!(strip_block_comments("intro h\nexact h"), "intro h\nexact h");
    }

    #[test]
    fn test_strip_inline_block_comment() {
        let input = "intro h /- bind -/ ; exact h";
        let stripped = strip_block_comments(input);
        assert_eq!(input.len(), stripped.len(), "byte length must be preserved");
        assert_eq!(stripped, "intro h            ; exact h");
    }

    #[test]
    fn test_strip_multiline_block_comment() {
        let input = "intro h\n/- this is\na multi-line\ncomment -/\nexact h";
        let stripped = strip_block_comments(input);
        assert!(
            !stripped.contains("/-"),
            "block comment delimiters should be removed"
        );
        assert!(
            !stripped.contains("-/"),
            "block comment delimiters should be removed"
        );
        assert_eq!(
            stripped.lines().count(),
            input.lines().count(),
            "line count must be preserved"
        );
        assert_eq!(input.len(), stripped.len(), "byte length must be preserved");
    }

    #[test]
    fn test_strip_nested_block_comments() {
        let input = "/- outer /- inner -/ still outer -/";
        let stripped = strip_block_comments(input);
        assert_eq!(
            stripped.trim(),
            "",
            "nested block comments should be fully stripped"
        );
        assert_eq!(input.len(), stripped.len());
    }

    #[test]
    fn test_strip_preserves_line_comments() {
        let input = "intro h -- line comment\nexact h";
        let stripped = strip_block_comments(input);
        assert_eq!(stripped, input, "line comments should be unchanged");
    }

    #[test]
    fn test_strip_sorry_after_closed_block_comment() {
        let input = "x /- comment -/ sorry";
        let stripped = strip_block_comments(input);
        assert!(
            stripped.contains("sorry"),
            "sorry after closed block comment should survive: got '{stripped}'"
        );
    }

    #[test]
    fn test_strip_sorry_inside_block_comment_removed() {
        let input = "/- sorry -/";
        let stripped = strip_block_comments(input);
        assert!(
            !stripped.contains("sorry"),
            "sorry inside block comment should be stripped: got '{stripped}'"
        );
    }

    #[test]
    fn test_strip_string_literal_with_balanced_block_comment_markers() {
        let input = "let s := \"/- not a comment -/\"\nsorry";
        let stripped = strip_block_comments(input);
        assert_eq!(
            stripped, input,
            "block-comment markers inside a string literal must be preserved"
        );
    }

    #[test]
    fn test_strip_string_literal_with_unmatched_block_comment_start() {
        let input = "let s := \"/-\"\nsorry";
        let stripped = strip_block_comments(input);
        assert_eq!(
            stripped, input,
            "an unmatched string-literal marker must not hide later holes"
        );
    }

    #[test]
    fn test_strip_multibyte_block_comment_preserves_byte_offsets() {
        let input = "x /- αβ -/ sorry";
        let stripped = strip_block_comments(input);
        assert_eq!(
            stripped.len(),
            input.len(),
            "multibyte comment contents must preserve byte offsets"
        );
        assert!(
            stripped.ends_with(" sorry"),
            "comment stripping must leave following tactics aligned: '{stripped}'"
        );
    }
}
