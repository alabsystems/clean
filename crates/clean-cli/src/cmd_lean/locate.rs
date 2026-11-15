// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Where Lean puts a message, read off the source text.
//!
//! Lean positions a message at a syntax node; Clean's surface declarations
//! carry their byte span, not the span of each token. The positions here are
//! the ones pinned Lean was measured to use (2026-10-16, both releases):
//!
//! - the `declaration uses sorry` warning, and a declaration-level error with
//!   no finer position, sit on the declaration's NAME (`theorem foo.bar`:
//!   `foo.bar`); a declaration with no name (`example`, an unnamed
//!   `instance`) on its keyword;
//! - a command's information message (`#eval`, `#check`, `#print`) on the
//!   command keyword (`#print axioms x` spans `#print`), and a `#guard_msgs`
//!   mismatch on the `#guard_msgs` keyword after the doc comment.
//!
//! The reader skips what Lean's `declModifiers` admits before the keyword:
//! doc and block comments, line comments, `@[…]` attributes and the modifier
//! keywords.

use super::message::Pos;

/// The byte offset of every line start of a source, for `Pos` lookups.
pub(crate) struct LineIndex<'a> {
    source: &'a str,
    starts: Vec<usize>,
}

impl<'a> LineIndex<'a> {
    pub(crate) fn new(source: &'a str) -> Self {
        let mut starts = vec![0];
        starts.extend(
            source
                .bytes()
                .enumerate()
                .filter(|&(_, byte)| byte == b'\n')
                .map(|(at, _)| at + 1),
        );
        Self { source, starts }
    }

    /// Lean's position of byte `offset`: 1-based line, 0-based column in
    /// Unicode scalar values. An offset past the end is the end.
    pub(crate) fn pos(&self, offset: usize) -> Pos {
        let offset = offset.min(self.source.len());
        let line_index = self.starts.partition_point(|&start| start <= offset) - 1;
        let start = self.starts[line_index];
        let column = self
            .source
            .get(start..offset)
            .map_or(0, |text| text.chars().count());
        Pos {
            line: u32::try_from(line_index + 1).unwrap_or(u32::MAX),
            column: u32::try_from(column).unwrap_or(u32::MAX),
        }
    }
}

/// Modifier keywords Lean's `declModifiers` admits before a declaration
/// keyword, plus `local` / `scoped` before `instance` / `notation`.
const MODIFIERS: &[&str] = &[
    "private",
    "protected",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
    "local",
    "scoped",
];

/// Declaration keywords followed by the declaration's name.
const NAMED: &[&str] = &[
    "def",
    "theorem",
    "lemma",
    "abbrev",
    "axiom",
    "opaque",
    "structure",
    "class",
    "inductive",
    "coinductive",
    "instance",
];

/// Skip whitespace and comments starting at `at`.
fn skip_trivia(source: &str, mut at: usize) -> usize {
    loop {
        let rest = &source[at..];
        let trimmed = rest.trim_start();
        at += rest.len() - trimmed.len();
        if trimmed.starts_with("--") {
            at += trimmed.find('\n').unwrap_or(trimmed.len());
        } else if trimmed.starts_with("/-") {
            at = skip_block_comment(source, at);
        } else {
            return at;
        }
    }
}

/// Skip a (nested) `/- … -/` comment starting at `at`.
fn skip_block_comment(source: &str, start: usize) -> usize {
    let bytes = source.as_bytes();
    let mut depth = 0usize;
    let mut at = start;
    while at + 1 < bytes.len() {
        if bytes[at] == b'/' && bytes[at + 1] == b'-' {
            depth += 1;
            at += 2;
        } else if bytes[at] == b'-' && bytes[at + 1] == b'/' {
            depth = depth.saturating_sub(1);
            at += 2;
            if depth == 0 {
                return at;
            }
        } else {
            at += 1;
        }
    }
    source.len()
}

/// Skip a bracketed group (`@[…]`, `(priority := …)`) starting at its opener.
fn skip_group(source: &str, start: usize, open: char, close: char) -> usize {
    let mut depth = 0usize;
    for (offset, ch) in source[start..].char_indices() {
        if ch == open {
            depth += 1;
        } else if ch == close {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return start + offset + ch.len_utf8();
            }
        }
    }
    source.len()
}

fn is_token_char(ch: char) -> bool {
    !ch.is_whitespace() && !"()[]{}⦃⦄⟨⟩:,=|@".contains(ch)
}

/// The identifier-ish token starting at `at`: a `«…»` name is one token.
fn token_end(source: &str, at: usize) -> usize {
    let mut end = at;
    let mut in_guillemets = false;
    for (offset, ch) in source[at..].char_indices() {
        if ch == '«' {
            in_guillemets = true;
        } else if ch == '»' {
            in_guillemets = false;
        } else if !in_guillemets && !is_token_char(ch) {
            break;
        }
        end = at + offset + ch.len_utf8();
    }
    end
}

/// The byte range of a declaration's reference token, scanning from the start
/// of its span: its name, or its keyword when it has none.
pub(crate) fn decl_ref_range(source: &str, span_start: usize) -> (usize, usize) {
    let mut at = skip_trivia(source, span_start.min(source.len()));
    loop {
        if source[at..].starts_with("@[") {
            at = skip_trivia(source, skip_group(source, at + 1, '[', ']'));
            continue;
        }
        let end = token_end(source, at);
        let word = &source[at..end];
        if MODIFIERS.contains(&word) {
            at = skip_trivia(source, end);
            continue;
        }
        if word == "class" {
            // `class inductive Foo`.
            let next = skip_trivia(source, end);
            if source[next..].starts_with("inductive") {
                return name_after(source, next, next + "inductive".len());
            }
        }
        if NAMED.contains(&word) {
            return name_after(source, at, end);
        }
        return (at, end.max(at));
    }
}

/// The name following the keyword at `keyword..keyword_end`, or the keyword.
fn name_after(source: &str, keyword: usize, keyword_end: usize) -> (usize, usize) {
    let mut at = skip_trivia(source, keyword_end);
    if source[keyword..keyword_end].starts_with("instance") && source[at..].starts_with('(') {
        // `instance (priority := low) foo`.
        at = skip_trivia(source, skip_group(source, at, '(', ')'));
    }
    let end = token_end(source, at);
    let word = &source[at..end];
    if end == at || word == "where" || word == "extends" {
        (keyword, keyword_end)
    } else {
        (at, end)
    }
}

/// Where an auxiliary declaration of a `where` / `let rec` clause is named
/// inside the declaration spanning `start..end`: the first whole-token
/// occurrence of `short` (its last name component) after the clause keyword.
/// Lean logs such a declaration's messages there (measured: the `sorry` in
/// `def foo … where bar … := sorry` is warned at `bar`).
pub(crate) fn aux_name_start(source: &str, start: usize, end: usize, short: &str) -> Option<usize> {
    let text = source.get(start..end.min(source.len()))?;
    let clause = ["where", "let rec"]
        .iter()
        .filter_map(|keyword| find_token(text, keyword, 0))
        .min()?;
    find_token(text, short, clause).map(|at| start + at)
}

/// The first occurrence of `word` in `text` at or after `from` that is a whole
/// token (not part of a longer identifier).
fn find_token(text: &str, word: &str, from: usize) -> Option<usize> {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'' || c == '.';
    let mut at = from;
    while let Some(found) = text.get(at..)?.find(word) {
        let begin = at + found;
        let after = begin + word.len();
        let before_ok = text[..begin]
            .chars()
            .next_back()
            .is_none_or(|c| !is_ident(c));
        let after_ok = text[after..].chars().next().is_none_or(|c| !is_ident(c));
        if before_ok && after_ok {
            return Some(begin);
        }
        at = after;
    }
    None
}

/// The byte range of a command keyword (`#eval`, `#check`, `#guard_msgs` …)
/// at or after `span_start`, past any doc comment.
pub(crate) fn command_keyword_range(source: &str, span_start: usize) -> (usize, usize) {
    let at = skip_trivia(source, span_start.min(source.len()));
    let rest = &source[at..];
    let len = rest
        .char_indices()
        .skip(1)
        .find(|&(_, ch)| !(ch.is_alphanumeric() || ch == '_'))
        .map_or(rest.len(), |(offset, _)| offset);
    (at, at + len)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name_of(source: &str) -> &str {
        let (start, end) = decl_ref_range(source, 0);
        &source[start..end]
    }

    #[test]
    fn test_pos_counts_columns_in_characters() {
        let source = "αβ x\ny";
        let index = LineIndex::new(source);
        assert_eq!(index.pos(0), Pos { line: 1, column: 0 });
        assert_eq!(index.pos("αβ ".len()), Pos { line: 1, column: 3 });
        assert_eq!(index.pos(source.len()), Pos { line: 2, column: 1 });
    }

    #[test]
    fn test_decl_ref_is_the_name_lean_reports() {
        // The positions pinned Lean's `declaration uses 'sorry'` used.
        assert_eq!(name_of("theorem foo.bar : True := sorry"), "foo.bar");
        assert_eq!(name_of("  private theorem p : True := sorry"), "p");
        assert_eq!(name_of("@[simp] theorem s : True := sorry"), "s");
        assert_eq!(name_of("/-- doc -/\ntheorem d : True := by sorry"), "d");
        assert_eq!(name_of("example : True := sorry"), "example");
        assert_eq!(name_of("instance : Inhabited Nat := sorry"), "instance");
        assert_eq!(name_of("instance (priority := low) foo : X := y"), "foo");
        assert_eq!(name_of("class inductive C : Prop"), "C");
        assert_eq!(name_of("def «weird name» : Nat := 1"), "«weird name»");
    }

    #[test]
    fn test_aux_name_is_found_after_its_clause() {
        let source = "def foo: Unit := ()\nwhere\n  bar: Unit := sorry\n";
        let at = aux_name_start(source, 0, source.len(), "bar").expect("found");
        assert_eq!(&source[at..at + 3], "bar");
        assert_eq!(aux_name_start(source, 0, source.len(), "ba"), None);
        assert_eq!(aux_name_start("def x := 1", 0, 10, "x"), None);
    }

    #[test]
    fn test_command_keyword_range() {
        let source = "/-- info: 2 -/\n#guard_msgs in\n#eval 1";
        let (start, end) = command_keyword_range(source, 0);
        assert_eq!(&source[start..end], "#guard_msgs");
        let source = "#print axioms x";
        let (start, end) = command_keyword_range(source, 0);
        assert_eq!(&source[start..end], "#print");
    }
}
