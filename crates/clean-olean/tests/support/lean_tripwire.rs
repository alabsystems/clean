// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The source tripwire Lean fixtures that must keep Ax0 by construction share
//! (`semr_reference.rs`, `vf5_f1_reference.rs`): what the kernel cannot see —
//! `implemented_by`, `extern` — and what it can, named in the source before a
//! build reaches it. Comments are removed; string and character literals are
//! KEPT (a banned word inside one is reported: fail closed).

use std::collections::BTreeSet;

/// The words the source tripwire refuses in the fixtures' code.
pub const BANNED: [&str; 8] = [
    "native_decide",
    "partial",
    "sorry",
    "implemented_by",
    "extern",
    "axiom",
    "opaque",
    "unsafe",
];

/// Every banned word `text`'s code says, comments removed (string and
/// character literals are KEPT, so a banned word inside one is reported too:
/// fail closed).
pub fn banned_words(text: &str) -> Vec<&'static str> {
    let code = lean_code_only(text);
    let words: BTreeSet<&str> = code
        .split(|ch: char| !(ch.is_alphanumeric() || ch == '_'))
        .collect();
    BANNED.into_iter().filter(|w| words.contains(w)).collect()
}

/// A character that continues a Lean identifier (so a `'` after it is a
/// prime, `x'`, not a character literal).
fn ident_char(ch: char) -> bool {
    ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '!' | '?' | '.')
}

/// The length in chars of the character literal starting at `chars[i]` (a
/// `'`), or `None` when it is not one.
fn char_literal_len(chars: &[char], i: usize) -> Option<usize> {
    match chars.get(i + 1)? {
        '\\' => (i + 3..chars.len().min(i + 14))
            .find(|&j| chars[j] == '\'')
            .map(|j| j - i + 1),
        '\'' | '\n' => None,
        _ => (chars.get(i + 2) == Some(&'\'')).then_some(3),
    }
}

/// `text` with Lean comments (`-- …`, nested `/- … -/`, doc comments among
/// them) removed and everything else kept. The lexer knows what can hide a
/// comment opener or a quote: string literals (with escapes, and with the
/// `{…}` code of an interpolated `s!"…"`, which may hold strings of its own)
/// and character literals (`'"'`, `'\''`). It panics on what it does not
/// model (a raw string `r"…"`, `r#"…"#`) and on a text that ends inside a
/// comment, string or literal, so nothing it misreads can pass: fail closed.
pub fn lean_code_only(text: &str) -> String {
    #[derive(Clone, Copy, PartialEq)]
    enum Mode {
        Code,
        /// In a string; `true` when interpolated (`s!"…"`, `m!"…"`, …).
        Str(bool),
        /// In the `{…}` of an interpolated string, at this brace depth.
        Interp(usize),
    }
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::new();
    let mut stack = vec![Mode::Code];
    let mut i = 0;
    while i < chars.len() {
        let (ch, next) = (chars[i], chars.get(i + 1).copied());
        let prev = if i == 0 { None } else { Some(chars[i - 1]) };
        let mode = *stack.last().expect("a mode");
        match mode {
            Mode::Str(interpolated) => {
                out.push(ch);
                if ch == '\\' {
                    if let Some(n) = next {
                        out.push(n);
                    }
                    i += 2;
                    continue;
                }
                if ch == '"' {
                    stack.pop();
                } else if ch == '{' && interpolated {
                    stack.push(Mode::Interp(0));
                }
                i += 1;
            }
            Mode::Code | Mode::Interp(_) => {
                if ch == '-' && next == Some('-') {
                    while i < chars.len() && chars[i] != '\n' {
                        i += 1;
                    }
                    continue;
                }
                if ch == '/' && next == Some('-') {
                    let mut depth = 1usize;
                    i += 2;
                    while depth > 0 {
                        assert!(i < chars.len(), "the text ends inside a block comment");
                        if chars[i] == '/' && chars.get(i + 1) == Some(&'-') {
                            depth += 1;
                            i += 2;
                        } else if chars[i] == '-' && chars.get(i + 1) == Some(&'/') {
                            depth -= 1;
                            i += 2;
                        } else {
                            i += 1;
                        }
                    }
                    out.push(' ');
                    continue;
                }
                if ch == 'r' && matches!(next, Some('"' | '#')) && !prev.is_some_and(ident_char) {
                    panic!(
                        "a raw string literal at char {i}: the tripwire does not lex raw strings"
                    );
                }
                if ch == '\'' && !prev.is_some_and(ident_char) {
                    if let Some(len) = char_literal_len(&chars, i) {
                        out.extend(&chars[i..i + len]);
                        i += len;
                        continue;
                    }
                }
                out.push(ch);
                if ch == '"' {
                    stack.push(Mode::Str(prev == Some('!')));
                } else if let Mode::Interp(depth) = mode {
                    let top = stack.last_mut().expect("a mode");
                    if ch == '{' {
                        *top = Mode::Interp(depth + 1);
                    } else if ch == '}' {
                        if depth == 0 {
                            stack.pop();
                        } else {
                            *top = Mode::Interp(depth - 1);
                        }
                    }
                }
                i += 1;
            }
        }
    }
    assert!(
        stack == [Mode::Code],
        "the text ends inside a string literal or an interpolation"
    );
    out
}
