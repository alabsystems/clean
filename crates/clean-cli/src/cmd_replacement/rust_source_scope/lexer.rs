// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The lexical layer of the module-tree classification: the Python sibling's
//! `NONCODE_RE` and the edge extractors that read the text it leaves.
//!
//! Every blanking here is BYTE-length-preserving, so the comment-blanked text,
//! the fully blanked text and the raw source share every offset; a span always
//! starts and ends on an ASCII delimiter, so blanking whole spans keeps UTF-8.

use super::cfg_body_is_test_only;

/// Is `c` a regex word character (`\w`, Unicode)?
fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// `\b` immediately before byte `at`.
fn word_start(src: &str, at: usize) -> bool {
    src[..at].chars().next_back().is_none_or(|c| !is_word(c))
}

/// `\b` at byte `at`, from the other side: the word ends at `at`.
fn word_end(src: &str, at: usize) -> bool {
    src[at..].chars().next().is_none_or(|c| !is_word(c))
}

/// The UTF-8 length of the char starting at byte `at`.
fn char_len(src: &str, at: usize) -> usize {
    src[at..].chars().next().map_or(1, char::len_utf8)
}

/// The end of the block comment opening at `at`: rustc NESTS block comments,
/// so leftmost `/*` and `*/` tokens are counted to the balanced close (`/*/`
/// opens, `*/*` closes). An unterminated comment, which rustc refuses, runs to
/// the end of the text, as in the Python sibling's `_NestingLexer`.
fn block_comment_end(b: &[u8], at: usize) -> usize {
    let (mut depth, mut i) = (0usize, at);
    while i + 1 < b.len() {
        match (b[i], b[i + 1]) {
            (b'/', b'*') => {
                depth += 1;
                i += 2;
            }
            (b'*', b'/') => {
                depth = depth.saturating_sub(1);
                i += 2;
                if depth == 0 {
                    return i;
                }
            }
            _ => i += 1,
        }
    }
    b.len()
}

/// The end of a `\u{..}` escape whose `u` is at `u`: one to six hex digits,
/// the first leading, underscores anywhere after it
/// (`u\{[0-9A-Fa-f](?:_*[0-9A-Fa-f]){0,5}_*\}`).
fn unicode_escape_end(b: &[u8], u: usize) -> Option<usize> {
    if b.get(u + 1) != Some(&b'{') || !b.get(u + 2).is_some_and(u8::is_ascii_hexdigit) {
        return None;
    }
    let body = b[u + 2..]
        .iter()
        .take_while(|c| c.is_ascii_hexdigit() || **c == b'_')
        .count();
    let digits = b[u + 2..u + 2 + body]
        .iter()
        .filter(|c| c.is_ascii_hexdigit())
        .count();
    (digits <= 6 && b.get(u + 2 + body) == Some(&b'}')).then_some(u + 3 + body)
}

/// `[at, end)` of the one `NONCODE_RE` alternative that matches at `at`, and
/// whether it is a comment. The alternatives, in the Python order (the shared
/// lexer block of `scripts/check_add_decl_ratchet.py`): a NESTING block
/// comment, `//[^\n]*`, `(?<![A-Za-z0-9_'])[bc]?r(#*)"(?:.|\n)*?"\1`,
/// `b?"(?:\\.|[^"\\])*"`, and a char literal reading the `\x..` and `\u{..}`
/// escapes rustc accepts. Each begins with a distinct ASCII prefix, so the
/// first that matches is the only one that can.
fn noncode_at(src: &str, at: usize) -> Option<(usize, bool)> {
    let b = src.as_bytes();
    let byte = |i: usize| b.get(i).copied();
    match byte(at)? {
        b'/' if byte(at + 1) == Some(b'*') => {
            return Some((block_comment_end(b, at), true));
        }
        b'/' if byte(at + 1) == Some(b'/') => {
            let end = src[at..].find('\n').map_or(b.len(), |p| at + p);
            return Some((end, true));
        }
        _ => {}
    }
    // raw string, which needs a token boundary before its prefix: to rustc
    // `1r"x"`, `'r"x"` and `xr"x"` are a token followed by an ordinary string.
    let boundary =
        at == 0 || !matches!(b[at - 1], b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'\'');
    let mut j = at;
    if matches!(byte(j), Some(b'b' | b'c')) {
        j += 1;
    }
    if boundary && byte(j) == Some(b'r') {
        j += 1;
        let hashes = b[j..].iter().take_while(|&&c| c == b'#').count();
        j += hashes;
        if byte(j) == Some(b'"') {
            let mut k = j + 1;
            while k < b.len() {
                if b[k] == b'"'
                    && b[k + 1..]
                        .iter()
                        .take(hashes)
                        .filter(|&&c| c == b'#')
                        .count()
                        == hashes
                {
                    return Some((k + 1 + hashes, false));
                }
                k += 1;
            }
        }
    }
    // string: b?"(?:\\.|[^"\\])*"
    let mut j = at;
    if byte(j) == Some(b'b') {
        j += 1;
    }
    if byte(j) == Some(b'"') {
        j += 1;
        while j < b.len() {
            match b[j] {
                b'\\' if j + 1 < b.len() => j += 1 + char_len(src, j + 1),
                b'\\' => return None,
                b'"' => return Some((j + 1, false)),
                _ => j += 1,
            }
        }
        return None;
    }
    // char: '(?:\\(?:x[0-9A-Fa-f]{2}|u\{..\}|.)|[^\\'])', each escape form
    // tried in the pattern's order, as its backtracking does.
    if byte(at) == Some(b'\'') {
        let j = at + 1;
        let ends: Vec<usize> = match byte(j)? {
            b'\\' if j + 1 < b.len() => {
                let hex2 = byte(j + 1) == Some(b'x')
                    && byte(j + 2).is_some_and(|c| c.is_ascii_hexdigit())
                    && byte(j + 3).is_some_and(|c| c.is_ascii_hexdigit());
                let unicode = if byte(j + 1) == Some(b'u') {
                    unicode_escape_end(b, j + 1)
                } else {
                    None
                };
                hex2.then_some(j + 4)
                    .into_iter()
                    .chain(unicode)
                    .chain(std::iter::once(j + 1 + char_len(src, j + 1)))
                    .collect()
            }
            b'\\' | b'\'' => return None,
            _ => vec![j + char_len(src, j)],
        };
        if let Some(k) = ends.into_iter().find(|&k| byte(k) == Some(b'\'')) {
            return Some((k + 1, false));
        }
    }
    None
}

/// Every non-code span, leftmost first, as `re.sub(NONCODE_RE, ..)` visits them.
fn noncode_spans(src: &str) -> Vec<(usize, usize, bool)> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < src.len() {
        match noncode_at(src, i) {
            Some((end, comment)) => {
                out.push((i, end, comment));
                i = end;
            }
            None => i += 1,
        }
    }
    out
}

/// (comments blanked, literals kept; comments AND literals blanked): the
/// Python sibling's `strip_comments_keep_strings` and `strip_noncode`.
pub(crate) fn blank_both(src: &str) -> (String, String) {
    let mut keep = src.as_bytes().to_vec();
    let mut full = keep.clone();
    for (start, end, comment) in noncode_spans(src) {
        for at in start..end {
            if full[at] != b'\n' {
                full[at] = b' ';
                if comment {
                    keep[at] = b' ';
                }
            }
        }
    }
    (
        String::from_utf8_lossy(&keep).into_owned(),
        String::from_utf8_lossy(&full).into_owned(),
    )
}

/// `mod NAME;` declarations in code-only text, as (offset of the line start,
/// name): `^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+([A-Za-z0-9_]+)[ \t]*;`.
pub(crate) fn mod_declarations(code: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    for line in code.split_inclusive('\n') {
        let mut rest = line.trim_start_matches([' ', '\t']);
        if let Some(after) = rest.strip_prefix("pub") {
            let after = match after
                .strip_prefix('(')
                .and_then(|a| a.find(')').map(|c| &a[c + 1..]))
            {
                Some(closed) => closed,
                None => after,
            };
            if after.starts_with([' ', '\t']) {
                rest = after.trim_start_matches([' ', '\t']);
            }
        }
        if let Some(after) = rest.strip_prefix("mod") {
            if after.starts_with([' ', '\t']) {
                let after = after.trim_start_matches([' ', '\t']);
                let name_len = after
                    .bytes()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == b'_')
                    .count();
                if name_len > 0
                    && after[name_len..]
                        .trim_start_matches([' ', '\t'])
                        .starts_with(';')
                {
                    out.push((offset, after[..name_len].to_string()));
                }
            }
        }
        offset += line.len();
    }
    out
}

/// The text between the delimiter at `open` and its match (`_balanced`).
fn balanced(src: &str, open: usize, opener: u8, closer: u8) -> Option<&str> {
    let b = src.as_bytes();
    if b.get(open) != Some(&opener) {
        return None;
    }
    let mut depth = 0usize;
    for (i, &c) in b.iter().enumerate().skip(open) {
        if c == opener {
            depth += 1;
        } else if c == closer {
            depth -= 1;
            if depth == 0 {
                return Some(&src[open + 1..i]);
            }
        }
    }
    None
}

/// The body of a `"..."` starting at `at` (`"((?:[^"\\]|\\.)*)"`, `.` not a
/// newline), and the offset just past it.
fn string_literal_at(src: &str, at: usize) -> Option<(&str, usize)> {
    let b = src.as_bytes();
    if b.get(at) != Some(&b'"') {
        return None;
    }
    let mut j = at + 1;
    while j < b.len() {
        match b[j] {
            b'\\' if b.get(j + 1).is_some_and(|&c| c != b'\n') => j += 1 + char_len(src, j + 1),
            b'\\' => return None,
            b'"' => return Some((&src[at + 1..j], j + 1)),
            _ => j += 1,
        }
    }
    None
}

/// Every string literal's body, as `_STRLIT_RE.findall` finds them.
fn string_literals(src: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(rel) = src[i..].find('"') {
        let at = i + rel;
        match string_literal_at(src, at) {
            Some((body, end)) => {
                out.push(body);
                i = end;
            }
            None => i = at + 1,
        }
    }
    out
}

/// `src[at..]` past any whitespace (`\s*`).
fn skip_ws(src: &str, at: usize) -> usize {
    at + (src[at..].len() - src[at..].trim_start().len())
}

/// The offset just past `\b<word>\s*<punct>` for every occurrence, in order.
fn keyword_then(src: &str, word: &str, punct: u8) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut from = 0usize;
    while let Some(rel) = src[from..].find(word) {
        let at = from + rel;
        from = at + 1;
        if !word_start(src, at) {
            continue;
        }
        let j = skip_ws(src, at + word.len());
        if src.as_bytes().get(j) == Some(&punct) {
            out.push((at, j));
            from = j + 1;
        }
    }
    out
}

/// `\bpath\s*=\s*"((?:[^"\\]|\\.)*)"`, first match.
fn path_value(attr: &str) -> Option<&str> {
    keyword_then(attr, "path", b'=')
        .into_iter()
        .find_map(|(_, eq)| string_literal_at(attr, skip_ws(attr, eq + 1)).map(|(body, _)| body))
}

/// (offset, text) of every bracket-matched `#[...]` / `#![...]` (`_attr_spans`).
fn attr_spans(src: &str) -> Vec<(usize, &str)> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(rel) = src[i..].find('#') {
        let j = i + rel;
        let mut k = j + 1;
        if b.get(k) == Some(&b'!') {
            k += 1;
        }
        if b.get(k) != Some(&b'[') {
            i = j + 1;
            continue;
        }
        let Some(body) = balanced(src, k, b'[', b']') else {
            return out;
        };
        let end = k + body.len() + 2;
        out.push((j, &src[j..end]));
        i = end;
    }
    out
}

/// (offset, target, the attribute's own `cfg_attr` condition is test-only)
/// for every attribute naming a module path (`_path_edges`).
pub(crate) fn path_edges(src: &str) -> Vec<(usize, String, bool)> {
    let mut out = Vec::new();
    for (offset, text) in attr_spans(src) {
        if !text.contains("path") {
            continue;
        }
        let cond_test_only = keyword_then(text, "cfg_attr", b'(')
            .first()
            .and_then(|&(_, open)| balanced(text, open, b'(', b')'))
            .and_then(|body| {
                super::split_top(body)
                    .first()
                    .map(|c| cfg_body_is_test_only(c))
            })
            .unwrap_or(false);
        if let Some(target) = path_value(text) {
            out.push((offset, target.to_string(), cond_test_only));
            continue;
        }
        // An attribute that MENTIONS `path` but whose target cannot be read:
        // every path-shaped literal in it is a production edge.
        out.extend(
            string_literals(text)
                .into_iter()
                .filter(|lit| lit.ends_with(".rs"))
                .map(|lit| (offset, lit.to_string(), false)),
        );
    }
    out
}

/// (offset, target) for every `include!` module edge (`_include_edges`): a
/// bare literal, else the concatenation and each `.rs` literal.
pub(crate) fn include_edges(src: &str) -> Vec<(usize, String)> {
    let mut out = Vec::new();
    for (at, open) in keyword_then(src, "include!", b'(') {
        let Some(body) = balanced(src, open, b'(', b')') else {
            continue;
        };
        let lits = string_literals(body);
        let bare = body
            .trim()
            .strip_prefix('"')
            .and_then(|s| s.strip_suffix('"'));
        if lits.len() == 1 && bare == Some(lits[0]) {
            out.push((at, lits[0].to_string()));
            continue;
        }
        let joined: String = lits.concat();
        out.extend(
            std::iter::once(joined.as_str())
                .chain(lits.iter().copied())
                .filter(|c| c.ends_with(".rs"))
                .map(|c| (at, c.to_string())),
        );
    }
    out
}

/// `[ \t\r]*#!\[[ \t]*cfg[ \t]*\([ \t]*test[ \t]*\)[ \t]*\][ \t\r]*`, the whole line.
fn is_head_cfg_test(line: &str) -> bool {
    const TABS: [char; 2] = [' ', '\t'];
    const ENDS: [char; 3] = [' ', '\t', '\r'];
    let tokens = ["cfg", "(", "test", ")", "]"];
    let Some(mut rest) = line.trim_start_matches(ENDS).strip_prefix("#![") else {
        return false;
    };
    for token in tokens {
        match rest.trim_start_matches(TABS).strip_prefix(token) {
            Some(after) => rest = after,
            None => return false,
        }
    }
    rest.trim_start_matches(ENDS).is_empty()
}

/// Is the file's first line that is not blank or a `//` comment exactly
/// `#![cfg(test)]` (the Python sibling's `headed_cfg_test`)? Read on the raw
/// text; a block comment or another inner attribute first answers no, the
/// direction that keeps the file scanned.
pub(crate) fn headed_cfg_test(text: &str) -> bool {
    for line in text.split('\n') {
        if is_head_cfg_test(line) {
            return true;
        }
        let rest = line.trim_start_matches([' ', '\t', '\r']);
        if !(rest.is_empty() || rest.starts_with("//")) {
            return false;
        }
    }
    false
}

/// Does the source hold the word `mod` (`\bmod\b`), `path` or `include!`?
/// Blanking only turns characters into spaces, so a file without any of them
/// declares no module edge.
pub(crate) fn may_declare_modules(raw: &str) -> bool {
    raw.contains("path")
        || raw.contains("include!")
        || raw
            .match_indices("mod")
            .any(|(at, _)| word_start(raw, at) && word_end(raw, at + 3))
}
