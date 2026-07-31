// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal fail-closed Rust tokenization used by the sorry-bypass lint.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RustTokenKind<'a> {
    Ident(&'a str),
    StringLiteral(&'a str),
    Punct(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RustToken<'a> {
    kind: RustTokenKind<'a>,
    pub(super) start: usize,
    end: usize,
}

impl RustToken<'_> {
    pub(super) fn is_ident(self, expected: &str) -> bool {
        matches!(self.kind, RustTokenKind::Ident(actual) if actual == expected)
    }

    pub(super) fn is_punct(self, expected: u8) -> bool {
        self.kind == RustTokenKind::Punct(expected)
    }

    pub(super) fn is_sorry_string(self) -> bool {
        matches!(self.kind, RustTokenKind::StringLiteral(literal) if literal_value_is_sorry(literal))
    }
}

pub(super) fn cfg_test_item_ranges(tokens: &[RustToken<'_>]) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut index = 0;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    while index < tokens.len() {
        if paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 {
            if let Some(after_cfg) = exact_cfg_test_attribute_end(tokens, index) {
                let mut item_start = after_cfg;
                while let Some(after_attribute) = attribute_end(tokens, item_start) {
                    item_start = after_attribute;
                }
                item_start = skip_item_prefixes(tokens, item_start);
                if is_supported_item_start(tokens.get(item_start).copied()) {
                    if let Some(end) = conservative_item_end(tokens, item_start) {
                        ranges.push((tokens[index].start, end));
                    }
                }
                index = after_cfg;
                continue;
            }
        }
        let token = tokens[index];
        if token.is_punct(b'(') {
            paren_depth = paren_depth.saturating_add(1);
        } else if token.is_punct(b')') {
            paren_depth = paren_depth.saturating_sub(1);
        } else if token.is_punct(b'[') {
            bracket_depth = bracket_depth.saturating_add(1);
        } else if token.is_punct(b']') {
            bracket_depth = bracket_depth.saturating_sub(1);
        } else if token.is_punct(b'{') {
            brace_depth = brace_depth.saturating_add(1);
        } else if token.is_punct(b'}') {
            brace_depth = brace_depth.saturating_sub(1);
        }
        index += 1;
    }
    ranges
}

fn exact_cfg_test_attribute_end(tokens: &[RustToken<'_>], index: usize) -> Option<usize> {
    let expected = [
        RustTokenKind::Punct(b'#'),
        RustTokenKind::Punct(b'['),
        RustTokenKind::Ident("cfg"),
        RustTokenKind::Punct(b'('),
        RustTokenKind::Ident("test"),
        RustTokenKind::Punct(b')'),
        RustTokenKind::Punct(b']'),
    ];
    let actual = tokens.get(index..index + expected.len())?;
    actual
        .iter()
        .zip(expected)
        .all(|(token, kind)| token.kind == kind)
        .then_some(index + expected.len())
}

fn attribute_end(tokens: &[RustToken<'_>], index: usize) -> Option<usize> {
    if !tokens.get(index).copied()?.is_punct(b'#')
        || !tokens.get(index + 1).copied()?.is_punct(b'[')
    {
        return None;
    }
    balanced_delimiter_end(tokens, index + 1, b'[', b']')
}

fn skip_item_prefixes(tokens: &[RustToken<'_>], mut index: usize) -> usize {
    if tokens.get(index).is_some_and(|token| token.is_ident("pub")) {
        index += 1;
        if tokens.get(index).is_some_and(|token| token.is_punct(b'(')) {
            if let Some(after_visibility) = balanced_delimiter_end(tokens, index, b'(', b')') {
                index = after_visibility;
            }
        }
    }
    while let Some(token) = tokens.get(index).copied() {
        if ["unsafe", "async", "default", "auto"]
            .iter()
            .any(|prefix| token.is_ident(prefix))
        {
            index += 1;
            continue;
        }
        if token.is_ident("const")
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.is_ident("fn"))
        {
            index += 1;
            continue;
        }
        if token.is_ident("extern")
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.is_ident("fn"))
        {
            index += 1;
            continue;
        }
        break;
    }
    index
}

fn is_supported_item_start(token: Option<RustToken<'_>>) -> bool {
    let Some(token) = token else {
        return false;
    };
    [
        "const",
        "enum",
        "extern",
        "fn",
        "impl",
        "let",
        "macro",
        "macro_rules",
        "mod",
        "static",
        "struct",
        "trait",
        "type",
        "union",
        "use",
    ]
    .iter()
    .any(|keyword| token.is_ident(keyword))
}

fn conservative_item_end(tokens: &[RustToken<'_>], start: usize) -> Option<usize> {
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        if token.is_punct(b'(') {
            paren_depth = paren_depth.saturating_add(1);
        } else if token.is_punct(b')') {
            paren_depth = paren_depth.saturating_sub(1);
        } else if token.is_punct(b'[') {
            bracket_depth = bracket_depth.saturating_add(1);
        } else if token.is_punct(b']') {
            bracket_depth = bracket_depth.saturating_sub(1);
        } else if paren_depth == 0 && bracket_depth == 0 && token.is_punct(b';') {
            return Some(token.end);
        } else if paren_depth == 0 && bracket_depth == 0 && token.is_punct(b'{') {
            let after = balanced_delimiter_end(tokens, index, b'{', b'}')?;
            return Some(tokens.get(after.checked_sub(1)?)?.end);
        }
    }
    None
}

fn balanced_delimiter_end(
    tokens: &[RustToken<'_>],
    start: usize,
    open: u8,
    close: u8,
) -> Option<usize> {
    if !tokens.get(start).copied()?.is_punct(open) {
        return None;
    }
    let mut depth = 1usize;
    for (offset, token) in tokens.get(start + 1..)?.iter().enumerate() {
        if token.is_punct(open) {
            depth = depth.saturating_add(1);
        } else if token.is_punct(close) {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return Some(start + 2 + offset);
            }
        }
    }
    None
}

pub(super) fn lex_rust_tokens(source: &str) -> Result<Vec<RustToken<'_>>, String> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes[index].is_ascii_whitespace() {
            index += 1;
        } else if bytes.get(index..index + 2) == Some(b"//") {
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
        } else if bytes.get(index..index + 2) == Some(b"/*") {
            index = block_comment_end(bytes, index)?;
        } else if let Some(end) = raw_string_end(bytes, index)? {
            tokens.push(RustToken {
                kind: RustTokenKind::StringLiteral(&source[index..end]),
                start: index,
                end,
            });
            index = end;
        } else if bytes[index] == b'"' {
            let end = quoted_literal_end(bytes, index, b'"')?;
            tokens.push(RustToken {
                kind: RustTokenKind::StringLiteral(&source[index..end]),
                start: index,
                end,
            });
            index = end;
        } else if matches!(bytes[index], b'b' | b'c') && bytes.get(index + 1) == Some(&b'"') {
            let end = quoted_literal_end(bytes, index + 1, b'"')?;
            tokens.push(RustToken {
                kind: RustTokenKind::StringLiteral(&source[index..end]),
                start: index,
                end,
            });
            index = end;
        } else if bytes[index] == b'\'' && is_char_literal(bytes, index) {
            index = quoted_literal_end(bytes, index, b'\'')?;
        } else if bytes[index] == b'b'
            && bytes.get(index + 1) == Some(&b'\'')
            && is_char_literal(bytes, index + 1)
        {
            index = quoted_literal_end(bytes, index + 1, b'\'')?;
        } else if is_ident_start(bytes[index]) {
            let start = index;
            index += 1;
            while index < bytes.len() && is_ident_continue(bytes[index]) {
                index += 1;
            }
            tokens.push(RustToken {
                kind: RustTokenKind::Ident(&source[start..index]),
                start,
                end: index,
            });
        } else {
            let start = index;
            index += source[index..]
                .chars()
                .next()
                .map(char::len_utf8)
                .unwrap_or(1);
            if bytes[start].is_ascii() {
                tokens.push(RustToken {
                    kind: RustTokenKind::Punct(bytes[start]),
                    start,
                    end: index,
                });
            }
        }
    }
    Ok(tokens)
}

fn literal_value_is_sorry(literal: &str) -> bool {
    if literal == "\"sorry\"" {
        return true;
    }
    let Some(r) = literal
        .strip_prefix('r')
        .or_else(|| literal.strip_prefix("br"))
        .or_else(|| literal.strip_prefix("cr"))
    else {
        return false;
    };
    let hashes = r.bytes().take_while(|byte| *byte == b'#').count();
    let Some(body) = r.get(hashes..).and_then(|tail| tail.strip_prefix('"')) else {
        return false;
    };
    let closing = format!("\"{}", "#".repeat(hashes));
    body.strip_suffix(&closing) == Some("sorry")
}

fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(byte: u8) -> bool {
    is_ident_start(byte) || byte.is_ascii_digit()
}

fn block_comment_end(bytes: &[u8], start: usize) -> Result<usize, String> {
    let mut index = start + 2;
    let mut depth = 1usize;
    while index < bytes.len() {
        if bytes.get(index..index + 2) == Some(b"/*") {
            depth = depth.saturating_add(1);
            index += 2;
        } else if bytes.get(index..index + 2) == Some(b"*/") {
            depth = depth.saturating_sub(1);
            index += 2;
            if depth == 0 {
                return Ok(index);
            }
        } else {
            index += 1;
        }
    }
    Err("unterminated block comment".to_string())
}

fn quoted_literal_end(bytes: &[u8], quote: usize, delimiter: u8) -> Result<usize, String> {
    let mut index = quote + 1;
    while index < bytes.len() {
        if bytes[index] == b'\\' {
            index = (index + 2).min(bytes.len());
        } else if bytes[index] == delimiter {
            return Ok(index + 1);
        } else {
            index += 1;
        }
    }
    Err("unterminated quoted literal".to_string())
}

fn is_char_literal(bytes: &[u8], quote: usize) -> bool {
    let Some(&first) = bytes.get(quote + 1) else {
        return false;
    };
    if first == b'\\' {
        return bytes
            .get(quote + 2..)
            .is_some_and(|tail| tail.contains(&b'\''));
    }
    bytes.get(quote + 2) == Some(&b'\'')
}

fn raw_string_end(bytes: &[u8], start: usize) -> Result<Option<usize>, String> {
    let r = if bytes.get(start) == Some(&b'r') {
        start
    } else if matches!(bytes.get(start), Some(b'b' | b'c')) && bytes.get(start + 1) == Some(&b'r') {
        start + 1
    } else {
        return Ok(None);
    };
    let mut quote = r + 1;
    while bytes.get(quote) == Some(&b'#') {
        quote += 1;
    }
    if bytes.get(quote) != Some(&b'"') {
        return Ok(None);
    }
    let hashes = quote - r - 1;
    let mut index = quote + 1;
    while index < bytes.len() {
        if bytes[index] == b'"'
            && bytes
                .get(index + 1..index + 1 + hashes)
                .is_some_and(|tail| tail.iter().all(|byte| *byte == b'#'))
        {
            return Ok(Some(index + 1 + hashes));
        }
        index += 1;
    }
    Err("unterminated raw string literal".to_string())
}
