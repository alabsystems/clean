// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Occurrence-local literal roles. These are source-discovery classifications,
//! not trusted validators or semantic soundness evidence. Unknown syntax stays
//! a candidate. No spelling or source file is exempted by these rules.

use super::scan::{ident, is_punct, lex, Item, Tok};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Role {
    Candidate,
    ByteArray,
    BuildEnvironment,
    FormatString,
    LetBinder,
    ExtensionRegistry,
    ExtensionEncoding,
    ExtensionDecoding,
}

fn before(toks: &[Tok], at: usize, pattern: &str) -> bool {
    let pattern = lex(pattern);
    at.checked_sub(pattern.len())
        .is_some_and(|start| toks[start..at] == pattern)
}

fn after(toks: &[Tok], at: usize, pattern: &str) -> bool {
    let pattern = lex(pattern);
    toks.get(at + 1..at + 1 + pattern.len()) == Some(pattern.as_slice())
}

/// Token index of the direct parent call's last path segment, allowing a turbofish. `open`
/// must be the `(` immediately before the complete argument expression.
pub(super) fn caller_start(toks: &[Tok], open: usize) -> Option<usize> {
    if !is_punct(toks.get(open), '(') {
        return None;
    }
    let mut end = open;
    if end > 0 && is_punct(toks.get(end - 1), '>') {
        let mut depth = 1;
        end -= 1;
        while end > 0 && depth > 0 {
            end -= 1;
            match toks[end] {
                Tok::Punct('>') => depth += 1,
                Tok::Punct('<') => depth -= 1,
                _ => {}
            }
        }
        if depth != 0 || end < 2 || !before(toks, end, "::") {
            return None;
        }
        end -= 2;
    }
    end.checked_sub(1).filter(|&i| ident(toks.get(i)).is_some())
}

fn caller(toks: &[Tok], open: usize) -> Option<&str> {
    caller_start(toks, open).and_then(|i| ident(toks.get(i)))
}

/// Classify only a complete literal expression consumed directly by a known
/// non-declaration position. In particular, neither an enclosing function nor
/// another occurrence of the SAME spelling licenses a lookup.
pub(super) fn role(item: &Item, toks: &[Tok], at: usize, extension_codec: bool) -> Role {
    if matches!(toks.get(at), Some(Tok::ByteStr(_))) {
        // Only a const/static's entire byte-array initializer. An inline byte
        // string converted to text, or an initializer that calls Name code,
        // remains a candidate. References from name-producing code additionally
        // promote these array occurrences (Census::name_data_items).
        let body = &toks[item.range.0..item.range.1];
        let local = at - item.range.0;
        if matches!(ident(body.first()), Some("const" | "static"))
            && body.iter().any(|t| ident(Some(t)) == Some("u8"))
            && (before(body, local, "=") || before(body, local, "= *"))
            && local + 1 == body.len()
        {
            return Role::ByteArray;
        }
        return Role::Candidate;
    }
    if before(toks, at, "env!(") && after(toks, at, ")") {
        return Role::BuildEnvironment;
    }
    if before(toks, at, "write!(f,") && (after(toks, at, ")") || after(toks, at, ",")) {
        return Role::FormatString;
    }
    if !before(toks, at, "Name::from_string(") || !after(toks, at, ")") {
        return Role::Candidate;
    }
    // `Name :: from_string (` is five tokens. The constructor must consume
    // exactly the literal, with no expression attached to its result.
    let start = at - 5;
    let end = at + 2;
    if after(toks, at, "),")
        && start > 0
        && caller(toks, start - 1) == Some("let_named")
        && before(toks, start - 1, "Expr::let_named")
    {
        return Role::LetBinder;
    }
    if is_punct(toks.get(end), ')')
        && start > 0
        && caller(toks, start - 1) == Some("register_persistent_ext")
    {
        return Role::ExtensionRegistry;
    }
    if extension_codec
        && item.name == "to_env_entry"
        && before(toks, start, "EnvExtensionEntry { name:")
        && after(toks, at, "), data:")
    {
        return Role::ExtensionEncoding;
    }
    if extension_codec
        && item.name == "from_env_entry"
        && before(toks, start, "entry.name ==")
        && after(toks, at, ") =>")
        && toks[item.range.0..item.range.1].starts_with(&lex(
            "fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {",
        ))
    {
        return Role::ExtensionDecoding;
    }
    Role::Candidate
}

/// A constructor with a computed string input may consume byte constants or
/// helper results. Demand their bodies too; a byte-array role cannot hide a
/// byte-to-text lookup through a const, local alias or helper function.
pub(super) fn computed_name_input(body: &[Tok]) -> bool {
    let constructor = lex("Name::from_string(");
    body.windows(6)
        .any(|w| w[..5] == constructor && !matches!(w[5], Tok::Str(_)))
        // A string comparison may dispatch without constructing a Name.
        // Conservatively demand byte inputs of text decoders as well.
        || body.iter().any(|t| matches!(ident(Some(t)), Some("from_utf8" | "from_utf8_lossy")))
}
