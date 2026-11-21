// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's own text rendering of names, which the IR decoder's errors use.
//!
//! [`name_to_string`] is `Lean.Name.toString` (`Init/Data/ToString/Name.lean`):
//! components that are not identifiers are escaped with `«»`, except in
//! inaccessible names, names with macro scopes and delaborator pseudo-syntax,
//! which print raw. Whole IR declarations render in `format_decl`, compiled
//! only for the census and tests.

use clean_kernel::name::NameInner;
use clean_kernel::Name;

/// Decimal `Nat.repr` for little-endian 64-bit limbs.
#[must_use]
pub fn nat_to_string(limbs: &[u64]) -> String {
    let mut limbs = limbs.to_vec();
    if limbs.len() == 1 {
        return limbs[0].to_string();
    }
    // Repeated division by 10^19 over little-endian limbs.
    const CHUNK: u64 = 10_000_000_000_000_000_000;
    let mut chunks = Vec::new();
    while limbs.iter().any(|&l| l != 0) {
        let mut rem: u128 = 0;
        for limb in limbs.iter_mut().rev() {
            let cur = (rem << 64) | u128::from(*limb);
            *limb = u64::try_from(cur / u128::from(CHUNK)).unwrap_or(u64::MAX);
            rem = cur % u128::from(CHUNK);
        }
        chunks.push(u64::try_from(rem).unwrap_or(0));
    }
    let mut out = chunks
        .pop()
        .map_or_else(|| "0".to_owned(), |c| c.to_string());
    for chunk in chunks.iter().rev() {
        out.push_str(&format!("{chunk:019}"));
    }
    out
}

// --- Name.toString -----------------------------------------------------------

/// `isLetterLike` (`Init/Meta/Defs.lean`).
fn is_letter_like(c: char) -> bool {
    let v = u32::from(c);
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb
        || (0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3
        || (0x3ca..=0x3fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v)
        || (0x1d49c..=0x1d59f).contains(&v)
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7
        || (0x0100..=0x017f).contains(&v)
}

/// `isSubScriptAlnum` (`Init/Meta/Defs.lean`).
fn is_subscript_alnum(c: char) -> bool {
    let v = u32::from(c);
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

/// `isIdFirst`: `Char.isAlpha` is ASCII-only in Lean.
fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// `isIdRest`.
fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_letter_like(c)
        || is_subscript_alnum(c)
}

/// `Name.needsNoEscape` (both the ASCII fast path and the general one).
fn needs_no_escape(s: &str) -> bool {
    let bytes = s.as_bytes();
    let ascii = bytes
        .first()
        .is_some_and(|b| b.is_ascii_alphabetic() || *b == b'_')
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'\'' | b'!' | b'?'));
    ascii || {
        let mut chars = s.chars();
        chars.next().is_some_and(is_id_first) && chars.all(is_id_rest)
    }
}

/// `Name.escapePart` with `force := false`.
fn escape_part(s: &str) -> Option<String> {
    if !s.is_empty() && needs_no_escape(s) {
        Some(s.to_owned())
    } else if s.contains('»') {
        None
    } else {
        Some(format!("«{s}»"))
    }
}

fn is_inaccessible_user_name(n: &Name) -> bool {
    match n.inner() {
        NameInner::Str(_, s) => s.contains('✝') || s.as_ref() == "_inaccessible",
        NameInner::Num(p, _) => is_inaccessible_user_name(p),
        NameInner::Anon => false,
    }
}

fn has_macro_scopes(n: &Name) -> bool {
    match n.inner() {
        NameInner::Str(_, s) => s.as_ref() == "_hyg",
        NameInner::Num(p, _) => has_macro_scopes(p),
        NameInner::Anon => false,
    }
}

fn root_component(n: &Name) -> &Name {
    let mut current = n;
    loop {
        match current.inner() {
            NameInner::Str(p, _) | NameInner::Num(p, _) if !p.is_anon() => current = p,
            _ => return current,
        }
    }
}

/// `toStringWithToken.maybePseudoSyntax`.
fn maybe_pseudo_syntax(n: &Name) -> bool {
    if let NameInner::Str(p, s) = n.inner() {
        if p.is_anon() && s.as_ref() == "_" {
            return true;
        }
    }
    match root_component(n).inner() {
        NameInner::Str(_, s) => s.starts_with('#') || s.starts_with('?'),
        _ => false,
    }
}

fn to_string_with_sep(n: &Name, escape: bool, out: &mut String) {
    let maybe_escape = |s: &str| {
        if escape {
            escape_part(s).unwrap_or_else(|| s.to_owned())
        } else {
            s.to_owned()
        }
    };
    match n.inner() {
        NameInner::Anon => out.push_str("[anonymous]"),
        NameInner::Str(p, s) if p.is_anon() => out.push_str(&maybe_escape(s)),
        NameInner::Num(p, v) if p.is_anon() => out.push_str(&v.to_string()),
        NameInner::Str(p, s) => {
            to_string_with_sep(p, escape, out);
            out.push('.');
            out.push_str(&maybe_escape(s));
        }
        NameInner::Num(p, v) => {
            to_string_with_sep(p, escape, out);
            out.push('.');
            out.push_str(&v.to_string());
        }
    }
}

/// `Lean.Name.toString` (with `escape := true`).
#[must_use]
pub(crate) fn name_to_string(n: &Name) -> String {
    let escape = !is_inaccessible_user_name(n) && !has_macro_scopes(n) && !maybe_pseudo_syntax(n);
    let mut out = String::new();
    to_string_with_sep(n, escape, &mut out);
    out
}
