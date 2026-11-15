// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Review of the string-literal expansion (`native_fold_review.rs`): a literal
//! `"s"` means `String.ofList [Char.ofNat c₁, …]` only over the definitions of
//! `String.ofList` and `Char.ofNat` it was written against, and both names
//! are reviewed together because the rule needs both.
//!
//! Legs, in `KernelTheory::LeanReference`: every test literal is
//! definitionally its expansion at type `String`; no test literal is
//! definitionally the expansion of a DIFFERENT string (the expansion does not
//! identify distinct literals); and `Char.ofNat n`'s code point, read through
//! the definition of `Char.toNat` with no reducer, is `n` for a Unicode scalar
//! value and `0` otherwise — the reading every character reducer assumes.

use super::{checker, def_eq, fresh, Review};
use crate::env::{Environment, KernelTheory};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

const STRINGS: [&str; 8] = ["", "a", "abc", "ab", "a b\n", "héllo", "Ä\u{3000}", "😀z"];

/// Code points around every boundary `Char.ofNat` distinguishes.
const CODE_POINTS: [u32; 9] = [
    0,
    0x41,
    0xD7FF,
    0xD800,
    0xDFFF,
    0xE000,
    0x10FFFF,
    0x110000,
    0x7FFF_FFFF,
];

pub(super) fn is_literal_key(name: &str) -> bool {
    matches!(name, "String.ofList" | "Char.ofNat")
}

fn c(s: &str) -> Expr {
    Expr::const_(Name::from_string(s), vec![])
}

/// `String.ofList [Char.ofNat c, …]` for the characters of `s`.
fn expansion_head(env: &Environment) -> Option<&'static str> {
    if env.get_const(&Name::from_string("String.ofList")).is_some() {
        Some("String.ofList")
    } else if env
        .get_constructor(&Name::from_string("String.mk"))
        .is_some()
    {
        Some("String.mk")
    } else {
        None
    }
}

fn expansion(s: &str, constructor: &str) -> Expr {
    let ty = c("Char");
    let mut list = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        ty.clone(),
    );
    for ch in s.chars().rev() {
        let head = Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(u32::from(ch))));
        list = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [ty.clone(), head, list],
        );
    }
    Expr::app(c(constructor), list)
}

/// A different string of the same shape: the last character bumped, or one
/// character appended to the empty string.
fn mutated(s: &str) -> String {
    let mut chars: Vec<char> = s.chars().collect();
    match chars.last_mut() {
        Some(last) => *last = if *last == 'z' { 'y' } else { 'z' },
        None => chars.push('a'),
    }
    chars.into_iter().collect()
}

/// Whether `s` reads as its characters here: the literal is definitionally
/// `String.ofList [Char.ofNat c, …]` in `tc`'s theory.
pub(super) fn expansion_admitted(env: &Environment, tc: &TypeChecker<'_>, s: &str) -> bool {
    let Some(head) = expansion_head(env) else {
        return false;
    };
    ["Char.ofNat", "List.cons", "List.nil"]
        .iter()
        .all(|n| env.get_const(&Name::from_string(n)).is_some())
        && def_eq(tc, &Expr::str_lit(s), &expansion(s, head))
}

pub(super) fn review_literal(env: &Environment) -> Review {
    let Some(head) = expansion_head(env) else {
        return Review::unreviewable("no string conversion or list-backed constructor");
    };
    for needed in ["Char.ofNat", "Char.toNat", "List.cons", "List.nil"] {
        if env.get_const(&Name::from_string(needed)).is_none() {
            return Review::unreviewable(format!("`{needed}` is absent"));
        }
    }
    let tc = checker(env, Some(KernelTheory::LeanReference));
    let mut out = Review::default();
    for s in STRINGS {
        out.cases += 1;
        out.fired += 1;
        let lit = Expr::str_lit(s);
        fresh(&tc);
        match tc.infer_type(&expansion(s, head)) {
            Ok(ty) if def_eq(&tc, &ty, &c("String")) => {}
            other => out
                .failures
                .push(format!("T {s:?}: the expansion's type is {other:?}")),
        }
        if !def_eq(&tc, &lit, &expansion(s, head)) {
            out.failures
                .push(format!("D {s:?}: the literal is not its own expansion"));
            if s.is_empty() {
                out.failures.push(format!(
                    "literal registry: head={head}; String={:?}; String.mk={:?}; List={:?}; nil={:?}; cons={:?}",
                    env.get_inductive(&Name::from_string("String")),
                    env.get_constructor(&Name::from_string("String.mk")),
                    env.get_inductive(&Name::from_string("List")),
                    env.get_constructor(&Name::from_string("List.nil")),
                    env.get_constructor(&Name::from_string("List.cons")),
                ));
            }
        }
        let other = mutated(s);
        if def_eq(&tc, &lit, &expansion(&other, head)) {
            out.failures.push(format!(
                "N {s:?}: the literal equals the expansion of {other:?}"
            ));
        }
    }
    for cp in CODE_POINTS {
        out.cases += 1;
        out.fired += 1;
        let valid = cp < 0xD800 || (0xDFFF < cp && cp < 0x11_0000);
        let expected = Expr::nat_lit(u64::from(if valid { cp } else { 0 }));
        let read = Expr::app(
            c("Char.toNat"),
            Expr::app(c("Char.ofNat"), Expr::nat_lit(u64::from(cp))),
        );
        if !def_eq(&tc, &read, &expected) {
            out.failures.push(format!(
                "I {cp:#x}: Char.toNat (Char.ofNat {cp:#x}) is not {expected:?}"
            ));
        }
    }
    out
}
