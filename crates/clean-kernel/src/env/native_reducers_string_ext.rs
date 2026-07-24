// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended String native reducers: search, replace, trim, comparison.
//!
//! Split from `native_reducers_string.rs` to stay within the 500-line limit.
//! These are higher-level string operations that Lean 4 provides as built-in
//! native reducers. Part of #3134.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for extended string reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static STRING_STARTS_WITH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.startsWith"));
    pub(crate) static STRING_ENDS_WITH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.endsWith"));
    pub(crate) static STRING_CONTAINS: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.containsSubstr"));
    pub(crate) static STRING_REPLACE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.replace"));
    pub(crate) static STRING_TRIM_LEFT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.trimLeft"));
    pub(crate) static STRING_TRIM_RIGHT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.trimRight"));
    pub(crate) static STRING_SUBSTR_EQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.substrEq"));
}

/// Extract a String value from an expression.
pub(crate) fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// Extract a Nat value from an expression.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Build a Bool expression.
pub(crate) fn mk_bool_expr(val: bool) -> Expr {
    static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    if val {
        Expr::const_(BOOL_TRUE.clone(), vec![])
    } else {
        Expr::const_(BOOL_FALSE.clone(), vec![])
    }
}

/// Native reducer for `String.startsWith : String → String → Bool`.
pub(crate) fn reduce_string_starts_with(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let prefix = get_string_val(args[1])?;
    Some(mk_bool_expr(s.starts_with(prefix)))
}

/// Native reducer for `String.endsWith : String → String → Bool`.
pub(crate) fn reduce_string_ends_with(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let suffix = get_string_val(args[1])?;
    Some(mk_bool_expr(s.ends_with(suffix)))
}

/// Native reducer for `String.containsSubstr : String → String → Bool`.
pub(crate) fn reduce_string_contains(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let needle = get_string_val(args[1])?;
    Some(mk_bool_expr(s.contains(needle)))
}

/// Native reducer for `String.replace : String → String → String → String`.
pub(crate) fn reduce_string_replace(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 3 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let pat = get_string_val(args[1])?;
    let rep = get_string_val(args[2])?;
    Some(Expr::str_lit(s.replace(pat, rep)))
}

/// Native reducer for `String.trimLeft : String → String`.
///
/// Removes leading whitespace.
pub(crate) fn reduce_string_trim_left(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    Some(Expr::str_lit(s.trim_start()))
}

/// Native reducer for `String.trimRight : String → String`.
///
/// Removes trailing whitespace.
pub(crate) fn reduce_string_trim_right(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    Some(Expr::str_lit(s.trim_end()))
}

/// Native reducer for `String.substrEq : String → Nat → String → Nat → Nat → Bool`.
///
/// Compares substrings: checks whether `s1[off1..off1+len] == s2[off2..off2+len]`
/// where offsets and length are in byte positions.
pub(crate) fn reduce_string_substr_eq(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 5 {
        return None;
    }
    let s1 = get_string_val(args[0])?;
    let off1 = get_nat_val(args[1])? as usize;
    let s2 = get_string_val(args[2])?;
    let off2 = get_nat_val(args[3])? as usize;
    let len = get_nat_val(args[4])? as usize;

    // Bounds check — out of bounds is false
    if off1 + len > s1.len() || off2 + len > s2.len() {
        return Some(mk_bool_expr(false));
    }
    // Validate char boundaries
    if !s1.is_char_boundary(off1)
        || !s1.is_char_boundary(off1 + len)
        || !s2.is_char_boundary(off2)
        || !s2.is_char_boundary(off2 + len)
    {
        return None;
    }
    let eq = s1[off1..off1 + len] == s2[off2..off2 + len];
    Some(mk_bool_expr(eq))
}

/// Register extended String native reducers on the environment.
impl Environment {
    pub(crate) fn init_string_ext_native_reducers(&mut self) {
        self.register_native_reducer(names::STRING_STARTS_WITH.clone(), reduce_string_starts_with);
        self.register_native_reducer(names::STRING_ENDS_WITH.clone(), reduce_string_ends_with);
        self.register_native_reducer(names::STRING_CONTAINS.clone(), reduce_string_contains);
        self.register_native_reducer(names::STRING_REPLACE.clone(), reduce_string_replace);
        self.register_native_reducer(names::STRING_TRIM_LEFT.clone(), reduce_string_trim_left);
        self.register_native_reducer(names::STRING_TRIM_RIGHT.clone(), reduce_string_trim_right);
        self.register_native_reducer(names::STRING_SUBSTR_EQ.clone(), reduce_string_substr_eq);
    }
}

#[cfg(test)]
#[path = "native_reducers_string_ext_tests.rs"]
mod tests;
