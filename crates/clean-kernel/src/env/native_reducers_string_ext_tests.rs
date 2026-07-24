// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended String native reducers (search, replace, trim, comparison).

use super::*;
use crate::expr::{ExprKind, Literal};
use crate::name::Name;

// === String.startsWith tests ===

#[test]
fn test_reduce_string_starts_with_true() {
    let s = Expr::str_lit("hello world");
    let prefix = Expr::str_lit("hello");
    let result = reduce_string_starts_with(&[&s, &prefix]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_string_starts_with_false() {
    let s = Expr::str_lit("hello world");
    let prefix = Expr::str_lit("world");
    let result = reduce_string_starts_with(&[&s, &prefix]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === String.endsWith tests ===

#[test]
fn test_reduce_string_ends_with_true() {
    let s = Expr::str_lit("hello world");
    let suffix = Expr::str_lit("world");
    let result = reduce_string_ends_with(&[&s, &suffix]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_string_ends_with_false() {
    let s = Expr::str_lit("hello world");
    let suffix = Expr::str_lit("hello");
    let result = reduce_string_ends_with(&[&s, &suffix]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === String.containsSubstr tests ===

#[test]
fn test_reduce_string_contains_true() {
    let s = Expr::str_lit("hello world");
    let needle = Expr::str_lit("lo wo");
    let result = reduce_string_contains(&[&s, &needle]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"));
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_string_contains_false() {
    let s = Expr::str_lit("hello world");
    let needle = Expr::str_lit("xyz");
    let result = reduce_string_contains(&[&s, &needle]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"));
    } else {
        panic!("Expected Bool.false");
    }
}

// === String.replace tests ===

#[test]
fn test_reduce_string_replace() {
    let s = Expr::str_lit("hello world");
    let pat = Expr::str_lit("world");
    let rep = Expr::str_lit("lean");
    let result = reduce_string_replace(&[&s, &pat, &rep]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hello lean");
    } else {
        panic!("Expected string literal");
    }
}

#[test]
fn test_reduce_string_replace_no_match() {
    let s = Expr::str_lit("hello");
    let pat = Expr::str_lit("xyz");
    let rep = Expr::str_lit("abc");
    let result = reduce_string_replace(&[&s, &pat, &rep]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hello");
    } else {
        panic!("Expected string literal");
    }
}

// === String.trimLeft / String.trimRight tests ===

#[test]
fn test_reduce_string_trim_left() {
    let s = Expr::str_lit("  hello  ");
    let result = reduce_string_trim_left(&[&s]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "hello  ");
    } else {
        panic!("Expected string literal");
    }
}

#[test]
fn test_reduce_string_trim_right() {
    let s = Expr::str_lit("  hello  ");
    let result = reduce_string_trim_right(&[&s]);
    assert!(result.is_some());
    if let ExprKind::Lit(Literal::String(r)) = result.unwrap().kind() {
        assert_eq!(&**r, "  hello");
    } else {
        panic!("Expected string literal");
    }
}

// === String.substrEq tests ===

#[test]
fn test_reduce_string_substr_eq_true() {
    let s1 = Expr::str_lit("hello");
    let off1 = Expr::nat_lit(1);
    let s2 = Expr::str_lit("bell");
    let off2 = Expr::nat_lit(1);
    let len = Expr::nat_lit(3);
    let result = reduce_string_substr_eq(&[&s1, &off1, &s2, &off2, &len]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.true"), "\"ell\" == \"ell\"");
    } else {
        panic!("Expected Bool.true");
    }
}

#[test]
fn test_reduce_string_substr_eq_false() {
    let s1 = Expr::str_lit("hello");
    let off1 = Expr::nat_lit(0);
    let s2 = Expr::str_lit("world");
    let off2 = Expr::nat_lit(0);
    let len = Expr::nat_lit(3);
    let result = reduce_string_substr_eq(&[&s1, &off1, &s2, &off2, &len]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(*name, Name::from_string("Bool.false"), "\"hel\" != \"wor\"");
    } else {
        panic!("Expected Bool.false");
    }
}

#[test]
fn test_reduce_string_substr_eq_out_of_bounds() {
    let s1 = Expr::str_lit("hi");
    let off1 = Expr::nat_lit(0);
    let s2 = Expr::str_lit("hello");
    let off2 = Expr::nat_lit(0);
    let len = Expr::nat_lit(5);
    let result = reduce_string_substr_eq(&[&s1, &off1, &s2, &off2, &len]);
    assert!(result.is_some());
    if let ExprKind::Const(name, _) = result.unwrap().kind() {
        assert_eq!(
            *name,
            Name::from_string("Bool.false"),
            "Out of bounds should be false"
        );
    } else {
        panic!("Expected Bool.false");
    }
}

// === Registration test ===

#[test]
fn test_string_ext_native_reducers_registered() {
    let mut env = Environment::new();
    env.init_string_ext_native_reducers();

    assert!(env.get_native_reducer(&names::STRING_STARTS_WITH).is_some());
    assert!(env.get_native_reducer(&names::STRING_ENDS_WITH).is_some());
    assert!(env.get_native_reducer(&names::STRING_CONTAINS).is_some());
    assert!(env.get_native_reducer(&names::STRING_REPLACE).is_some());
    assert!(env.get_native_reducer(&names::STRING_TRIM_LEFT).is_some());
    assert!(env.get_native_reducer(&names::STRING_TRIM_RIGHT).is_some());
    assert!(env.get_native_reducer(&names::STRING_SUBSTR_EQ).is_some());
}
