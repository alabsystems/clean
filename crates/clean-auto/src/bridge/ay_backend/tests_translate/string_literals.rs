// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! String literal caching tests (#2306).

use super::*;
use clean_kernel::Expr;

/// Test that identical string literals produce the same ay term (#2306).
///
/// Before the fix, each `Literal::String` created a fresh `Sort::Int` constant,
/// so `"hello" = "hello"` could be modeled as false (unsound for string equality).
#[test]
fn test_string_literal_identical_same_term() {
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let s1 = Expr::str_lit("hello");
    let s2 = Expr::str_lit("hello");

    let t1 = backend
        .translate_expr(&s1)
        .expect("string lit should translate");
    let t2 = backend
        .translate_expr(&s2)
        .expect("string lit should translate");

    assert_eq!(
        t1, t2,
        "identical string literals must produce the same ay term"
    );
}

/// Test that distinct string literals produce different ay terms (#2306).
#[test]
fn test_string_literal_distinct_different_terms() {
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let s1 = Expr::str_lit("hello");
    let s2 = Expr::str_lit("world");

    let t1 = backend
        .translate_expr(&s1)
        .expect("string lit should translate");
    let t2 = backend
        .translate_expr(&s2)
        .expect("string lit should translate");

    // Different strings get different fresh constants, so they should differ
    assert_ne!(
        t1, t2,
        "distinct string literals should produce different ay terms"
    );
}

/// Test that "hello" = "hello" is provable after fix (#2306).
///
/// Asserts `str1 != str2` where both come from `"hello"`. Since they map to the
/// same constant, this is UNSAT.
#[test]
fn test_string_literal_equality_provable() {
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let s1 = Expr::str_lit("hello");
    let s2 = Expr::str_lit("hello");

    let t1 = backend.translate_expr(&s1).expect("translate");
    let t2 = backend.translate_expr(&s2).expect("translate");

    let diseq = backend.neq(t1, t2);
    backend.assert_term(diseq);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Unsat,
        "\"hello\" != \"hello\" should be UNSAT (identical strings are equal)"
    );
}
