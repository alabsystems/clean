// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fallback/fail-closed path tests.

use super::*;

#[test]
fn test_translate_unknown_const_returns_error() {
    let mut t = SmtLibTranslator::new();
    let expr = Expr::const_(Name::from_string("MyCustomProp"), vec![]);
    let err = t
        .translate_expr(&expr)
        .expect_err("unknown constants must fail closed");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unknown constant: MyCustomProp")),
        "unexpected error for unknown constant: {err:?}"
    );
    assert!(t.declarations().is_empty());
}

#[test]
fn test_translate_unhandled_expr_kind_returns_error() {
    let mut t = SmtLibTranslator::new();
    // A Sort expression is unsupported and must fail closed.
    let sort_expr = Expr::sort(Level::zero());
    let err = t
        .translate_expr(&sort_expr)
        .expect_err("unhandled expression kinds must be rejected");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unsupported expression kind")),
        "unexpected error for unsupported expression kind: {err:?}"
    );
    assert!(t.declarations().is_empty());
}

#[test]
fn test_translate_non_const_app_head_returns_error() {
    let mut t = SmtLibTranslator::new();
    // Application with a non-const head: (λ x, x) 5
    let lam = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::bvar(0),
    );
    let app_expr = Expr::app(lam, Expr::nat_lit(5));
    let err = t
        .translate_expr(&app_expr)
        .expect_err("non-const heads must be rejected");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unsupported application head")),
        "unexpected error for non-const application head: {err:?}"
    );
    assert!(t.declarations().is_empty());
}

#[test]
fn test_translate_string_literal() {
    let mut t = SmtLibTranslator::new();
    let expr = Expr::str_lit("hello");
    let result = t.translate_expr(&expr).unwrap();
    assert!(
        result.starts_with("str_"),
        "string literals should lower to opaque Int constants: {result}"
    );
    assert_eq!(t.declarations(), &[format!("(declare-const {result} Int)")]);
}

#[test]
fn test_translate_unknown_const_app_returns_error() {
    let mut t = SmtLibTranslator::new();
    // Unknown function with 1 arg must fail closed.
    let app_expr = Expr::app(
        Expr::const_(Name::from_string("MyFunc"), vec![]),
        Expr::nat_lit(1),
    );
    let err = t
        .translate_expr(&app_expr)
        .expect_err("unknown constant applications must be rejected");
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(ref message) if message.contains("unsupported constant application: MyFunc")),
        "unexpected error for unknown constant application: {err:?}"
    );
    assert!(t.declarations().is_empty());
}
