// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the enhanced `#eval` command.

use super::*;
use clean_kernel::{Environment, Expr, Level};

#[test]
fn test_eval_nat_literal() {
    let env = Environment::new();
    let nat_42 = Expr::nat_lit(42u64);
    let result = eval_expression(&nat_42, &env).expect("should eval nat literal");
    match &result {
        EvalResult::Value(v) => assert_eq!(v, "42"),
        other => panic!("expected Value, got {other:?}"),
    }
}

#[test]
fn test_eval_string_literal() {
    let env = Environment::new();
    let hello = Expr::str_lit("hello");
    let result = eval_expression(&hello, &env).expect("should eval string literal");
    match &result {
        EvalResult::Value(v) => assert_eq!(v, "\"hello\""),
        other => panic!("expected Value, got {other:?}"),
    }
}

#[test]
fn test_eval_sort_returns_type() {
    let env = Environment::new();
    // Prop = Sort(0) is a type
    let prop = Expr::sort(Level::zero());
    let result = eval_expression(&prop, &env).expect("should eval sort");
    match &result {
        EvalResult::Type(t) => {
            assert!(!t.is_empty(), "type display should not be empty");
        }
        other => panic!("expected Type, got {other:?}"),
    }
}

#[test]
fn test_eval_error_on_ill_typed() {
    let env = Environment::new();
    let bad = Expr::const_(Name::from_string("nonexistent"), vec![]);
    let err = eval_expression(&bad, &env);
    assert!(err.is_err(), "should fail for unknown constant");
}

#[test]
fn test_eval_result_display() {
    let v = EvalResult::Value("42".into());
    assert_eq!(format!("{v}"), "42");

    let io = EvalResult::Io("hello\n()".into());
    assert_eq!(format!("{io}"), "hello\n()");

    let t = EvalResult::Type("Prop : Type".into());
    assert_eq!(format!("{t}"), "Prop : Type");

    let e = EvalResult::Error("bad expr".into());
    assert_eq!(format!("{e}"), "bad expr");
}

#[test]
fn test_try_display_literal_nat() {
    let expr = Expr::nat_lit(100u64);
    assert_eq!(try_display_literal(&expr), Some("100".to_owned()));
}

#[test]
fn test_try_display_literal_string() {
    let expr = Expr::str_lit("test");
    assert_eq!(try_display_literal(&expr), Some("\"test\"".to_owned()));
}

#[test]
fn test_try_display_literal_bool_true() {
    let expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert_eq!(try_display_literal(&expr), Some("true".to_owned()));
}

#[test]
fn test_try_display_literal_bool_false() {
    let expr = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert_eq!(try_display_literal(&expr), Some("false".to_owned()));
}

#[test]
fn test_try_display_literal_unit() {
    let expr = Expr::const_(Name::from_string("Unit.unit"), vec![]);
    assert_eq!(try_display_literal(&expr), Some("()".to_owned()));
}

#[test]
fn test_try_display_literal_unknown_const() {
    let expr = Expr::const_(Name::from_string("Foo.bar"), vec![]);
    assert_eq!(try_display_literal(&expr), None);
}

#[test]
fn test_try_display_constructor_list_nil() {
    let nil = Expr::const_(Name::from_string("List.nil"), vec![]);
    assert_eq!(try_display_constructor(&nil), Some("[]".to_owned()));
}

#[test]
fn test_try_display_constructor_option_none() {
    let none = Expr::const_(Name::from_string("Option.none"), vec![]);
    assert_eq!(try_display_constructor(&none), Some("none".to_owned()));
}

/// Build `List.cons {Nat} <head> <tail>`.
fn list_cons(head: Expr, tail: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![]),
        [nat_ty, head, tail],
    )
}

#[test]
fn test_try_display_constructor_array_of_list() {
    // Array.mk (List.cons 1 (List.cons 2 List.nil)) → [1, 2]
    let nil = Expr::const_(Name::from_string("List.nil"), vec![]);
    let list = list_cons(Expr::nat_lit(1u64), list_cons(Expr::nat_lit(2u64), nil));
    let array = Expr::app(Expr::const_(Name::from_string("Array.mk"), vec![]), list);
    assert_eq!(try_display_constructor(&array), Some("[1, 2]".to_owned()));
}

#[test]
fn test_try_display_constructor_array_empty() {
    // Array.mk List.nil → []
    let nil = Expr::const_(Name::from_string("List.nil"), vec![]);
    let array = Expr::app(Expr::const_(Name::from_string("Array.mk"), vec![]), nil);
    assert_eq!(try_display_constructor(&array), Some("[]".to_owned()));
}

#[test]
fn test_try_display_constructor_array_direct_positional() {
    // Surface-elaborated fallback: Array.mk Nat 1 2 → [1, 2] (type arg dropped).
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let array = Expr::apps(
        Expr::const_(Name::from_string("Array.mk"), vec![]),
        [nat_ty, Expr::nat_lit(1u64), Expr::nat_lit(2u64)],
    );
    assert_eq!(try_display_constructor(&array), Some("[1, 2]".to_owned()));
}
