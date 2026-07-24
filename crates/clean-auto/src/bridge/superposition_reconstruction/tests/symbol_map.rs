// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for SymbolMap term conversion and type inference.

use super::super::*;
use crate::superposition::Term;
use clean_kernel::BinderInfo;

/// Test that SymbolMap correctly converts simple terms.
#[test]
fn test_symbol_map_const() {
    let mut map = SymbolMap::new();
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(0, a_expr.clone(), nat_ty);

    let term = Term::Const(0);
    let result = map
        .term_to_expr(&term)
        .expect("invariant: term_to_expr succeeded");
    assert_eq!(result, a_expr);
}

/// Test that SymbolMap converts function application terms.
#[test]
fn test_symbol_map_app() {
    let mut map = SymbolMap::new();
    let f_expr = Expr::const_(Name::from_string("f"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.add_symbol(0, f_expr.clone(), nat_ty.clone());
    map.add_symbol(1, a_expr.clone(), nat_ty);

    let term = Term::App(0, vec![Term::Const(1)]);
    let result = map
        .term_to_expr(&term)
        .expect("invariant: term_to_expr succeeded");
    let expected = Expr::app(f_expr, a_expr);
    assert_eq!(result, expected);
}

/// Test that term_type for App peels Pi binders to return the return type.
#[test]
fn test_term_type_app_peels_pi() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    // f : Nat -> Bool (a Pi type)
    let f_type = Expr::pi(BinderInfo::Default, nat_ty.clone(), bool_ty.clone());
    let f_expr = Expr::const_(Name::from_string("f"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    map.add_symbol(0, f_expr, f_type);
    map.add_symbol(1, a_expr, nat_ty);

    // f(a) should have type Bool (the Pi body)
    let app_term = Term::App(0, vec![Term::Const(1)]);
    let result_type = map
        .term_type(&app_term)
        .expect("invariant: term_type succeeded");

    // The body of Pi(_, Nat, Bool) is Bool
    assert_eq!(result_type, bool_ty);
}

/// Test that term_type for App peels multiple Pi binders.
#[test]
fn test_term_type_app_peels_multiple_pi() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    // g : Nat -> Nat -> Bool
    let g_type = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), bool_ty.clone()),
    );
    let g_expr = Expr::const_(Name::from_string("g"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let b_expr = Expr::const_(Name::from_string("b"), vec![]);
    map.add_symbol(0, g_expr, g_type);
    map.add_symbol(1, a_expr, nat_ty.clone());
    map.add_symbol(2, b_expr, nat_ty);

    // g(a, b) should have type Bool
    let app_term = Term::App(0, vec![Term::Const(1), Term::Const(2)]);
    let result_type = map
        .term_type(&app_term)
        .expect("invariant: term_type succeeded");
    assert_eq!(result_type, bool_ty);
}

/// Test that term_type for App substitutes arguments into dependent Pi bodies.
///
/// For a function `f : (x : Nat) -> Vec x`, applying `f(a)` where `a : Nat`
/// should produce type `Vec a`, not `Vec (BVar 0)`.
#[test]
fn test_term_type_dependent_pi_substitutes_arg() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let vec_const = Expr::const_(Name::from_string("Vec"), vec![]);

    // f : (x : Nat) -> Vec x
    // Body of Pi is: App(Vec, BVar(0))  -- BVar(0) references the bound `x`
    let f_type = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::app(vec_const.clone(), Expr::bvar(0)),
    );
    let f_expr = Expr::const_(Name::from_string("f"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    map.add_symbol(0, f_expr, f_type);
    map.add_symbol(1, a_expr.clone(), nat_ty);

    // f(a) should have type Vec(a), not Vec(BVar(0))
    let app_term = Term::App(0, vec![Term::Const(1)]);
    let result_type = map
        .term_type(&app_term)
        .expect("invariant: term_type succeeded");

    let expected = Expr::app(vec_const, a_expr);
    assert_eq!(
        result_type, expected,
        "dependent Pi body should have BVar(0) substituted with the actual argument"
    );
}

/// Test that term_type substitutes multiple arguments in nested dependent Pi.
///
/// For `g : (x : Nat) -> (y : Nat) -> Pair x y`, applying `g(a, b)` should
/// produce `Pair a b`.
#[test]
fn test_term_type_nested_dependent_pi() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair_const = Expr::const_(Name::from_string("Pair"), vec![]);

    // g : (x : Nat) -> (y : Nat) -> Pair x y
    // Inner body: App(App(Pair, BVar(1)), BVar(0))
    //   BVar(0) = y (inner binder), BVar(1) = x (outer binder)
    let inner_body = Expr::app(Expr::app(pair_const.clone(), Expr::bvar(1)), Expr::bvar(0));
    let inner_pi = Expr::pi(BinderInfo::Default, nat_ty.clone(), inner_body);
    let g_type = Expr::pi(BinderInfo::Default, nat_ty.clone(), inner_pi);

    let g_expr = Expr::const_(Name::from_string("g"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let b_expr = Expr::const_(Name::from_string("b"), vec![]);
    map.add_symbol(0, g_expr, g_type);
    map.add_symbol(1, a_expr.clone(), nat_ty.clone());
    map.add_symbol(2, b_expr.clone(), nat_ty);

    // g(a, b) should have type Pair(a, b)
    let app_term = Term::App(0, vec![Term::Const(1), Term::Const(2)]);
    let result_type = map
        .term_type(&app_term)
        .expect("invariant: term_type succeeded");

    let expected = Expr::app(Expr::app(pair_const, a_expr), b_expr);
    assert_eq!(
        result_type, expected,
        "nested dependent Pi should substitute both arguments correctly"
    );
}

/// Test that term_type returns error on arity mismatch (more args than Pi binders).
#[test]
fn test_term_type_arity_mismatch_returns_error() {
    let mut map = SymbolMap::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // h : Nat (not a function type -- zero Pi binders)
    let h_expr = Expr::const_(Name::from_string("h"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    map.add_symbol(0, h_expr, nat_ty.clone());
    map.add_symbol(1, a_expr, nat_ty);

    // h(a) should fail: Nat is not a Pi type
    let app_term = Term::App(0, vec![Term::Const(1)]);
    let result = map.term_type(&app_term);
    assert!(
        result.is_err(),
        "applying args to non-Pi type should return error"
    );
    assert!(
        matches!(
            result.unwrap_err(),
            ReconstructionError::SortInferenceFailed(_)
        ),
        "error should be SortInferenceFailed"
    );
}

/// Test that unmapped symbols produce errors.
#[test]
fn test_unmapped_symbol_error() {
    let map = SymbolMap::new();
    let term = Term::Const(99);
    let err = map
        .term_to_expr(&term)
        .expect_err("unmapped symbol 99 should produce error");
    assert!(
        matches!(err, ReconstructionError::UnmappedSymbol(99)),
        "expected UnmappedSymbol(99), got {err:?}"
    );
}
