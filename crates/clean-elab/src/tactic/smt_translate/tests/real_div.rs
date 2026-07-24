// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real translation tests for the SMT-LIB proof-producing path (#2795, #2796, #2800).
//!
//! Verifies that Real-typed division (both typeclass `HDiv.hDiv` and direct
//! `Real.div`), direct arithmetic, and direct comparison heads emit the correct
//! SMT-LIB surface instead of falling back to opaque Bool placeholders.

use super::*;

// -- Family-local helpers --

fn real_of_int_neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n),
        ),
    )
}

/// Build `@HDiv.hDiv Real Real Real inst lhs rhs` — typeclass Real division.
fn make_real_hdiv(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    make_hdiv(real_ty, lhs, rhs)
}

/// Build `Real.div lhs rhs` — direct Real division.
fn make_real_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.div"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.add lhs rhs` (direct 2-arg form).
fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.sub lhs rhs` (direct 2-arg form).
fn real_sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.sub"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.mul lhs rhs` (direct 2-arg form).
fn real_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.lt lhs rhs` (direct 2-arg form).
fn real_lt_direct(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.lt"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.le lhs rhs` (direct 2-arg form).
fn real_le_direct(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.le"), vec![]), lhs),
        rhs,
    )
}

// -- Tests --

#[test]
fn test_hdiv_real_concrete_ofnat_uses_real_division() {
    let mut t = SmtLibTranslator::new();
    // HDiv.hDiv Real Real Real inst (Real.ofInt 1) (Real.ofNat 2) → (/ 1.0 2.0)
    let expr = make_real_hdiv(
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            Expr::nat_lit(1),
        ),
        Expr::app(
            Expr::const_(Name::from_string("Real.ofNat"), vec![]),
            Expr::nat_lit(2),
        ),
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "(/ 1.0 2.0)");
}

#[test]
fn test_hdiv_real_nat_literal_denominator_uses_real_division() {
    let mut t = SmtLibTranslator::new();
    // HDiv.hDiv Real Real Real inst (Real.ofNat 5) 2 → (/ 5.0 2)
    let expr = make_real_hdiv(real_of_nat(5), Expr::nat_lit(2));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(/ 5.0 2)");
}

#[test]
fn test_hdiv_real_symbolic_denominator_fails_closed() {
    let mut t = SmtLibTranslator::new();
    // HDiv.hDiv Real Real Real inst (Real.ofNat 1) fvar → UnsupportedExpr
    let fvar = Expr::fvar(FVarId::new(99));
    let expr = make_real_hdiv(real_of_nat(1), fvar);
    let err = t.translate_expr(&expr).unwrap_err();
    assert!(
        format!("{err:?}").contains("symbolic denominator"),
        "expected symbolic denominator error, got: {err:?}"
    );
}

#[test]
fn test_real_div_direct_concrete_uses_real_division() {
    let mut t = SmtLibTranslator::new();
    // Real.div (Real.ofInt 1) (Real.ofNat 2) → (/ 1.0 2.0)
    let expr = make_real_div(
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt"), vec![]),
            Expr::nat_lit(1),
        ),
        real_of_nat(2),
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "(/ 1.0 2.0)");
}

#[test]
fn test_real_div_direct_symbolic_denominator_fails_closed() {
    let mut t = SmtLibTranslator::new();
    // Real.div (Real.ofNat 3) fvar → UnsupportedExpr
    let fvar = Expr::fvar(FVarId::new(99));
    let expr = make_real_div(real_of_nat(3), fvar);
    let err = t.translate_expr(&expr).unwrap_err();
    assert!(
        format!("{err:?}").contains("symbolic denominator"),
        "expected symbolic denominator error, got: {err:?}"
    );
}

#[test]
fn test_hdiv_nat_still_uses_total_after_real_div_fix() {
    // Ensure Nat division is unchanged by the Real division fix
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let expr = make_hdiv(nat_ty, Expr::nat_lit(7), Expr::nat_lit(3));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (> 3 0) (div 7 3) 0)"
    );
}

#[test]
fn test_hdiv_int_still_uses_int_div_after_real_div_fix() {
    // Ensure Int division is unchanged by the Real division fix
    let mut t = SmtLibTranslator::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let expr = make_hdiv(int_ty, Expr::nat_lit(7), Expr::nat_lit(3));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(div 7 3)");
}

// --- Direct Real.add / Real.sub / Real.mul tests (#2796) ---

#[test]
fn test_real_add_direct_translates_to_plus() {
    let mut t = SmtLibTranslator::new();
    let expr = real_add(real_of_nat(3), real_of_nat(5));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(+ 3.0 5.0)");
}

#[test]
fn test_real_sub_direct_translates_to_minus() {
    let mut t = SmtLibTranslator::new();
    let expr = real_sub(real_of_nat(7), real_of_nat(2));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(- 7.0 2.0)");
}

#[test]
fn test_real_mul_direct_translates_to_times() {
    let mut t = SmtLibTranslator::new();
    let expr = real_mul(real_of_nat(4), real_of_nat(6));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(* 4.0 6.0)");
}

#[test]
fn test_real_add_not_monus_semantics() {
    // Real.add should produce plain +, not Nat monus
    let mut t = SmtLibTranslator::new();
    let expr = real_add(real_of_nat(0), real_of_nat(1));
    let result = t.translate_expr(&expr).unwrap();
    assert!(result.contains('+'), "Real.add should use + operator");
    assert!(!result.contains("ite"), "Real.add must not use monus/ite");
}

#[test]
fn test_real_sub_not_monus_semantics() {
    // Real.sub should produce plain -, not Nat monus (ite (>= ...))
    let mut t = SmtLibTranslator::new();
    let expr = real_sub(real_of_nat(1), real_of_nat(2));
    let result = t.translate_expr(&expr).unwrap();
    assert!(result.contains('-'), "Real.sub should use - operator");
    assert!(!result.contains("ite"), "Real.sub must not use monus/ite");
}

#[test]
fn test_real_lt_direct_translates_without_bool_placeholder() {
    let mut t = SmtLibTranslator::new();
    let expr = real_lt_direct(real_of_nat(0), real_of_nat(1));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(< 0.0 1.0)");
    assert!(
        t.declarations().is_empty(),
        "direct Real.lt should stay on the arithmetic surface: {:?}",
        t.declarations()
    );
}

#[test]
fn test_real_le_direct_translates_without_bool_placeholder() {
    let mut t = SmtLibTranslator::new();
    let expr = real_le_direct(real_of_int_neg_succ(0), real_of_nat(0));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(<= (- 1.0) 0.0)");
    assert!(
        t.declarations().is_empty(),
        "direct Real.le should stay on the arithmetic surface: {:?}",
        t.declarations()
    );
}
