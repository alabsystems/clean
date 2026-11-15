// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int arithmetic semantics tests.

use super::*;

#[test]
fn test_translate_nat_sub_monus_semantics() {
    let mut t = SmtLibTranslator::new();
    // Nat.sub has monus semantics: max(a - b, 0)
    let sub_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.sub"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(
        t.translate_expr(&sub_expr).unwrap(),
        "(ite (>= 10 3) (- 10 3) 0)"
    );
}

#[test]
fn test_translate_int_sub_plain() {
    let mut t = SmtLibTranslator::new();
    // Int.sub has standard subtraction (can go negative)
    let sub_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.sub"), vec![]),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(10),
    );
    assert_eq!(t.translate_expr(&sub_expr).unwrap(), "(- 3 10)");
}

#[test]
fn test_translate_mul() {
    let mut t = SmtLibTranslator::new();
    let mul_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            Expr::nat_lit(4),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(t.translate_expr(&mul_expr).unwrap(), "(* 4 5)");
}

#[test]
fn test_translate_neg() {
    let mut t = SmtLibTranslator::new();
    let neg_expr = Expr::app(
        Expr::const_(Name::from_string("Int.neg"), vec![]),
        Expr::nat_lit(7),
    );
    assert_eq!(t.translate_expr(&neg_expr).unwrap(), "(- 7)");
}

#[test]
fn test_translate_nat_div_total_semantics() {
    let mut t = SmtLibTranslator::new();
    // Nat.div is total: Nat.div a 0 = 0
    let div_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.div"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(
        t.translate_expr(&div_expr).unwrap(),
        "(ite (> 3 0) (div 10 3) 0)"
    );
}

#[test]
fn test_translate_nat_mod_total_semantics() {
    let mut t = SmtLibTranslator::new();
    // Nat.mod is total: Nat.mod a 0 = a
    let mod_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(
        t.translate_expr(&mod_expr).unwrap(),
        "(ite (> 3 0) (mod 10 3) 10)"
    );
}

#[test]
fn test_translate_int_ediv_is_total() {
    let mut t = SmtLibTranslator::new();
    // Lean's Euclidean quotient is total, unlike unconstrained SMT div-by-zero.
    let div_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.ediv"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(
        t.translate_expr(&div_expr).unwrap(),
        "(ite (= 3 0) 0 (div 10 3))"
    );
}

#[test]
fn test_translate_int_emod_preserves_the_dividend_at_zero() {
    let mut t = SmtLibTranslator::new();
    // Lean's Euclidean remainder preserves the dividend for divisor zero.
    let mod_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.emod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(
        t.translate_expr(&mod_expr).unwrap(),
        "(ite (= 3 0) 10 (mod 10 3))"
    );
}

#[test]
fn test_explicit_t_rounding_uses_sign_magnitudes() {
    let mut t = SmtLibTranslator::new();
    let expr = Expr::apps(
        Expr::const_(Name::from_string("Int.div"), vec![]),
        [Expr::nat_lit(7), Expr::nat_lit(2)],
    );
    let text = t
        .translate_expr(&expr)
        .expect("translate explicit T-division");
    assert!(text.starts_with("(ite (= 2 0) 0 "), "{text}");
    assert!(
        text.contains("(div (ite (< 7 0) (- 7) 7) (ite (< 2 0) (- 2) 2))"),
        "{text}"
    );
    assert_ne!(text, "(ite (= 2 0) 0 (div 7 2))");
}
