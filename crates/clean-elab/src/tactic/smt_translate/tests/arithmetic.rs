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
fn test_translate_int_div_plain() {
    let mut t = SmtLibTranslator::new();
    // Int.div has standard SMT-LIB semantics (undefined for div by 0)
    let div_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.div"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(t.translate_expr(&div_expr).unwrap(), "(div 10 3)");
}

#[test]
fn test_translate_int_mod_plain() {
    let mut t = SmtLibTranslator::new();
    // Int.mod has standard SMT-LIB semantics
    let mod_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.mod"), vec![]),
            Expr::nat_lit(10),
        ),
        Expr::nat_lit(3),
    );
    assert_eq!(t.translate_expr(&mod_expr).unwrap(), "(mod 10 3)");
}
