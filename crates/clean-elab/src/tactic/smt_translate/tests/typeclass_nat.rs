// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HSub/HDiv/HMod typeclass dispatch with Nat type arg (#2452).

use super::*;

#[test]
fn test_hsub_nat_uses_monus() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let expr = make_hsub(nat_ty, Expr::nat_lit(10), Expr::nat_lit(3));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (>= 10 3) (- 10 3) 0)"
    );
}

#[test]
fn test_hsub_int_uses_plain() {
    let mut t = SmtLibTranslator::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let expr = make_hsub(int_ty, Expr::nat_lit(3), Expr::nat_lit(10));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(- 3 10)");
}

#[test]
fn test_hdiv_nat_uses_total() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let expr = make_hdiv(nat_ty, Expr::nat_lit(10), Expr::nat_lit(3));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (> 3 0) (div 10 3) 0)"
    );
}

#[test]
fn test_hdiv_int_uses_plain() {
    let mut t = SmtLibTranslator::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let expr = make_hdiv(int_ty, Expr::nat_lit(10), Expr::nat_lit(3));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(div 10 3)");
}

#[test]
fn test_hmod_nat_uses_total() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let expr = make_hmod(nat_ty, Expr::nat_lit(10), Expr::nat_lit(3));
    assert_eq!(
        t.translate_expr(&expr).unwrap(),
        "(ite (> 3 0) (mod 10 3) 10)"
    );
}

#[test]
fn test_hmod_int_uses_plain() {
    let mut t = SmtLibTranslator::new();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let expr = make_hmod(int_ty, Expr::nat_lit(10), Expr::nat_lit(3));
    assert_eq!(t.translate_expr(&expr).unwrap(), "(mod 10 3)");
}
