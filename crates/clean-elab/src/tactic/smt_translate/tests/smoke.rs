// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minimal smoke tests: translator still works at all.

use super::*;

#[test]
fn test_translate_nat_literal() {
    let mut translator = SmtLibTranslator::new();
    let expr = Expr::nat_lit(42);
    let result = translator.translate_expr(&expr).unwrap();
    assert_eq!(result, "42");
}

#[test]
fn test_translate_true_false() {
    let mut translator = SmtLibTranslator::new();

    let t = Expr::const_(Name::from_string("True"), vec![]);
    assert_eq!(translator.translate_expr(&t).unwrap(), "true");

    let f = Expr::const_(Name::from_string("False"), vec![]);
    assert_eq!(translator.translate_expr(&f).unwrap(), "false");
}

#[test]
fn test_translate_eq_skips_type_arg() {
    let mut translator = SmtLibTranslator::new();

    // @Eq Nat a b → (= a b)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            a,
        ),
        b,
    );

    let result = translator.translate_expr(&eq_expr).unwrap();
    assert_eq!(result, "(= 1 2)");
}

#[test]
fn test_translate_lt_last_two_args() {
    let mut translator = SmtLibTranslator::new();

    // @LT.lt Nat inst a b → (< a b), skipping type + instance
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instLtNat"), vec![]);
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let lt_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![]), nat_ty),
                inst,
            ),
            a,
        ),
        b,
    );

    let result = translator.translate_expr(&lt_expr).unwrap();
    assert_eq!(result, "(< 3 5)");
}

#[test]
fn test_translate_add() {
    let mut translator = SmtLibTranslator::new();

    // @HAdd.hAdd Nat Nat Nat instHAddNat a b → (+ a b)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instHAddNat"), vec![]);
    let a = Expr::nat_lit(10);
    let b = Expr::nat_lit(20);
    // 6 args: 3 type args + 1 instance + 2 operands
    let add_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("HAdd.hAdd"), vec![]),
                            nat_ty.clone(),
                        ),
                        nat_ty.clone(),
                    ),
                    nat_ty,
                ),
                inst,
            ),
            a,
        ),
        b,
    );

    let result = translator.translate_expr(&add_expr).unwrap();
    assert_eq!(result, "(+ 10 20)");
}

#[test]
fn test_build_problem() {
    let mut translator = SmtLibTranslator::new();

    // Create a simple problem: assert (< fvar_0 5)
    let fvar_id = FVarId::new(42);
    let fvar = Expr::fvar(fvar_id);
    translator.register_fvar(fvar_id, SmtSort::Int, fvar.clone());
    let five = Expr::nat_lit(5);
    let lt = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), fvar),
        five,
    );

    let assertion = translator.translate_expr(&lt).unwrap();
    let problem = translator.build_problem(&assertion, "QF_LIA");

    assert!(problem.contains("(set-logic QF_LIA)"));
    assert!(problem.contains("(set-option :produce-proofs true)"));
    assert!(problem.contains("(declare-const fvar_42 Int)"));
    assert!(problem.contains("(assert (< fvar_42 5))"));
    assert!(problem.contains("(check-sat)"));
    assert!(problem.contains("(get-proof)"));
}
