// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor-form Real coercions and comparison tests (#2794).

use super::*;

// -- Family-local helpers --

fn real_of_int_neg_succ(n: u64) -> Expr {
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    );
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn real_lt(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let inst = Expr::const_(Name::from_string("instLTReal"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![]), real_ty),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

fn real_le(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let inst = Expr::const_(Name::from_string("instLEReal"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), vec![]), real_ty),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

// -- Tests --

#[test]
fn test_translate_real_ofnat_concrete() {
    let mut t = SmtLibTranslator::new();
    // Real.ofNat(3) → 3.0
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "3.0");
}

#[test]
fn test_translate_real_ofnat_zero() {
    let mut t = SmtLibTranslator::new();
    // Real.ofNat(0) → 0.0
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "0.0");
}

#[test]
fn test_translate_real_ofint_positive() {
    let mut t = SmtLibTranslator::new();
    // Real.ofInt(Int.ofNat(5)) → 5.0
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "5.0");
}

#[test]
fn test_translate_real_ofint_negative() {
    let mut t = SmtLibTranslator::new();
    // Real.ofInt(Int.negSucc(0)) → (- 1.0)  [negSucc(0) = -(0+1) = -1]
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "(- 1.0)");
}

#[test]
fn test_translate_real_ofint_negative_two() {
    let mut t = SmtLibTranslator::new();
    // Real.ofInt(Int.negSucc(1)) → (- 2.0)  [negSucc(1) = -(1+1) = -2]
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(1),
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "(- 2.0)");
}

#[test]
fn test_translate_real_ofnat_non_concrete_fails() {
    let mut t = SmtLibTranslator::new();
    // Real.ofNat(fvar) → UnsupportedExpr (fail closed)
    let fvar = Expr::fvar(FVarId::new(42));
    let expr = Expr::app(Expr::const_(Name::from_string("Real.ofNat"), vec![]), fvar);
    assert!(t.translate_expr(&expr).is_err());
}

#[test]
fn test_translate_real_ofint_non_concrete_fails() {
    let mut t = SmtLibTranslator::new();
    // Real.ofInt(fvar) → UnsupportedExpr (fail closed)
    let fvar = Expr::fvar(FVarId::new(42));
    let expr = Expr::app(Expr::const_(Name::from_string("Real.ofInt"), vec![]), fvar);
    assert!(t.translate_expr(&expr).is_err());
}

#[test]
fn test_translate_real_ofnat_no_bool_declaration() {
    let mut t = SmtLibTranslator::new();
    // Real.ofNat(1) should NOT produce a Bool declaration
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(1),
    );
    t.translate_expr(&expr).unwrap();
    assert!(
        !t.declarations().iter().any(|d| d.contains("Bool")),
        "Real.ofNat should not declare Bool: {:?}",
        t.declarations()
    );
}

#[test]
fn test_translate_real_ofint_with_bare_nat_lit() {
    let mut t = SmtLibTranslator::new();
    // Real.ofInt(NatLit(7)) → 7.0  (bare Nat literal as non-negative Int)
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        Expr::nat_lit(7),
    );
    assert_eq!(t.translate_expr(&expr).unwrap(), "7.0");
}

#[test]
fn test_translate_real_lt_with_constructor_endpoints() {
    let mut t = SmtLibTranslator::new();
    let expr = real_lt(real_of_nat(0), real_of_nat(1));

    assert_eq!(t.translate_expr(&expr).unwrap(), "(< 0.0 1.0)");
    assert!(
        t.declarations().is_empty(),
        "supported Real constructor comparisons should not declare opaque Bool placeholders: {:?}",
        t.declarations()
    );
}

#[test]
fn test_translate_real_le_with_negative_constructor_endpoint() {
    let mut t = SmtLibTranslator::new();
    let expr = real_le(real_of_int_neg_succ(0), real_of_nat(0));

    assert_eq!(t.translate_expr(&expr).unwrap(), "(<= (- 1.0) 0.0)");
    assert!(
        t.declarations().is_empty(),
        "supported Real constructor comparisons should stay on the arithmetic surface: {:?}",
        t.declarations()
    );
}
