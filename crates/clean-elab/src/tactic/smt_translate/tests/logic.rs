// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Boolean connective, equality variant, and comparison operator tests.

use super::*;

// ===================================================================
// Boolean connectives
// ===================================================================

#[test]
fn test_translate_and() {
    let mut t = SmtLibTranslator::new();
    let a = Expr::const_(Name::from_string("True"), vec![]);
    let b = Expr::const_(Name::from_string("False"), vec![]);
    let and_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
        b,
    );
    assert_eq!(t.translate_expr(&and_expr).unwrap(), "(and true false)");
}

#[test]
fn test_translate_or() {
    let mut t = SmtLibTranslator::new();
    let a = Expr::const_(Name::from_string("True"), vec![]);
    let b = Expr::const_(Name::from_string("False"), vec![]);
    let or_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a),
        b,
    );
    assert_eq!(t.translate_expr(&or_expr).unwrap(), "(or true false)");
}

#[test]
fn test_translate_not() {
    let mut t = SmtLibTranslator::new();
    let a = Expr::const_(Name::from_string("True"), vec![]);
    let not_expr = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a);
    assert_eq!(t.translate_expr(&not_expr).unwrap(), "(not true)");
}

// ===================================================================
// Equality variants
// ===================================================================

#[test]
fn test_translate_ne_skips_type_arg() {
    let mut t = SmtLibTranslator::new();
    // @Ne Nat 1 2 → (not (= 1 2))
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let ne_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            Expr::nat_lit(1),
        ),
        Expr::nat_lit(2),
    );
    assert_eq!(t.translate_expr(&ne_expr).unwrap(), "(not (= 1 2))");
}

#[test]
fn test_translate_beq() {
    let mut t = SmtLibTranslator::new();
    // BEq.beq with last-2-args extraction
    let inst = Expr::const_(Name::from_string("instBEqNat"), vec![]);
    let beq_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("BEq.beq"), vec![]), inst),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(4),
    );
    assert_eq!(t.translate_expr(&beq_expr).unwrap(), "(= 3 4)");
}

#[test]
fn test_translate_iff() {
    let mut t = SmtLibTranslator::new();
    let a = Expr::const_(Name::from_string("True"), vec![]);
    let b = Expr::const_(Name::from_string("False"), vec![]);
    let iff_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), a),
        b,
    );
    assert_eq!(
        t.translate_expr(&iff_expr).unwrap(),
        "(and (=> true false) (=> false true))"
    );
}

// ===================================================================
// Comparison operators
// ===================================================================

#[test]
fn test_translate_le() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instLENat"), vec![]);
    let le_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LE.le"), vec![]), nat_ty),
                inst,
            ),
            Expr::nat_lit(3),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(t.translate_expr(&le_expr).unwrap(), "(<= 3 5)");
}

#[test]
fn test_translate_gt() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instGTNat"), vec![]);
    let gt_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("GT.gt"), vec![]), nat_ty),
                inst,
            ),
            Expr::nat_lit(7),
        ),
        Expr::nat_lit(2),
    );
    assert_eq!(t.translate_expr(&gt_expr).unwrap(), "(> 7 2)");
}

#[test]
fn test_translate_ge() {
    let mut t = SmtLibTranslator::new();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inst = Expr::const_(Name::from_string("instGENat"), vec![]);
    let ge_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("GE.ge"), vec![]), nat_ty),
                inst,
            ),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(5),
    );
    assert_eq!(t.translate_expr(&ge_expr).unwrap(), "(>= 5 5)");
}
