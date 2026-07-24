// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for comparison operator classification:
//! Lt, Le, Gt, Ge in direct, typeclass, and bare alias forms.

use super::*;

#[test]
fn test_classify_comparison_lt() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Int.lt"), a.clone(), b.clone())) {
        LogicalForm::Lt { ty, lhs, rhs } => {
            assert_eq!(ty, mk_const("Int"));
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Lt, got {other:?}"),
    }
}

#[test]
fn test_classify_comparison_le_typeclass() {
    // @LE.le Nat instLENat a b — 4 args: [type, instance, lhs, rhs]
    let nat = mk_const("Nat");
    let inst = mk_const("instLENat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let le = Expr::app(
        Expr::app(
            Expr::app(Expr::app(mk_const("LE.le"), nat.clone()), inst),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&le) {
        LogicalForm::Le { ty, lhs, rhs } => {
            assert_eq!(ty, nat);
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Le, got {other:?}"),
    }
}

#[test]
fn test_classify_comparison_gt_ge() {
    let nat = mk_const("Nat");
    let inst = mk_const("instGTNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let gt = Expr::app(
        Expr::app(
            Expr::app(Expr::app(mk_const("GT.gt"), nat.clone()), inst),
            a.clone(),
        ),
        b.clone(),
    );
    assert!(matches!(classify_expr(&gt), LogicalForm::Gt { .. }));

    let ge = Expr::app(
        Expr::app(
            Expr::app(Expr::app(mk_const("GE.ge"), nat), mk_const("instGENat")),
            a,
        ),
        b,
    );
    assert!(matches!(classify_expr(&ge), LogicalForm::Ge { .. }));
}

#[test]
fn test_classify_bare_comparison_aliases_no_type() {
    // Bare 2-arg aliases (lt, le, gt, ge) without type/instance args are partial
    // applications with unknown type — should NOT be classified as typed comparisons (#2301).
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    assert!(matches!(
        classify_expr(&app2(mk_const("lt"), a.clone(), b.clone())),
        LogicalForm::Atom(_)
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("le"), a.clone(), b.clone())),
        LogicalForm::Atom(_)
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("gt"), a.clone(), b.clone())),
        LogicalForm::Atom(_)
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("ge"), a.clone(), b.clone())),
        LogicalForm::Atom(_)
    ));
}

#[test]
fn test_classify_nat_int_gt_ge() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    match classify_expr(&app2(mk_const("Nat.gt"), a.clone(), b.clone())) {
        LogicalForm::Gt { ty, .. } => assert_eq!(ty, mk_const("Nat")),
        other => panic!("expected Gt, got {other:?}"),
    }
    match classify_expr(&app2(mk_const("Int.ge"), a.clone(), b.clone())) {
        LogicalForm::Ge { ty, .. } => assert_eq!(ty, mk_const("Int")),
        other => panic!("expected Ge, got {other:?}"),
    }
}

#[test]
fn test_classify_direct_real_comparison_heads() {
    let a = mk_fvar(1);
    let b = mk_fvar(2);

    match classify_expr(&app2(mk_const("Real.lt"), a.clone(), b.clone())) {
        LogicalForm::Lt { ty, lhs, rhs } => {
            assert_eq!(ty, mk_const("Real"));
            assert_eq!(lhs, a.clone());
            assert_eq!(rhs, b.clone());
        }
        other => panic!("expected direct Real.lt to classify as Lt, got {other:?}"),
    }

    match classify_expr(&app2(mk_const("Real.le"), a.clone(), b.clone())) {
        LogicalForm::Le { ty, lhs, rhs } => {
            assert_eq!(ty, mk_const("Real"));
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected direct Real.le to classify as Le, got {other:?}"),
    }
}

#[test]
fn test_is_theory_const_name_includes_direct_real_comparison_heads() {
    assert!(is_theory_const_name("Real.lt"));
    assert!(is_theory_const_name("Real.le"));
}

#[test]
fn test_classify_bare_typeclass_comparison_all_dotted_forms_not_classified() {
    // Bare 2-arg dotted typeclass forms (LT.lt, LE.le, GT.gt, GE.ge) without
    // type/instance args are partial applications — should return Atom (#2301).
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    for name in ["LT.lt", "LE.le", "GT.gt", "GE.ge"] {
        assert!(
            matches!(
                classify_expr(&app2(mk_const(name), a.clone(), b.clone())),
                LogicalForm::Atom(_)
            ),
            "{name} with 2 args should fall through to Atom"
        );
    }
}
