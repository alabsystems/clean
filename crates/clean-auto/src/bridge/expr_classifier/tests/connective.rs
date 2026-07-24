// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for propositional connective classification:
//! Eq, Ne, And, Or, Not, Iff, True, False, BEq, MData stripping, Implies, Atom.

use super::*;

#[test]
fn test_classify_eq() {
    let ty = mk_const("Nat");
    let lhs = mk_fvar(1);
    let rhs = mk_fvar(2);
    let expr = app3(mk_const("Eq"), ty.clone(), lhs.clone(), rhs.clone());
    match classify_expr(&expr) {
        LogicalForm::Eq {
            ty: t,
            lhs: l,
            rhs: r,
        } => {
            assert_eq!(t, ty);
            assert_eq!(l, lhs);
            assert_eq!(r, rhs);
        }
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn test_classify_ne() {
    let ty = mk_const("Int");
    let lhs = mk_fvar(1);
    let rhs = mk_fvar(2);
    let expr = app3(mk_const("Ne"), ty.clone(), lhs.clone(), rhs.clone());
    match classify_expr(&expr) {
        LogicalForm::Neq {
            ty: t,
            lhs: l,
            rhs: r,
        } => {
            assert_eq!(t, ty);
            assert_eq!(l, lhs);
            assert_eq!(r, rhs);
        }
        other => panic!("expected Neq, got {other:?}"),
    }
}

#[test]
fn test_classify_and_or_not() {
    let p = mk_fvar(1);
    let q = mk_fvar(2);
    assert!(matches!(
        classify_expr(&app2(mk_const("And"), p.clone(), q.clone())),
        LogicalForm::And(..)
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("Or"), p.clone(), q.clone())),
        LogicalForm::Or(..)
    ));
    assert!(matches!(
        classify_expr(&Expr::app(mk_const("Not"), p.clone())),
        LogicalForm::Not(..)
    ));
}

#[test]
fn test_classify_bool_variants() {
    let p = mk_fvar(1);
    let q = mk_fvar(2);
    assert!(matches!(
        classify_expr(&app2(mk_const("Bool.and"), p.clone(), q.clone())),
        LogicalForm::And(..)
    ));
    assert!(matches!(
        classify_expr(&app2(mk_const("Bool.or"), p.clone(), q.clone())),
        LogicalForm::Or(..)
    ));
    assert!(matches!(
        classify_expr(&Expr::app(mk_const("Bool.not"), p.clone())),
        LogicalForm::Not(..)
    ));
}

#[test]
fn test_classify_iff() {
    let p = mk_fvar(1);
    let q = mk_fvar(2);
    assert!(matches!(
        classify_expr(&app2(mk_const("Iff"), p, q)),
        LogicalForm::Iff(..)
    ));
}

#[test]
fn test_classify_true_false() {
    assert!(matches!(
        classify_expr(&mk_const("True")),
        LogicalForm::True
    ));
    assert!(matches!(
        classify_expr(&mk_const("False")),
        LogicalForm::False
    ));
}

#[test]
fn test_classify_mdata_stripping() {
    let and_expr = app2(mk_const("And"), mk_fvar(1), mk_fvar(2));
    let mdata_expr = Expr::mdata(vec![], and_expr);
    assert!(matches!(classify_expr(&mdata_expr), LogicalForm::And(..)));
}

#[test]
fn test_classify_implies_via_pi() {
    let p = mk_const("True");
    let q = mk_const("False");
    let pi = Expr::pi(clean_kernel::BinderInfo::Default, p.clone(), q.clone());
    match classify_expr(&pi) {
        LogicalForm::Implies(a, b) => {
            assert_eq!(a, p);
            assert_eq!(b, q);
        }
        other => panic!("expected Implies, got {other:?}"),
    }
}

#[test]
fn test_classify_beq() {
    let nat = mk_const("Nat");
    let inst = mk_const("instBEqNat");
    let a = mk_fvar(1);
    let b = mk_fvar(2);
    let beq = Expr::app(
        Expr::app(
            Expr::app(Expr::app(mk_const("BEq.beq"), nat), inst),
            a.clone(),
        ),
        b.clone(),
    );
    match classify_expr(&beq) {
        LogicalForm::Eq { lhs, rhs, .. } => {
            assert_eq!(lhs, a);
            assert_eq!(rhs, b);
        }
        other => panic!("expected Eq (from BEq.beq), got {other:?}"),
    }
}

#[test]
fn test_classify_atom_fallback() {
    assert!(matches!(
        classify_expr(&Expr::app(mk_const("MyCustomPred"), mk_fvar(1))),
        LogicalForm::Atom(..)
    ));
    assert!(matches!(classify_expr(&mk_fvar(42)), LogicalForm::Atom(..)));
}
