// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for quantifier classification: Forall, Exists (including MData predicate stripping
//! and eta-contracted predicates).

use super::*;
use clean_kernel::ExprKind;

#[test]
fn test_classify_forall_via_pi() {
    let nat = mk_const("Nat");
    let bvar0 = Expr::bvar(0);
    let body = app3(
        mk_const_u("Eq", vec![Level::succ(Level::zero())]),
        nat.clone(),
        bvar0.clone(),
        bvar0,
    );
    let pi = Expr::pi(clean_kernel::BinderInfo::Default, nat.clone(), body.clone());
    match classify_expr(&pi) {
        LogicalForm::Forall {
            binder_type,
            body: b,
        } => {
            assert_eq!(binder_type, nat);
            assert_eq!(b, body);
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn test_classify_nested_pi_with_outer_binder_reference_as_implies() {
    let nat = mk_const("Nat");
    let inner_codomain = app3(
        mk_const_u("Eq", vec![Level::succ(Level::zero())]),
        nat.clone(),
        Expr::bvar(1),
        Expr::bvar(1),
    );
    let inner_pi = Expr::pi(
        clean_kernel::BinderInfo::Default,
        nat.clone(),
        inner_codomain.clone(),
    );
    let outer_pi = Expr::pi(
        clean_kernel::BinderInfo::Default,
        nat.clone(),
        inner_pi.clone(),
    );

    let inner_body = match classify_expr(&outer_pi) {
        LogicalForm::Forall { binder_type, body } => {
            assert_eq!(binder_type, nat);
            assert_eq!(body, inner_pi);
            body
        }
        other => panic!("expected outer Forall, got {other:?}"),
    };

    match classify_expr(&inner_body) {
        LogicalForm::Implies(antecedent, consequent) => {
            assert_eq!(antecedent, nat);
            assert_eq!(consequent, inner_codomain);
        }
        other => panic!("expected inner Implies, got {other:?}"),
    }
}

#[test]
fn test_classify_exists() {
    let nat = mk_const("Nat");
    let bvar0 = Expr::bvar(0);
    let body = app3(
        mk_const_u("Eq", vec![Level::succ(Level::zero())]),
        nat.clone(),
        bvar0.clone(),
        bvar0,
    );
    let lam = Expr::lam(clean_kernel::BinderInfo::Default, nat.clone(), body.clone());
    match classify_expr(&app2(mk_const("Exists"), nat.clone(), lam)) {
        LogicalForm::Exists {
            binder_type,
            body: b,
        } => {
            assert_eq!(binder_type, nat);
            assert_eq!(b, body);
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

#[test]
fn test_classify_exists_mdata_predicate() {
    let nat = mk_const("Nat");
    let bvar0 = Expr::bvar(0);
    let body = app3(
        mk_const_u("Eq", vec![Level::succ(Level::zero())]),
        nat.clone(),
        bvar0.clone(),
        bvar0,
    );
    let lam = Expr::lam(clean_kernel::BinderInfo::Default, nat.clone(), body.clone());
    let mdata_lam = Expr::mdata(vec![], lam);
    match classify_expr(&app2(mk_const("Exists"), nat.clone(), mdata_lam)) {
        LogicalForm::Exists {
            binder_type,
            body: b,
        } => {
            assert_eq!(binder_type, nat);
            assert_eq!(b, body);
        }
        other => panic!("expected Exists through MData, got {other:?}"),
    }
}

#[test]
fn test_classify_exists_eta_contracted_const() {
    // Exists Nat even — predicate is a constant, not a lambda
    let nat = mk_const("Nat");
    let even = mk_const("even");
    let expr = app2(mk_const("Exists"), nat.clone(), even.clone());
    match classify_expr(&expr) {
        LogicalForm::Exists { binder_type, body } => {
            assert_eq!(binder_type, nat);
            // Body should be App(even, BVar(0)) — eta-expanded
            match body.kind() {
                ExprKind::App(f, arg) => {
                    assert_eq!(**f, even, "function should be the predicate");
                    assert_eq!(**arg, Expr::bvar(0), "argument should be BVar(0)");
                }
                other => panic!("expected App(even, BVar(0)), got {other:?}"),
            }
        }
        other => panic!("expected Exists for eta-contracted predicate, got {other:?}"),
    }
}

#[test]
fn test_classify_exists_eta_contracted_fvar() {
    // Exists α P where P is an FVar
    let alpha = mk_const("Nat");
    let p = mk_fvar(42);
    let expr = app2(mk_const("Exists"), alpha.clone(), p.clone());
    match classify_expr(&expr) {
        LogicalForm::Exists { binder_type, body } => {
            assert_eq!(binder_type, alpha);
            match body.kind() {
                ExprKind::App(f, arg) => {
                    assert_eq!(**f, p, "function should be the predicate FVar");
                    assert_eq!(**arg, Expr::bvar(0), "argument should be BVar(0)");
                }
                other => panic!("expected App(P, BVar(0)), got {other:?}"),
            }
        }
        other => panic!("expected Exists for FVar predicate, got {other:?}"),
    }
}
