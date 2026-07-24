// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::translate::ExprKey;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

#[test]
fn test_expr_key_const_different_levels_distinct() {
    // @Eq.{0} and @Eq.{1} must produce different ExprKeys (#2109)
    let eq_name = Name::from_string("Eq");
    let eq_level0 = Expr::const_(eq_name.clone(), vec![Level::zero()]);
    let eq_level1 = Expr::const_(eq_name, vec![Level::succ(Level::zero())]);

    let key0 = ExprKey::from_expr(&eq_level0).unwrap();
    let key1 = ExprKey::from_expr(&eq_level1).unwrap();

    assert_ne!(
        key0, key1,
        "same-name constants at different universe levels must have distinct ExprKeys"
    );
}

#[test]
fn test_expr_key_const_same_levels_equal() {
    let name = Name::from_string("Eq");
    let e1 = Expr::const_(name.clone(), vec![Level::zero()]);
    let e2 = Expr::const_(name, vec![Level::zero()]);

    let key1 = ExprKey::from_expr(&e1).unwrap();
    let key2 = ExprKey::from_expr(&e2).unwrap();

    assert_eq!(
        key1, key2,
        "same-name constants at same universe level must be equal"
    );
}

#[test]
fn test_expr_key_lam_different_binder_info_distinct() {
    // λ {x : A} => body vs λ (x : A) => body must be distinct (#2109)
    // Use Const (not Sort/type_()) since from_expr returns None for Sort
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = Expr::bvar(0);

    let lam_implicit = Expr::lam(BinderInfo::Implicit, ty.clone(), body.clone());
    let lam_explicit = Expr::lam(BinderInfo::Default, ty, body);

    let key_impl = ExprKey::from_expr(&lam_implicit).unwrap();
    let key_expl = ExprKey::from_expr(&lam_explicit).unwrap();

    assert_ne!(
        key_impl, key_expl,
        "lambdas with different binder info must have distinct ExprKeys"
    );
}

#[test]
fn test_expr_key_pi_different_binder_info_distinct() {
    // Π {x : A} → body vs Π (x : A) → body must be distinct (#2109)
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = Expr::bvar(0);

    let pi_implicit = Expr::pi(BinderInfo::Implicit, ty.clone(), body.clone());
    let pi_explicit = Expr::pi(BinderInfo::Default, ty, body);

    let key_impl = ExprKey::from_expr(&pi_implicit).unwrap();
    let key_expl = ExprKey::from_expr(&pi_explicit).unwrap();

    assert_ne!(
        key_impl, key_expl,
        "pi types with different binder info must have distinct ExprKeys"
    );
}
