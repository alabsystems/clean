// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builder equality tests: def_eq and structural_eq through the builder's
//! simplified WHNF (beta, zeta, delta, mdata/squash only).

use std::sync::Arc;

use crate::cert::builder::CertBuilder;
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, ZFCSetExpr};
use crate::level::Level;
use crate::name::Name;

#[test]
fn test_builder_def_eq_pi_domain_needs_zeta_reduction() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let let_prop = Expr::let_named(
        Name::anon(),
        prop.clone(),
        prop.clone(),
        Expr::bvar(0),
        false,
    );
    let pi_with_let = Expr::pi(BinderInfo::Default, let_prop, prop.clone());
    let pi_direct = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    assert!(builder.def_eq(&pi_with_let, &pi_direct));
    assert!(builder.def_eq(&pi_direct, &pi_with_let));
}

#[test]
fn test_builder_def_eq_app_arg_needs_beta_reduction() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let f = Expr::from_kind(ExprKind::FVar(FVarId(1)));
    let id_lam = Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0));
    let beta_redex = Expr::app(id_lam, prop.clone());
    let app_with_redex = Expr::app(f.clone(), beta_redex);
    let app_direct = Expr::app(f, prop);

    assert!(builder.def_eq(&app_with_redex, &app_direct));
}

#[test]
fn test_builder_def_eq_lam_body_needs_reduction() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let let_body = Expr::let_named(
        Name::anon(),
        prop.clone(),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    let lam_with_let = Expr::lam(BinderInfo::Default, prop.clone(), let_body);
    let lam_direct = Expr::lam(BinderInfo::Default, prop, Expr::bvar(0));

    assert!(builder.def_eq(&lam_with_let, &lam_direct));
}

#[test]
fn test_builder_def_eq_eta_expansion_lam_vs_non_lam() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let f = Expr::from_kind(ExprKind::FVar(FVarId(42)));
    let f_lifted = f.lift_from(0, 1);
    let body = Expr::app(f_lifted, Expr::bvar(0));
    let lam_f_x = Expr::lam(BinderInfo::Default, prop, body);

    assert!(builder.def_eq(&lam_f_x, &f));
    assert!(builder.def_eq(&f, &lam_f_x));
}

#[test]
fn test_builder_def_eq_binder_info_irrelevant_pi() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let pi_default = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
    let pi_implicit = Expr::pi(BinderInfo::Implicit, prop.clone(), prop);

    assert!(builder.def_eq(&pi_default, &pi_implicit));
}

#[test]
fn test_builder_def_eq_sort_levels_normalize() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let lhs = Expr::from_kind(ExprKind::Sort(Level::max(u.clone(), v.clone())));
    let rhs = Expr::from_kind(ExprKind::Sort(Level::max(v, u)));

    assert!(builder.def_eq(&lhs, &rhs));
}

#[test]
fn test_builder_structural_eq_zfc_set_pair_uses_structural_helper() {
    let env = crate::env::Environment::new();
    let builder = CertBuilder::new(&env);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let lhs = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        Arc::new(prop.clone()),
        Arc::new(prop.clone()),
    )));
    let rhs = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        Arc::new(prop.clone()),
        Arc::new(prop),
    )));

    assert!(builder.structural_eq(&lhs, &rhs));
}
