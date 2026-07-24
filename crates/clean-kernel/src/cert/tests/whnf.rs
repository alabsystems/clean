// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WHNF reduction tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_whnf_app_beta() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    // (λ x. x) y → y
    let id = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let arg = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let app = Expr::app(id, arg.clone());

    let result = verifier.whnf(&app);
    assert_eq!(result, arg);
}

#[test]
fn test_whnf_let_zeta() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    // let x := v in x → v
    let val = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let let_expr = Expr::let_named(
        Name::anon(),
        Expr::from_kind(ExprKind::Sort(Level::zero())), // type
        val.clone(),                                    // value
        Expr::from_kind(ExprKind::BVar(0)),             // body = x
        false,
    );

    let result = verifier.whnf(&let_expr);
    assert_eq!(result, val);
}

#[test]
fn test_whnf_const_unfold() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Define a constant that unfolds
    let val = Expr::from_kind(ExprKind::Sort(Level::zero()));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("myProp"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        value: val.clone(),
        is_reducible: true,
    })
    .unwrap();

    let verifier = CertVerifier::new(&env);
    let const_expr = Expr::const_(Name::from_string("myProp"), vec![]);

    let result = verifier.whnf(&const_expr);
    assert_eq!(result, val);
}

#[test]
fn test_whnf_non_reducible() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    // Sort should not reduce
    let sort = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let result = verifier.whnf(&sort);
    assert_eq!(result, sort);
}

// --- cert_name and expr_name tests (for Display mutations) ---
