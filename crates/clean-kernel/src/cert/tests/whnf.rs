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

/// leanprover/lean4#14632, in the certificate checker's own reducer: a
/// projection extracts a field only from a constructor of the structure it
/// names. `CertA`/`CertB` are one-field `Prop` structures; the same-name
/// projection is the control.
#[test]
fn cert_projection_of_a_foreign_structure_constructor_stays_stuck() {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = empty_env();
    for s in ["CertA", "CertB"] {
        let name = Name::from_string(s);
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: name.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string(&format!("{s}.mk")),
                    type_: Expr::arrow(Expr::prop(), Expr::const_(name, vec![])),
                }],
            }],
        })
        .unwrap_or_else(|e| panic!("env setup: structure {s}: {e:?}"));
    }
    let verifier = CertVerifier::new(&env);
    let field = Expr::const_(Name::from_string("True"), vec![]);
    let b_mk = Expr::app(
        Expr::const_(Name::from_string("CertB.mk"), vec![]),
        field.clone(),
    );
    let own = Expr::proj(Name::from_string("CertB"), 0, b_mk.clone());
    assert_eq!(
        verifier.whnf(&own),
        field,
        "control: CertB.0 (CertB.mk True)"
    );
    let foreign = Expr::proj(Name::from_string("CertA"), 0, b_mk);
    assert_eq!(
        verifier.whnf(&foreign),
        foreign,
        "CertA.0 (CertB.mk True) must stay stuck"
    );
}
