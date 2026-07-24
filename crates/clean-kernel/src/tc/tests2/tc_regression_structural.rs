// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TC regression tests: structural patterns (projection, proof irrelevance,
//! eta expansion, noConfusion).
//!
//! These tests cover patterns that previously failed in .olean loading:
//! projection through structures, proof irrelevance through delta, eta
//! expansion, and noConfusion value type-checking (#3208).

use super::support::{make_nat_env, make_nat_env_with_eq};
use super::*;
use crate::env::{ConstantInfo, Declaration, Reducibility};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Add a reducible definition to the environment.
fn add_reducible(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), true);
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn cst_u(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

// ============================================================================
// Projection through structures
// ============================================================================

/// Regression: projection of a constructor application must reduce.
#[test]
fn test_regression_projection_simple_pair() {
    let mut env = Environment::new();

    let pair = Name::from_string("MyPair");
    let pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(cst_u("MyPair", vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("MyPair.mk"),
                type_: mk_type,
            }],
        }],
    };
    env.add_inductive(decl)
        .expect("invariant: MyPair registers");

    let tc = TypeChecker::new(&env);

    let mk_val = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cst("MyPair.mk"), Expr::type_()), Expr::type_()),
            Expr::prop(),
        ),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
    );

    let proj0 = Expr::proj(pair.clone(), 0, mk_val.clone());
    assert_eq!(
        tc.whnf(&proj0),
        Expr::prop(),
        "Projection .0 should yield Prop"
    );

    let proj1 = Expr::proj(pair, 1, mk_val);
    assert_eq!(
        tc.whnf(&proj1),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
        "Projection .1 should yield Sort 2"
    );
}

/// Regression: projection through a delta-unfolded definition.
#[test]
fn test_regression_projection_through_delta() {
    let mut env = Environment::new();

    let pair = Name::from_string("DPair");
    let pair_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(cst_u("DPair", vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: pair_type,
            constructors: vec![Constructor {
                name: Name::from_string("DPair.mk"),
                type_: mk_type,
            }],
        }],
    };
    env.add_inductive(decl).expect("invariant: DPair registers");

    let mk_val = Expr::app(
        Expr::app(
            Expr::app(Expr::app(cst("DPair.mk"), Expr::type_()), Expr::type_()),
            Expr::prop(),
        ),
        Expr::type_(),
    );

    let pair_ty = Expr::app(Expr::app(cst("DPair"), Expr::type_()), Expr::type_());
    add_reducible(&mut env, "myPair", pair_ty, mk_val);

    let tc = TypeChecker::new(&env);

    let proj = Expr::proj(pair, 0, cst("myPair"));
    assert_eq!(
        tc.whnf(&proj),
        Expr::prop(),
        "Projection through delta-unfolded pair should yield Prop"
    );
}

// ============================================================================
// Proof irrelevance
// ============================================================================

/// Regression: proof irrelevance through delta-unfolded propositions.
#[test]
fn test_regression_proof_irrelevance_through_delta() {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("invariant: R axiom registers");

    add_reducible(&mut env, "P", Expr::prop(), cst("R"));
    add_reducible(&mut env, "Q", Expr::prop(), cst("R"));

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p1"),
        level_params: vec![],
        type_: cst("P"),
    })
    .expect("invariant: p1 axiom registers");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p2"),
        level_params: vec![],
        type_: cst("Q"),
    })
    .expect("invariant: p2 axiom registers");

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&cst("p1"), &cst("p2")),
        "Proof irrelevance should work through delta: P := R, Q := R"
    );
}

/// Regression: proof irrelevance must NOT apply for Type-level terms.
#[test]
fn test_regression_proof_irrelevance_not_for_type() {
    let mut env = make_nat_env();

    let nat = cst("Nat");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("invariant: x axiom registers");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("y"),
        level_params: vec![],
        type_: nat,
    })
    .expect("invariant: y axiom registers");

    let tc = TypeChecker::new(&env);
    assert!(
        !tc.is_def_eq(&cst("x"), &cst("y")),
        "Proof irrelevance must NOT apply for Nat (Type 0, not Prop)"
    );
}

// ============================================================================
// Eta expansion
// ============================================================================

/// Regression: eta-expanded lambda is def-eq to the original function.
#[test]
fn test_regression_eta_expansion_lambda() {
    let mut env = Environment::new();

    let fn_ty = Expr::arrow(Expr::prop(), Expr::prop());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: fn_ty,
    })
    .expect("invariant: f axiom registers");

    let tc = TypeChecker::new(&env);

    let f = cst("f");
    let eta_f = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::app(cst("f"), Expr::bvar(0)),
    );

    assert!(tc.is_def_eq(&f, &eta_f), "Eta: (fun x => f x) == f");
    assert!(
        tc.is_def_eq(&eta_f, &f),
        "Eta symmetric: f == (fun x => f x)"
    );
}

/// Regression: double eta expansion.
#[test]
fn test_regression_double_eta_expansion() {
    let mut env = Environment::new();

    let fn_ty = Expr::arrow(Expr::prop(), Expr::arrow(Expr::prop(), Expr::prop()));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f2"),
        level_params: vec![],
        type_: fn_ty,
    })
    .expect("invariant: f2 axiom registers");

    let tc = TypeChecker::new(&env);

    let eta_f2 = Expr::lam(
        BinderInfo::Default,
        Expr::prop(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::app(Expr::app(cst("f2"), Expr::bvar(1)), Expr::bvar(0)),
        ),
    );

    assert!(
        tc.is_def_eq(&cst("f2"), &eta_f2),
        "Double eta: (fun x y => f2 x y) == f2"
    );
}

// ============================================================================
// noConfusion value type-checking
// ============================================================================

/// Regression: Nat.noConfusionType must type-check (#3208).
#[test]
fn test_regression_nat_no_confusion_type_tc() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let nct = env
        .get_const(&Name::from_string("Nat.noConfusionType"))
        .expect("Nat.noConfusionType should exist");

    let _ = tc
        .infer_type(&nct.type_)
        .expect("Nat.noConfusionType type should type-check");

    if let Some(val) = &nct.value {
        let _ = tc
            .infer_type(val)
            .expect("Nat.noConfusionType value should type-check");
    }
}

/// Regression: Nat.noConfusion must type-check (#3208).
#[test]
fn test_regression_nat_no_confusion_value_tc() {
    let env = make_nat_env_with_eq();
    let tc = TypeChecker::new(&env);

    let nc = env
        .get_const(&Name::from_string("Nat.noConfusion"))
        .expect("Nat.noConfusion should exist");

    let _ = tc
        .infer_type(&nc.type_)
        .expect("Nat.noConfusion type should type-check");

    if let Some(val) = &nc.value {
        let _ = tc
            .infer_type(val)
            .expect("Nat.noConfusion value should type-check");
    }
}

/// Regression: noConfusion for a multi-constructor inductive (#3208).
#[test]
fn test_regression_no_confusion_multi_constructor() {
    let mut env = Environment::new();
    env.init_eq().expect("invariant: Eq initializes");

    let color = Name::from_string("Color");
    let color_ref = cst("Color");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: color.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Color.red"),
                    type_: color_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Color.green"),
                    type_: color_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Color.blue"),
                    type_: color_ref,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("invariant: Color registers");

    let tc = TypeChecker::new(&env);

    let nct = env
        .get_const(&Name::from_string("Color.noConfusionType"))
        .expect("Color.noConfusionType should exist");
    let _ = tc
        .infer_type(&nct.type_)
        .expect("Color.noConfusionType type should type-check");
    if let Some(val) = &nct.value {
        let _ = tc
            .infer_type(val)
            .expect("Color.noConfusionType value should type-check");
    }

    let nc = env
        .get_const(&Name::from_string("Color.noConfusion"))
        .expect("Color.noConfusion should exist");
    let _ = tc
        .infer_type(&nc.type_)
        .expect("Color.noConfusion type should type-check");
    if let Some(val) = &nc.value {
        let _ = tc
            .infer_type(val)
            .expect("Color.noConfusion value should type-check");
    }
}
