// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Advanced tests for structure eta expansion: parametric types (PProd, Sigma),
//! negative cases (multi-constructor, Prop guard), and predicate unit tests.
//!
//! See `struct_eta.rs` for basic tests and shared helpers.
//! Part of #3134

use super::struct_eta::{build_simple_struct, setup_prod};
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

// =========================================================================
// PProd-like (implicit params)
// =========================================================================

/// Set up PProd : {a : Type} -> {b : Type} -> Type with implicit params.
fn setup_pprod(env: &mut Environment) {
    let pprod_name = Name::from_string("PProd");
    let pprod_mk = Name::from_string("PProd.mk");

    let pprod_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(BinderInfo::Implicit, Expr::type_(), Expr::type_()),
    );

    let mk_type = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::app(
                        Expr::app(Expr::const_(pprod_name.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: pprod_name,
            type_: pprod_type,
            constructors: vec![Constructor {
                name: pprod_mk,
                type_: mk_type,
            }],
        }],
    })
    .expect("add PProd");
}

/// p : PProd Nat Nat = PProd.mk Nat Nat (p.0) (p.1)
#[test]
fn test_struct_eta_pprod_like() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_pprod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pprod_name = Name::from_string("PProd");
    let pprod_nat_nat = Expr::app(
        Expr::app(Expr::const_(pprod_name.clone(), vec![]), nat.clone()),
        nat.clone(),
    );

    let p = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("p"),
        pprod_nat_nat,
        BinderInfo::Default,
    ));

    let mut expanded = Expr::const_(Name::from_string("PProd.mk"), vec![]);
    expanded = Expr::app(expanded, nat.clone());
    expanded = Expr::app(expanded, nat);
    expanded = Expr::app(expanded, Expr::proj(pprod_name.clone(), 0, p.clone()));
    expanded = Expr::app(expanded, Expr::proj(pprod_name, 1, p.clone()));

    assert!(tc.is_def_eq(&p, &expanded), "p = PProd.mk ... (p.0) (p.1)");
    assert!(tc.is_def_eq(&expanded, &p), "symmetric");
}

// =========================================================================
// Sigma-like type (dependent pair)
// =========================================================================

/// Set up Sigma : (a : Type) -> (a -> Type) -> Type.
fn setup_sigma(env: &mut Environment) {
    let sigma_name = Name::from_string("Sigma");
    let sigma_mk = Name::from_string("Sigma.mk");

    // Sigma : (a : Type) -> (a -> Type) -> Type
    let sigma_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::type_()),
            Expr::type_(),
        ),
    );

    // Sigma.mk : (a : Type) -> (b : a -> Type) -> (fst : a) -> b fst -> Sigma a b
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::type_()),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                    Expr::app(
                        Expr::app(Expr::const_(sigma_name.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: sigma_name,
            type_: sigma_type,
            constructors: vec![Constructor {
                name: sigma_mk,
                type_: mk_type,
            }],
        }],
    })
    .expect("add Sigma");
}

/// s : Sigma Nat (fun _ => Nat) = Sigma.mk ... (s.0) (s.1)
#[test]
fn test_struct_eta_sigma_like() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_sigma(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let sigma_name = Name::from_string("Sigma");
    let beta = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let sigma_nat = Expr::app(
        Expr::app(Expr::const_(sigma_name.clone(), vec![]), nat.clone()),
        beta.clone(),
    );

    let s = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("s"),
        sigma_nat,
        BinderInfo::Default,
    ));

    let mut expanded = Expr::const_(Name::from_string("Sigma.mk"), vec![]);
    expanded = Expr::app(expanded, nat);
    expanded = Expr::app(expanded, beta);
    expanded = Expr::app(expanded, Expr::proj(sigma_name.clone(), 0, s.clone()));
    expanded = Expr::app(expanded, Expr::proj(sigma_name, 1, s.clone()));

    assert!(tc.is_def_eq(&s, &expanded), "Sigma eta");
    assert!(tc.is_def_eq(&expanded, &s), "symmetric");
}

// =========================================================================
// Negative cases
// =========================================================================

/// Multi-constructor type: no structure eta.
#[test]
fn test_struct_eta_not_for_multi_constructor() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let either_name = Name::from_string("Either");

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: either_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Either.left"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat.clone(),
                        Expr::const_(either_name.clone(), vec![]),
                    ),
                },
                Constructor {
                    name: Name::from_string("Either.right"),
                    type_: Expr::pi(
                        BinderInfo::Default,
                        nat,
                        Expr::const_(either_name.clone(), vec![]),
                    ),
                },
            ],
        }],
    })
    .expect("add Either");

    let tc = TypeChecker::new(&env);
    let ty = Expr::const_(either_name, vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        ty.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("b"), ty, BinderInfo::Default),
    );
    assert!(!tc.is_def_eq(&a, &b), "multi-ctor values not def-eq");
}

/// Prop-typed structures: proof irrelevance, not structure eta.
#[test]
fn test_struct_eta_prop_guard() {
    let mut env = Environment::new();
    let pst_name = Name::from_string("PSt");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pst_name.clone(),
            type_: Expr::prop(),
            constructors: vec![Constructor {
                name: Name::from_string("PSt.mk"),
                type_: Expr::const_(pst_name.clone(), vec![]),
            }],
        }],
    })
    .expect("add PSt");

    let tc = TypeChecker::new(&env);
    let ty = Expr::const_(pst_name, vec![]);
    let a = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("a"),
        ty.clone(),
        BinderInfo::Default,
    ));
    let b = Expr::fvar(
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("b"), ty, BinderInfo::Default),
    );
    // Def-eq via proof irrelevance, not structure eta
    assert!(
        tc.is_def_eq(&a, &b),
        "Prop proofs def-eq via proof irrelevance"
    );
}

/// Prod.mk Nat Nat x y is reflexively def-eq via structural equality.
#[test]
fn test_struct_eta_ctor_concrete_fields_reflexive() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_prod(&mut env);

    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let x = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        nat.clone(),
        BinderInfo::Default,
    ));
    let y = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("y"),
        nat.clone(),
        BinderInfo::Default,
    ));

    let mk = super::struct_eta::build_prod_mk(&nat, &nat, x, y);
    assert!(tc.is_def_eq(&mk, &mk), "Prod.mk Nat Nat x y reflexive");
}

// =========================================================================
// Predicate unit tests
// =========================================================================

/// is_structure_like: true for single-ctor non-recursive, false otherwise.
#[test]
fn test_is_structure_like_predicate() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Wrap", 1, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    assert!(tc.is_structure_like(&Name::from_string("Wrap")));
    assert!(!tc.is_structure_like(&Name::from_string("Nat")));
    assert!(!tc.is_structure_like(&Name::from_string("Nonexistent")));
}

/// is_constructor_app detects constructor head applications.
#[test]
fn test_is_constructor_app_predicate() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Wrap", 1, nat.clone(), Expr::type_());

    let tc = TypeChecker::new(&env);
    let wrap_mk_app = Expr::app(
        Expr::const_(Name::from_string("Wrap.mk"), vec![]),
        Expr::nat_lit(42),
    );
    assert!(
        tc.is_constructor_app(&wrap_mk_app),
        "Wrap.mk 42 is ctor app"
    );

    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(tc.is_constructor_app(&nat_zero), "Nat.zero is ctor app");

    let not_ctor = Expr::const_(Name::from_string("Wrap"), vec![]);
    assert!(
        !tc.is_constructor_app(&not_ctor),
        "Wrap type is not ctor app"
    );

    let fvar = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        nat,
        BinderInfo::Default,
    ));
    assert!(!tc.is_constructor_app(&fvar), "FVar is not ctor app");
}

// =========================================================================
// expand_eta_struct and try_eta_struct direct tests
// =========================================================================

/// expand_eta_struct produces Pt.mk (x.0) (x.1).
#[test]
fn test_expand_eta_struct_direct() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "Pt", 2, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let pt_name = Name::from_string("Pt");
    let pt_ty = Expr::const_(pt_name.clone(), vec![]);
    let x = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        pt_ty.clone(),
        BinderInfo::Default,
    ));

    let result = tc.expand_eta_struct(&pt_ty, &x);
    assert!(result.is_some(), "expand_eta_struct succeeds for Pt");

    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Pt.mk"), vec![]),
            Expr::proj(pt_name.clone(), 0, x.clone()),
        ),
        Expr::proj(pt_name, 1, x),
    );
    assert!(
        tc.is_def_eq(&result.unwrap(), &expected),
        "correct expansion"
    );
}

/// try_eta_struct returns None for non-structure (Nat is recursive).
#[test]
fn test_try_eta_struct_none_for_non_structure() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let x = Expr::fvar(
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("x"), nat, BinderInfo::Default),
    );
    assert!(tc.try_eta_struct(&Name::from_string("Nat"), &x).is_none());
}

/// try_eta_struct returns None for already-constructor application.
#[test]
fn test_try_eta_struct_none_for_ctor_app() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "W1", 1, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let ctor_app = Expr::app(
        Expr::const_(Name::from_string("W1.mk"), vec![]),
        Expr::nat_lit(42),
    );
    assert!(tc
        .try_eta_struct(&Name::from_string("W1"), &ctor_app)
        .is_none());
}

/// try_eta_struct returns Some for FVar of structure type.
#[test]
fn test_try_eta_struct_some_for_fvar() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    build_simple_struct(&mut env, "W1", 1, nat, Expr::type_());

    let tc = TypeChecker::new(&env);
    let x = Expr::fvar(tc.ctx.borrow_mut().push(
        Name::from_string("x"),
        Expr::const_(Name::from_string("W1"), vec![]),
        BinderInfo::Default,
    ));
    assert!(tc.try_eta_struct(&Name::from_string("W1"), &x).is_some());
}
