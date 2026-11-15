// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Environment::add_quot` refuses every `Eq` Lean's `add_quot` refuses, and
//! installs nothing when it does.

use super::super::{ConstantInfo, ConstantKind, Environment, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn u() -> Level {
    Level::param(n("u"))
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, a, b)
}

/// `{α : Sort u} → α → α → Prop`
fn eq_type() -> Expr {
    Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u()),
        arrow(Expr::bvar(0), arrow(Expr::bvar(1), prop())),
    )
}

/// `∀ {α : Sort u} (a : α), @Eq α a a`
fn refl_type() -> Expr {
    let eq_u = Expr::const_(n("Eq"), vec![u()]);
    Expr::pi(
        BinderInfo::Implicit,
        Expr::sort(u()),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(
                Expr::app(Expr::app(eq_u, Expr::bvar(1)), Expr::bvar(0)),
                Expr::bvar(0),
            ),
        ),
    )
}

fn add_eq(env: &mut Environment, num_params: u32, ctors: Vec<Constructor>) {
    env.add_inductive_core(InductiveDecl {
        level_params: vec![n("u")],
        num_params,
        types: vec![InductiveType {
            name: n("Eq"),
            type_: eq_type(),
            constructors: ctors,
        }],
    })
    .expect("fixture Eq is admissible");
}

fn refl() -> Constructor {
    Constructor {
        name: n("Eq.refl"),
        type_: refl_type(),
    }
}

fn assert_refused(env: &mut Environment, needle: &str) {
    let err = env.add_quot().expect_err("add_quot must refuse this Eq");
    assert!(err.contains(needle), "{err}");
    assert!(
        !env.quot_installed(),
        "a refused add_quot installed the quotient"
    );
    assert!(env.get_const(&n("Quot.sound")).is_none());
}

#[test]
fn lean_shaped_eq_admits_the_quotient() {
    for num_params in [1, 2] {
        let mut env = Environment::default();
        add_eq(&mut env, num_params, vec![refl()]);
        env.add_quot().expect("Lean-shaped Eq");
        assert!(env.quot_installed());
        assert!(env.get_const(&n("Quot.sound")).is_some());
        // Idempotent.
        env.add_quot().expect("second call is a no-op");
    }
}

#[test]
fn no_eq_is_refused() {
    assert_refused(
        &mut Environment::default(),
        "does not hold an inductive type `Eq`",
    );
}

/// The round-23 attack's first form: `Eq` as a DEFINITION.
#[test]
fn a_definition_named_eq_is_refused() {
    let mut env = Environment::default();
    let value = Expr::lam(
        BinderInfo::Implicit,
        Expr::sort(u()),
        Expr::lam(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::lam(BinderInfo::Default, Expr::bvar(1), prop()),
        ),
    );
    let rejected = env.extend_constants_structural(std::iter::once(ConstantInfo {
        name: n("Eq"),
        level_params: vec![n("u")],
        type_: eq_type(),
        value: Some(value),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    }));
    assert!(rejected.is_empty(), "{rejected:?}");
    assert_refused(&mut env, "does not hold an inductive type `Eq`");
}

/// The round-23 attack's second form: `Eq` with NO constructor.
#[test]
fn an_empty_eq_is_refused() {
    let mut env = Environment::default();
    add_eq(&mut env, 2, vec![]);
    assert_refused(&mut env, "0 constructors");
}

#[test]
fn an_eq_with_a_second_constructor_is_refused() {
    let mut env = Environment::default();
    add_eq(
        &mut env,
        2,
        vec![
            refl(),
            Constructor {
                name: n("Eq.any"),
                // ∀ {α} (a b : α), @Eq α a b
                type_: Expr::pi(
                    BinderInfo::Implicit,
                    Expr::sort(u()),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(0),
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::bvar(1),
                            Expr::app(
                                Expr::app(
                                    Expr::app(Expr::const_(n("Eq"), vec![u()]), Expr::bvar(2)),
                                    Expr::bvar(1),
                                ),
                                Expr::bvar(0),
                            ),
                        ),
                    ),
                ),
            },
        ],
    );
    assert_refused(&mut env, "2 constructors");
}

/// One constructor, but it relates EVERY pair: `∀ {α} (a b : α), Eq a b`.
#[test]
fn an_eq_whose_one_constructor_is_not_refl_is_refused() {
    let mut env = Environment::default();
    add_eq(
        &mut env,
        1,
        vec![Constructor {
            name: n("Eq.any"),
            type_: Expr::pi(
                BinderInfo::Implicit,
                Expr::sort(u()),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(0),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::bvar(1),
                        Expr::app(
                            Expr::app(
                                Expr::app(Expr::const_(n("Eq"), vec![u()]), Expr::bvar(2)),
                                Expr::bvar(1),
                            ),
                            Expr::bvar(0),
                        ),
                    ),
                ),
            ),
        }],
    );
    assert_refused(&mut env, "does not have type");
}
