// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for propositional proof-reconstruction tests.

use super::*;

pub(super) fn add_prop_axioms(env: &mut Environment) {
    for (name, type_) in [
        (
            "And",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Or",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Not",
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        ("True", Expr::prop()),
        ("False", Expr::prop()),
        (
            "Iff",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .expect("propositional axiom should register");
    }
}

pub(super) fn add_prop_constructors(env: &mut Environment) {
    // True.intro : True
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True.intro"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .expect("True.intro axiom should register");
    // False.elim : {p : Sort 0} -> False -> p
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("False.elim"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("False"), vec![]),
                Expr::bvar(1),
            ),
        ),
    })
    .expect("False.elim axiom should register");
    // Iff.intro : {a b : Prop} -> (a -> b) -> (b -> a) -> Iff a b
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Iff.intro"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)),
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Iff"), vec![]),
                                Expr::bvar(3),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    })
    .expect("Iff.intro axiom should register");
    // absurd : {a b : Prop} -> a -> !a -> b
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("absurd"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(
                            Expr::const_(Name::from_string("Not"), vec![]),
                            Expr::bvar(2),
                        ),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    })
    .expect("absurd axiom should register");
}

pub(super) fn add_prop_constants(env: &mut Environment) {
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("propositional test constant should register");
    }
}

pub(super) fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    add_prop_axioms(&mut env);
    add_prop_constructors(&mut env);
    add_prop_constants(&mut env);
    env
}

pub(super) fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

pub(super) fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

pub(super) fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

pub(super) fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a.clone())
}

pub(super) fn mk_iff(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), a.clone()),
        b.clone(),
    )
}
