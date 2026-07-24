// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for bridge tests.
//!
//! Provides common setup functions used across multiple bridge test modules.
//! Split from bridge/tests.rs as part of #307.

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level};

/// Create a standard test environment with Eq, Eq.refl, type A, constants a/b/c, and function f.
pub(super) fn setup_env() -> Environment {
    let mut env = Environment::new();

    // Add Eq type: Eq : {α : Sort u} → α → α → Prop
    // We'll use a simplified version
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                clean_kernel::BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(
                    clean_kernel::BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::prop(),
                ),
            ),
        ),
    })
    .expect("invariant: test env decl should be valid");

    // Add Eq.refl : ∀ {α : Sort u} (a : α), Eq α a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                clean_kernel::BinderInfo::Implicit,
                Expr::bvar(0),
                // Eq α a a (using apps)
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .expect("invariant: test env decl should be valid");

    // Add a base type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("invariant: test env decl should be valid");

    // Add constants a, b, c : A
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .expect("invariant: test env decl should be valid");
    }

    // Add a function f : A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        ),
    })
    .expect("invariant: test env decl should be valid");

    env
}

/// Make an Eq expression: Eq A a b
pub(super) fn make_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}
