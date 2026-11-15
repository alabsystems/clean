// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public-API regressions for legitimate `_nested.` display prefixes.
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{Environment, Expr, Level, Name};

fn constant(name: &Name) -> Expr {
    Expr::const_(name.clone(), vec![])
}

fn counter(name: &Name) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: name.clone().str("zero"),
                    type_: constant(name),
                },
                Constructor {
                    name: name.clone().str("next"),
                    type_: Expr::arrow(constant(name), constant(name)),
                },
            ],
        }],
    }
}

fn nested(name: &Name) -> InductiveDecl {
    let mut decl = counter(name);
    decl.types[0].constructors.push(Constructor {
        name: name.clone().str("children"),
        type_: Expr::arrow(
            Expr::app(
                Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                constant(name),
            ),
            constant(name),
        ),
    });
    decl
}

#[test]
fn ordinary_quoted_nested_control() {
    let name = Name::anon().str("Ordinary.Quoted");
    let mut env = Environment::with_prelude();
    env.add_inductive(nested(&name)).unwrap();
    assert!(env.get_inductive(&name).unwrap().is_nested);
    assert!(env.get_recursor(&name.clone().str("rec_1")).is_some());
}

#[test]
fn quoted_prefix_is_legal_for_core_inductive() {
    let name = Name::anon().str("_nested.Quoted");
    assert_ne!(name, Name::from_string("_nested.Quoted"));
    let mut env = Environment::with_prelude();
    env.add_inductive_core(counter(&name)).unwrap();
    assert!(env.get_inductive(&name).is_some());
    assert!(env.get_recursor(&name.clone().str("rec")).is_some());
}

#[test]
fn legitimate_quoted_prefix_nested_should_register() {
    let name = Name::anon().str("_nested.Quoted");
    assert_ne!(name, Name::from_string("_nested.Quoted"));
    let mut env = Environment::with_prelude();
    env.add_inductive(nested(&name)).unwrap();
    assert!(env.get_inductive(&name).unwrap().is_nested);
    assert!(env.get_recursor(&name.clone().str("rec_1")).is_some());
}

#[test]
fn unrelated_legal_quoted_prefix_must_not_panic_later_nested_registration() {
    let unrelated = Name::anon().str("_nested.Unrelated");
    let ordinary = Name::from_string("OrdinaryAfterUnrelated");
    let mut env = Environment::with_prelude();
    env.add_inductive_core(counter(&unrelated)).unwrap();
    env.add_inductive(nested(&ordinary)).unwrap();
    assert!(env.get_inductive(&unrelated).is_some());
    assert!(env.get_inductive(&ordinary).unwrap().is_nested);
}

#[test]
fn segmented_user_prefix_is_also_not_a_temporary_auxiliary_identity() {
    let name = Name::from_string("_nested.UserFamily");
    let mut env = Environment::with_prelude();
    env.add_inductive(nested(&name)).unwrap();
    assert!(env.get_inductive(&name).unwrap().is_nested);
    assert!(env.get_recursor(&name.clone().str("rec_1")).is_some());
}
