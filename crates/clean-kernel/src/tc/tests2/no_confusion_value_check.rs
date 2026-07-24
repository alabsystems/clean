// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests that noConfusion value bodies type-check correctly.
//!
//! These tests validate the Eq.ndrec + casesOn diagonal proof construction
//! in `build_no_confusion`, covering 0-param types (Nat), 1-param types
//! (Option-like), and multi-field constructors (List-like).

use super::support::make_nat_env_with_eq;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Assert that a named constant's value type-checks against its declared type.
fn assert_value_typechecks(env: &Environment, name: &str) {
    let tc = TypeChecker::new(env);
    let msg = format!("{name} should exist as a constant");
    let c = env.get_const(&Name::from_string(name)).expect(&msg);
    let msg = format!("{name} should have a value");
    let value = c.value.as_ref().expect(&msg);
    let msg = format!("{name} value should type-check");
    tc.check_type(value, &c.type_).expect(&msg);
}

/// Helper: create a 1-param Opt environment (Option-like) with Eq.
fn make_opt_env() -> Environment {
    let mut env = Environment::new();
    let v = Name::from_string("v");
    let v_level = Level::param(v.clone());
    let type_v = Expr::sort(Level::succ(v_level.clone()));
    let opt_name = Name::from_string("Opt");

    let none_type = Expr::pi(
        BinderInfo::Implicit,
        type_v.clone(),
        Expr::app(
            Expr::const_(opt_name.clone(), vec![v_level.clone()]),
            Expr::bvar(0),
        ),
    );
    let some_type = Expr::pi(
        BinderInfo::Implicit,
        type_v.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(
                Expr::const_(opt_name.clone(), vec![v_level.clone()]),
                Expr::bvar(1),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![InductiveType {
            name: opt_name.clone(),
            type_: Expr::arrow(type_v.clone(), type_v),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Opt.none"),
                    type_: none_type,
                },
                Constructor {
                    name: Name::from_string("Opt.some"),
                    type_: some_type,
                },
            ],
        }],
    };
    // Eq + HEq before add_inductive: the v4.30 heterogeneous noConfusion
    // convention (designs/2026-07-03-noconfusion-ctoridx-convention.md) uses
    // HEq/eq_of_heq for parameterized types.
    env.init_eq().expect("invariant: init_eq");
    env.init_heq().expect("invariant: init_heq");
    env.add_inductive(decl)
        .expect("invariant: Opt add_inductive");
    env
}

/// Helper: create a 1-param List environment with Eq.
fn make_list_env() -> Environment {
    let mut env = Environment::new();
    let v = Name::from_string("v");
    let v_level = Level::param(v.clone());
    let type_v = Expr::sort(Level::succ(v_level.clone()));
    let list_name = Name::from_string("List");

    let nil_type = Expr::pi(
        BinderInfo::Implicit,
        type_v.clone(),
        Expr::app(
            Expr::const_(list_name.clone(), vec![v_level.clone()]),
            Expr::bvar(0),
        ),
    );
    let cons_type = Expr::pi(
        BinderInfo::Implicit,
        type_v.clone(),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(list_name.clone(), vec![v_level.clone()]),
                    Expr::bvar(1),
                ),
                Expr::app(
                    Expr::const_(list_name.clone(), vec![v_level.clone()]),
                    Expr::bvar(2),
                ),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![v],
        num_params: 1,
        types: vec![InductiveType {
            name: list_name.clone(),
            type_: Expr::arrow(type_v.clone(), type_v),
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    // Eq + HEq before add_inductive: the v4.30 heterogeneous noConfusion
    // convention uses HEq/eq_of_heq for parameterized types.
    env.init_eq().expect("invariant: init_eq");
    env.init_heq().expect("invariant: init_heq");
    env.add_inductive(decl)
        .expect("invariant: List add_inductive");
    env
}

/// Nat.noConfusion value body type-checks (0-param inductive).
#[test]
fn test_no_confusion_value_typechecks() {
    let env = make_nat_env_with_eq();
    assert_value_typechecks(&env, "Nat.noConfusion");
}

/// Opt.noConfusion value body type-checks (1-param, Option-like).
#[test]
fn test_no_confusion_value_typechecks_1param() {
    let env = make_opt_env();
    assert_value_typechecks(&env, "Opt.noConfusionType");
    assert_value_typechecks(&env, "Opt.noConfusion");
}

/// List.noConfusion value body type-checks (1-param, multi-field constructor).
#[test]
fn test_no_confusion_value_typechecks_parameterized() {
    let env = make_list_env();
    assert_value_typechecks(&env, "List.noConfusion");
}

/// Helper: create a PUnit-like environment (0-param, 1 constructor, 0 fields).
/// PUnit.{u} : Sort u, with constructor PUnit.unit.{u} : PUnit.{u}.
/// This is the simplest possible universe-polymorphic inductive type.
fn make_punit_env() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let punit_name = Name::from_string("PUnit");
    let punit_const = Expr::const_(punit_name.clone(), vec![u_level.clone()]);

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 0,
        types: vec![InductiveType {
            name: punit_name.clone(),
            type_: Expr::sort(Level::succ(u_level)),
            constructors: vec![Constructor {
                name: Name::from_string("PUnit.unit"),
                type_: punit_const,
            }],
        }],
    };
    env.add_inductive(decl)
        .expect("invariant: PUnit add_inductive");
    env.init_eq().expect("invariant: init_eq");
    env
}

/// PUnit.noConfusionType value type-checks (0-param, single-constructor, 0 fields).
/// Regression: .olean-loaded PUnit.noConfusionType fails check_type with
/// TypeMismatch expected=PUnit.{u} inferred=Sort(u_1). Part of #3209.
#[test]
fn test_no_confusion_value_typechecks_punit_type() {
    let env = make_punit_env();
    assert_value_typechecks(&env, "PUnit.noConfusionType");
}

/// PUnit.noConfusion value type-checks (0-param, single-constructor, 0 fields).
/// Part of #3209.
#[test]
fn test_no_confusion_value_typechecks_punit() {
    let env = make_punit_env();
    assert_value_typechecks(&env, "PUnit.noConfusion");
}

/// Structural: PUnit.noConfusionType value starts with Lam. Part of #3209.
#[test]
fn test_punit_no_confusion_type_value_structure() {
    let env = make_punit_env();
    let c = env
        .get_const(&Name::from_string("PUnit.noConfusionType"))
        .expect("PUnit.noConfusionType should exist");
    let val = c.value.as_ref().expect("should have value");

    // Verify basic structure: should be 3 nested lambdas (P, a, b)
    assert!(val.is_lam(), "value should start with Lam");
    assert!(c.is_reducible, "should be Reducible");
    assert_eq!(
        c.level_params.len(),
        2,
        "should have 2 level params (u_1, u)"
    );
}
