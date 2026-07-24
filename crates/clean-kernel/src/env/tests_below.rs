// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `.below` and `.brecOn` generation for recursive inductive types.
//!
//! These cover the automatically generated `.below` and `.brecOn` definitions
//! for recursive inductives, the `PUnit`/`PProd` prerequisites those
//! definitions depend on, and the fact that non-recursive inductives do not
//! get `.below`/`.brecOn` generated.

use super::test_helpers::{assert_const, expr_contains_const};
use super::*;
use crate::inductive::{count_pi_args, Constructor, InductiveDecl, InductiveType};
use crate::tc::TypeChecker;

fn make_nat_below_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_punit().unwrap();
    env.init_pprod().unwrap();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

fn make_list_below_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_punit().unwrap();
    env.init_pprod().unwrap();
    // Also need Nat for List's dependency
    env.init_nat().unwrap();

    let u = Name::from_string("u");
    let list = Name::from_string("List");
    // List : Type u -> Type u = Sort(u+1) -> Sort(u+1)
    let u_succ = Level::succ(Level::param(u.clone()));
    let type_u = Expr::from_kind(ExprKind::Sort(u_succ.clone()));
    let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    // List.nil : (a : Type u) -> List a
    let nil_type = Expr::pi(BinderInfo::Default, type_u.clone(), list_a.clone());
    // List.cons : (a : Type u) -> a -> List a -> List a
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(BinderInfo::Default, type_u, cons_body);
    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
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
    env.add_inductive(decl).unwrap();
    env
}

fn make_bool_env() -> Environment {
    let mut env = Environment::new();
    env.init_punit().unwrap();
    env.init_pprod().unwrap();

    let bool_name = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref,
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

#[test]
fn test_nat_below_generated() {
    let env = make_nat_below_env();
    assert_const(&env, "Nat.below");
}

#[test]
fn test_nat_brec_on_generated() {
    let env = make_nat_below_env();
    assert_const(&env, "Nat.brecOn");
}

#[test]
fn test_nat_below_type_arity() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    assert_eq!(
        count_pi_args(&ci.type_),
        2,
        "Nat.below should have 2 Pi args (motive + major)"
    );
}

#[test]
fn test_nat_below_type_well_formed() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&ci.type_);
    assert!(
        result.is_ok(),
        "Nat.below type should be well-formed: {:?}",
        result.err()
    );
}

#[test]
fn test_nat_below_value_type_checks() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    assert_eq!(
        count_pi_args(&ci.type_),
        2,
        "Nat.below should have 2 Pi args (motive + major)"
    );
    let value = ci.value.as_ref().unwrap();
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("Nat.below value should type-check");
}

#[test]
fn test_nat_brec_on_type_arity() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.brecOn")).unwrap();
    assert_eq!(
        count_pi_args(&ci.type_),
        3,
        "Nat.brecOn should have 3 Pi args (motive + major + F)"
    );
}

#[test]
fn test_nat_brec_on_type_well_formed() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.brecOn")).unwrap();
    let tc = TypeChecker::new(&env);
    let result = tc.infer_type(&ci.type_);
    assert!(
        result.is_ok(),
        "Nat.brecOn type should be well-formed: {:?}",
        result.err()
    );
}

#[test]
fn test_nat_brec_on_value_type_checks() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.brecOn")).unwrap();
    let value = ci.value.as_ref().unwrap();
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("Nat.brecOn value should type-check");
}

#[test]
fn test_list_below_generated() {
    let env = make_list_below_env();
    assert_const(&env, "List.below");
}

#[test]
fn test_list_brec_on_generated() {
    let env = make_list_below_env();
    assert_const(&env, "List.brecOn");
}

#[test]
fn test_list_below_type_arity() {
    let env = make_list_below_env();
    let ci = env.get_const(&Name::from_string("List.below")).unwrap();
    assert_eq!(
        count_pi_args(&ci.type_),
        3,
        "List.below should have 3 Pi args (alpha + motive + major)"
    );
}

#[test]
fn test_list_below_value_type_checks() {
    let env = make_list_below_env();
    let ci = env.get_const(&Name::from_string("List.below")).unwrap();
    assert_eq!(
        count_pi_args(&ci.type_),
        3,
        "List.below should have 3 Pi args (alpha + motive + major)"
    );
    let value = ci.value.as_ref().unwrap();
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("List.below value should type-check");
}

#[test]
fn test_list_brec_on_value_type_checks() {
    let env = make_list_below_env();
    let ci = env.get_const(&Name::from_string("List.brecOn")).unwrap();
    let value = ci.value.as_ref().unwrap();
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("List.brecOn value should type-check");
}

#[test]
fn test_nonrecursive_no_below() {
    let env = make_bool_env();
    assert!(
        env.get_const(&Name::from_string("Bool.below")).is_none(),
        "Bool.below should not be generated for a non-recursive inductive"
    );
    assert!(
        env.get_const(&Name::from_string("Bool.brecOn")).is_none(),
        "Bool.brecOn should not be generated for a non-recursive inductive"
    );
}

#[test]
fn test_below_not_generated_without_punit() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_pprod().unwrap();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();

    assert!(
        env.get_const(&Name::from_string("Nat.below")).is_none(),
        "Nat.below should be skipped when PUnit is missing"
    );
    assert!(
        env.get_const(&Name::from_string("Nat.brecOn")).is_none(),
        "Nat.brecOn should be skipped when PUnit is missing"
    );
}

#[test]
fn test_below_not_generated_without_pprod() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_punit().unwrap();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();

    assert!(
        env.get_const(&Name::from_string("Nat.below")).is_none(),
        "Nat.below should be skipped when PProd is missing"
    );
    assert!(
        env.get_const(&Name::from_string("Nat.brecOn")).is_none(),
        "Nat.brecOn should be skipped when PProd is missing"
    );
}

#[test]
fn test_nat_below_references_pprod() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    let value = ci.value.as_ref().unwrap();
    assert!(
        expr_contains_const(value, &Name::from_string("PProd")),
        "Nat.below value should reference PProd"
    );
}

#[test]
fn test_nat_below_references_punit() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    let value = ci.value.as_ref().unwrap();
    assert!(
        expr_contains_const(value, &Name::from_string("PUnit")),
        "Nat.below value should reference PUnit"
    );
}

#[test]
fn test_nat_below_references_rec() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    let value = ci.value.as_ref().unwrap();
    assert!(
        expr_contains_const(value, &Name::from_string("Nat.rec")),
        "Nat.below value should reference Nat.rec"
    );
}

#[test]
fn test_nat_below_is_reducible() {
    let env = make_nat_below_env();
    let ci = env.get_const(&Name::from_string("Nat.below")).unwrap();
    assert!(ci.is_reducible, "Nat.below should be reducible");
}
