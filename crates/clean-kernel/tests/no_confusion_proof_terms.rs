// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration coverage for the direct noConfusion proof terms used by decide_eq.

use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

fn make_nat_bool_env() -> Environment {
    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    env.add_inductive(InductiveDecl {
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
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    })
    .unwrap();

    let bool_ = Name::from_string("Bool");
    let bool_ref = Expr::const_(bool_.clone(), vec![]);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Bool.true"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Bool.false"),
                    type_: bool_ref.clone(),
                },
            ],
        }],
    })
    .unwrap();

    env.init_true_false().unwrap();
    env.init_eq().unwrap();
    env
}

fn build_ne_proof(type_name: &str, lhs: &Expr, rhs: &Expr) -> (Expr, Expr) {
    let ty = Expr::const_(Name::from_string(type_name), vec![]);
    let eq_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    );

    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let no_confusion = Expr::const_(
        Name::from_string(&format!("{type_name}.noConfusion")),
        vec![Level::zero()],
    );

    let body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(no_confusion, false_expr.clone()), lhs.clone()),
            rhs.clone(),
        ),
        Expr::bvar(0),
    );

    let proof = Expr::lam(BinderInfo::Default, eq_app.clone(), body);
    let expected = Expr::pi(BinderInfo::Default, eq_app, false_expr);
    (proof, expected)
}

fn assert_ne_proof_typechecks(type_name: &str, lhs: Expr, rhs: Expr, case_label: &str) {
    let env = make_nat_bool_env();
    let tc = TypeChecker::new(&env);
    let (proof, expected) = build_ne_proof(type_name, &lhs, &rhs);
    let inferred = tc
        .infer_type(&proof)
        .unwrap_or_else(|_| panic!("{case_label} should typecheck"));
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "{case_label} type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );
}

#[test]
fn test_ne_proof_nat_zero_succ_typechecks() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    assert_ne_proof_typechecks("Nat", zero, succ_zero, "Nat.zero ≠ Nat.succ");
}

#[test]
fn test_ne_proof_nat_succ_zero_typechecks() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    assert_ne_proof_typechecks("Nat", succ_zero, zero, "Nat.succ ≠ Nat.zero");
}

#[test]
fn test_ne_proof_bool_true_false_typechecks() {
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert_ne_proof_typechecks("Bool", btrue, bfalse, "Bool.true ≠ Bool.false");
}

#[test]
fn test_ne_proof_bool_false_true_typechecks() {
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert_ne_proof_typechecks("Bool", bfalse, btrue, "Bool.false ≠ Bool.true");
}
