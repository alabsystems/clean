// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for noConfusion proof term typechecking (#1144).
//!
//! Verifies that the proof terms produced by `make_ne_proof` in decide_eq.rs
//! actually typecheck in the kernel. Tests construct the exact proof term
//! structure: `λ (h : @Eq T a b), @T.noConfusion.{0} False a b h`.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Helper: create a Nat+Bool environment with True/False and Eq.
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

/// Build the exact proof term that make_ne_proof in decide_eq.rs constructs:
///   `λ (h : @Eq.{1} T a b), @T.noConfusion.{0} False a b h`
///
/// Returns (proof_term, expected_type) where expected_type = `@Eq T a b → False`.
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
    let nc = Expr::const_(
        Name::from_string(&format!("{type_name}.noConfusion")),
        vec![Level::zero()],
    );

    let body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(nc, false_expr.clone()), lhs.clone()),
            rhs.clone(),
        ),
        Expr::bvar(0),
    );

    let proof = Expr::lam(BinderInfo::Default, eq_app.clone(), body);
    let expected = Expr::pi(BinderInfo::Default, eq_app, false_expr);
    (proof, expected)
}

/// Verify: noConfusion proof for Nat.zero ≠ Nat.succ(Nat.zero) typechecks.
#[test]
fn test_ne_proof_nat_zero_succ_typechecks() {
    let env = make_nat_bool_env();
    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let (proof, expected) = build_ne_proof("Nat", &zero, &succ_zero);
    let inferred = tc
        .infer_type(&proof)
        .expect("proof for Nat.zero ≠ Nat.succ should typecheck");
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );
}

/// Verify: noConfusion proof for Nat.succ(Nat.zero) ≠ Nat.zero (reversed).
#[test]
fn test_ne_proof_nat_succ_zero_typechecks() {
    let env = make_nat_bool_env();
    let tc = TypeChecker::new(&env);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    let (proof, expected) = build_ne_proof("Nat", &succ_zero, &zero);
    let inferred = tc
        .infer_type(&proof)
        .expect("proof for Nat.succ ≠ Nat.zero should typecheck");
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );
}

/// Verify: noConfusion proof for Bool.true ≠ Bool.false typechecks.
#[test]
fn test_ne_proof_bool_true_false_typechecks() {
    let env = make_nat_bool_env();
    let tc = TypeChecker::new(&env);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);

    let (proof, expected) = build_ne_proof("Bool", &btrue, &bfalse);
    let inferred = tc
        .infer_type(&proof)
        .expect("proof for Bool.true ≠ Bool.false should typecheck");
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );
}

/// Verify: noConfusion proof for Bool.false ≠ Bool.true (reversed).
#[test]
fn test_ne_proof_bool_false_true_typechecks() {
    let env = make_nat_bool_env();
    let tc = TypeChecker::new(&env);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);

    let (proof, expected) = build_ne_proof("Bool", &bfalse, &btrue);
    let inferred = tc
        .infer_type(&proof)
        .expect("proof for Bool.false ≠ Bool.true should typecheck");
    assert!(
        tc.is_def_eq(&inferred, &expected),
        "type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );
}
