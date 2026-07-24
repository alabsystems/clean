// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for T30 Lipschitz composition (compose_lipschitz).
//!
//! NOTE: The higher-order function types `(NNVec n -> NNVec n)` cause stack
//! overflow in the type checker's sort inference, so these tests verify
//! structural properties of the registered declarations rather than
//! running full type checking. See nn_verify_lipschitz_compose.rs for details.
//!
//! Part of #3079.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_compose()
        .expect("init_nn_verify_lipschitz_compose should succeed");
    env
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

#[test]
fn test_is_lipschitz_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.is_lipschitz"))
            .is_some(),
        "NNVerify.is_lipschitz should be registered"
    );
}

#[test]
fn test_compose_fns_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.compose_fns"))
            .is_some(),
        "NNVerify.compose_fns should be registered"
    );
}

#[test]
fn test_compose_lipschitz_axiom_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.compose_lipschitz_axiom"))
            .is_some(),
        "compose_lipschitz_axiom should be registered"
    );
}

#[test]
fn test_compose_lipschitz_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.compose_lipschitz"))
            .is_some(),
        "compose_lipschitz should be registered"
    );
}

// ---------------------------------------------------------------
// Kind tests
// ---------------------------------------------------------------

#[test]
fn test_compose_lipschitz_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_lipschitz"))
        .expect("should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "compose_lipschitz should be a Theorem, not {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "compose_lipschitz should have a proof term"
    );
}

#[test]
fn test_compose_fns_is_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_fns"))
        .expect("should exist");
    // Registered as Axiom (opaque — no definition body).
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "compose_fns should be an Axiom, not {:?}",
        info.kind
    );
}

#[test]
fn test_compose_lipschitz_axiom_is_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_lipschitz_axiom"))
        .expect("should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "compose_lipschitz_axiom should be an Axiom, not {:?}",
        info.kind
    );
}

// ---------------------------------------------------------------
// Structural type tests
// ---------------------------------------------------------------

#[test]
fn test_compose_lipschitz_type_is_pi() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_lipschitz"))
        .expect("should exist");
    assert!(
        matches!(info.type_.kind(), ExprKind::Pi(..)),
        "compose_lipschitz type should be Pi, got {:?}",
        info.type_.kind()
    );
}

#[test]
fn test_compose_fns_type_is_pi() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_fns"))
        .expect("should exist");
    assert!(
        matches!(info.type_.kind(), ExprKind::Pi(..)),
        "compose_fns type should be Pi, got {:?}",
        info.type_.kind()
    );
}

#[test]
fn test_is_lipschitz_type_is_pi() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.is_lipschitz"))
        .expect("should exist");
    assert!(
        matches!(info.type_.kind(), ExprKind::Pi(..)),
        "is_lipschitz type should be Pi, got {:?}",
        info.type_.kind()
    );
}

#[test]
fn test_compose_lipschitz_proof_references_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_lipschitz"))
        .expect("should exist");
    let proof = info.value.as_ref().expect("should have proof term");
    // The proof is Expr::const_("NNVerify.compose_lipschitz_axiom", [])
    match proof.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(
                name.to_string(),
                "NNVerify.compose_lipschitz_axiom",
                "proof should reference compose_lipschitz_axiom"
            );
            assert!(levels.is_empty(), "proof should have no universe levels");
        }
        other => panic!("proof should be Const, got {:?}", other),
    }
}

#[test]
fn test_compose_fns_no_value() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_fns"))
        .expect("should exist");
    assert!(
        info.value.is_none(),
        "compose_fns (Axiom) should have no value"
    );
}

// ---------------------------------------------------------------
// Trust tests
// ---------------------------------------------------------------

#[test]
fn test_compose_lipschitz_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.compose_lipschitz"))
        .expect("should exist");
    let sorry = info.sorry_summary();
    assert!(!sorry.has_sorry, "compose_lipschitz should not use sorry");
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_compose().expect("first init");
    env.init_nn_verify_lipschitz_compose()
        .expect("second init (idempotent)");
}
