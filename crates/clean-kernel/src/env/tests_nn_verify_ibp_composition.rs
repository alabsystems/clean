// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for T82 IBP composition (layer chaining proof).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_composition()
        .expect("init_nn_verify_ibp_composition should succeed");
    env
}

// ---------------------------------------------------------------
// Registration tests
// ---------------------------------------------------------------

#[test]
fn test_ibp_composition_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.ibp_composition"))
            .is_some(),
        "NNVerify.ibp_composition should be registered"
    );
}

#[test]
fn test_ibp_composition_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_composition"))
        .expect("should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "ibp_composition should be a Theorem, not {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "ibp_composition should have a proof term"
    );
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_ibp_composition_type_is_pi() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.ibp_composition"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("ibp_composition should type-check");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "ibp_composition type should be Pi, got {:?}",
        ty.kind()
    );
}

#[test]
fn test_ibp_composition_proof_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_composition"))
        .expect("should exist");
    let proof = info.value.as_ref().expect("should have proof term");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc.infer_type(proof).expect("T82 proof should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_ibp_composition_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_composition"))
        .expect("should exist");
    let sorry = info.sorry_summary();
    assert!(!sorry.has_sorry, "T82 proof should not use sorry");
}

// ---------------------------------------------------------------
// Dependency tests — T82 depends on T80 and T81
// ---------------------------------------------------------------

#[test]
fn test_t80_available() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.ibp_linear_sound"))
            .is_some(),
        "T80 (ibp_linear_sound) should be available after T82 init"
    );
}

#[test]
fn test_t81_available() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.ibp_relu_soundness"))
            .is_some(),
        "T81 (ibp_relu_soundness) should be available after T82 init"
    );
}

#[test]
fn test_intermediate_definitions_available() {
    let env = make_env();
    for name in &[
        "NNVerify.ibp_linear_bounds",
        "NNVerify.linear_output",
        "NNVerify.ibp_relu_bounds",
        "NNVerify.relu_vec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_composition().expect("first init");
    env.init_nn_verify_ibp_composition()
        .expect("second init (idempotent)");
}
