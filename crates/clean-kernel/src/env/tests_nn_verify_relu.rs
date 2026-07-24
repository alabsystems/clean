// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for T81 (IBP ReLU soundness) — constructive 3-case split proof.
//!
//! Verifies that all 6 T81-related declarations are:
//! - Registered with correct `ConstantKind`
//! - Kernel type-checked (`tc.infer_type()` + `tc.is_def_eq()`)
//! - Fully verified (zero sorry, zero trusted-axiom debt)
//!
//! Part of #3254.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_relu()
        .expect("init_nn_verify_relu should succeed");
    env
}

fn assert_is_kind(env: &Environment, name: &str, expected: ConstantKind) {
    let info = env
        .get_const(&Name::from_string(name))
        .expect("should exist");
    assert_eq!(info.kind, expected, "{name} kind mismatch");
    assert!(info.value.is_some(), "{name} should have value");
}

fn assert_proof_type_checks(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .expect("should exist");
    let proof = info.value.as_ref().expect("should have proof term");
    let tc = TypeChecker::with_mode(env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("{name} proof should type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred type should match declared type"
    );
}

// --- Registration tests ---

#[test]
fn test_relu_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("NNVerify.relu")).is_some());
}

#[test]
fn test_relu_vec_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.relu_vec"))
        .is_some());
}

#[test]
fn test_sub_lemmas_registered() {
    let env = make_env();
    for name in &[
        "NNVerify.relu_nonneg",
        "NNVerify.relu_of_nonneg",
        "NNVerify.relu_of_nonpos",
        "NNVerify.relu_monotone",
    ] {
        assert!(env.get_const(&Name::from_string(name)).is_some(), "{name}");
    }
}

#[test]
fn test_ibp_relu_bounds_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ibp_relu_bounds"))
        .is_some());
}

#[test]
fn test_t81_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ibp_relu_soundness"))
        .is_some());
}

// --- Type-checking tests ---

#[test]
fn test_relu_type_checks() {
    let env = make_env();
    let relu = Expr::const_(Name::from_string("NNVerify.relu"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&relu).expect("infer NNVerify.relu type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_relu_vec_type_checks() {
    let env = make_env();
    let relu_vec = Expr::const_(Name::from_string("NNVerify.relu_vec"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&relu_vec).expect("infer relu_vec type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_relu().expect("first init");
    env.init_nn_verify_relu().expect("second init (idempotent)");
}

// --- Kind tests ---

#[test]
fn test_relu_of_nonneg_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.relu_of_nonneg", ConstantKind::Theorem);
}

#[test]
fn test_relu_of_nonpos_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.relu_of_nonpos", ConstantKind::Theorem);
}

#[test]
fn test_relu_nonneg_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.relu_nonneg", ConstantKind::Theorem);
}

#[test]
fn test_relu_monotone_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.relu_monotone", ConstantKind::Theorem);
}

#[test]
fn test_ibp_relu_bounds_is_definition() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_relu_bounds", ConstantKind::Definition);
}

#[test]
fn test_t81_is_theorem() {
    let env = make_env();
    assert_is_kind(&env, "NNVerify.ibp_relu_soundness", ConstantKind::Theorem);
}

// --- Proof type-checking tests ---

#[test]
fn test_relu_of_nonneg_proof_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.relu_of_nonneg");
}

#[test]
fn test_relu_of_nonpos_proof_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.relu_of_nonpos");
}

#[test]
fn test_relu_nonneg_proof_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.relu_nonneg");
}

#[test]
fn test_relu_monotone_proof_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.relu_monotone");
}

#[test]
fn test_ibp_relu_bounds_value_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.ibp_relu_bounds");
}

#[test]
fn test_t81_proof_type_checks() {
    let env = make_env();
    assert_proof_type_checks(&env, "NNVerify.ibp_relu_soundness");
}

// --- Trust and axiom-freedom tests ---

#[test]
fn test_t81_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_relu_soundness"))
        .expect("should exist");
    let sorry = info.sorry_summary();
    assert!(!sorry.has_sorry, "T81 proof should not use sorry");
}

/// Verify zero axiom dependencies: no sorry, no trusted-axiom debt
/// across all T81-related declarations (acceptance criterion #3254).
#[test]
fn test_t81_fully_verified_trust() {
    let env = make_env();
    for name in &[
        "NNVerify.relu_of_nonneg",
        "NNVerify.relu_of_nonpos",
        "NNVerify.relu_nonneg",
        "NNVerify.relu_monotone",
        "NNVerify.ibp_relu_bounds",
        "NNVerify.ibp_relu_soundness",
    ] {
        let info = env.get_const(&Name::from_string(name)).expect(name);
        let trust = info.trust_summary();
        assert!(
            trust.is_fully_verified(),
            "{name} should be fully verified (no sorry, no trusted axioms), \
             got: sorry={}, trusted_arith={}, trusted_ay={}",
            trust.has_sorry(),
            trust.trusted_arith_count,
            trust.trusted_ay_count,
        );
    }
}

/// Verify that T81 uses Declaration::Theorem, not Axiom.
#[test]
fn test_t81_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.ibp_relu_soundness"))
        .expect("should exist");
    assert_ne!(
        info.kind,
        ConstantKind::Axiom,
        "T81 must be a constructive Theorem, not an Axiom stub"
    );
    assert_eq!(info.kind, ConstantKind::Theorem);
    assert!(
        info.value.is_some(),
        "T81 Theorem must have a constructive proof value"
    );
}
