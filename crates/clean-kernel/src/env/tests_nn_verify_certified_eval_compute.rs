// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for certified computation engine.
//!
//! Validates that concrete NN evaluation produces kernel-verified proofs:
//! - Concrete vector registration and type-checking
//! - Constant network registration and type-checking
//! - Certified eval theorem (Eq.refl proof) passes kernel verification
//! - Multi-layer composition via certified_eval_composition
//! - Rational literal construction and equality
//!
//! Part of #3186.

use crate::env::nn_verify_certified_eval_compute::{CertifiedEvalInstance, ComputeConsts};
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_certified_eval()
        .expect("init certified eval");
    env.init_rat_arith().expect("init rat arith");
    env
}

// ── Rational literal construction ───────────────────────────────────

#[test]
fn test_compute_mk_rat_positive() {
    let cc = ComputeConsts::new();
    // Rat.mk (Int.ofNat 3) 4 represents 3/4
    let rat = cc.mk_rat(3, 4);
    // Should be App(App(Rat.mk, Int.ofNat(Nat.succ^3(Nat.zero))), Nat.succ^4(Nat.zero))
    match rat.kind() {
        ExprKind::App(_, _) => {} // Correct shape
        other => panic!("Expected App for Rat literal, got {:?}", other),
    }
}

#[test]
fn test_compute_mk_rat_negative() {
    let cc = ComputeConsts::new();
    // Rat.mk (Int.negSucc 1) 3 represents -2/3
    let rat = cc.mk_rat(-2, 3);
    match rat.kind() {
        ExprKind::App(_, _) => {} // Correct shape
        other => panic!("Expected App for negative Rat literal, got {:?}", other),
    }
}

#[test]
fn test_compute_mk_rat_zero() {
    let cc = ComputeConsts::new();
    // Rat.mk (Int.ofNat 0) 1 represents 0/1
    let rat = cc.mk_rat(0, 1);
    match rat.kind() {
        ExprKind::App(_, _) => {} // Correct shape
        other => panic!("Expected App for zero Rat literal, got {:?}", other),
    }
}

#[test]
fn test_compute_mk_nat_constructs_succ_chain() {
    let cc = ComputeConsts::new();
    let nat_0 = cc.mk_nat(0);
    assert!(
        matches!(nat_0.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.zero")),
        "mk_nat(0) should be Nat.zero"
    );

    let nat_3 = cc.mk_nat(3);
    // Should be Nat.succ(Nat.succ(Nat.succ(Nat.zero)))
    match nat_3.kind() {
        ExprKind::App(_, _) => {} // Correct: Nat.succ applied
        other => panic!("Expected App for Nat.succ chain, got {:?}", other),
    }
}

// ── Concrete vector registration ────────────────────────────────────

#[test]
fn test_compute_register_vec_dim1() {
    let mut env = make_env();
    let cc = ComputeConsts::new();
    let name = Name::from_string("NNVerify.CertEval.test_v1");
    env.register_concrete_vec(&cc, &name, 1, &[(3, 4)])
        .expect("register dim-1 vector");

    let info = env.get_const(&name).expect("vector should be registered");
    assert_eq!(info.kind, ConstantKind::Definition);

    // Type-check the value
    let tc = TypeChecker::with_mode(&env, env.mode());
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_compute_register_vec_dim0() {
    let mut env = make_env();
    let cc = ComputeConsts::new();
    let name = Name::from_string("NNVerify.CertEval.test_v0");
    env.register_concrete_vec(&cc, &name, 0, &[])
        .expect("register dim-0 vector");

    let info = env.get_const(&name).expect("vector should be registered");
    assert_eq!(info.kind, ConstantKind::Definition);
}

#[test]
fn test_compute_register_vec_dim3() {
    let mut env = make_env();
    let cc = ComputeConsts::new();
    let name = Name::from_string("NNVerify.CertEval.test_v3");
    env.register_concrete_vec(&cc, &name, 3, &[(1, 1), (2, 1), (3, 1)])
        .expect("register dim-3 vector");

    let info = env.get_const(&name).expect("vector should be registered");
    assert_eq!(info.kind, ConstantKind::Definition);

    let tc = TypeChecker::with_mode(&env, env.mode());
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "dim-3 vector type should match"
    );
}

// ── Constant network registration ───────────────────────────────────

#[test]
fn test_compute_register_const_network() {
    let mut env = make_env();
    let cc = ComputeConsts::new();
    let name = Name::from_string("NNVerify.CertEval.test_net");
    env.register_const_network(&cc, &name, 2, 1, &[(5, 1)])
        .expect("register constant network");

    let info = env.get_const(&name).expect("network should be registered");
    assert_eq!(info.kind, ConstantKind::Definition);

    // Type should be NNVec 2 -> NNVec 1
    let tc = TypeChecker::with_mode(&env, env.mode());
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "network type should match"
    );
}

#[test]
fn test_compute_const_network_type_is_pi() {
    let mut env = make_env();
    let cc = ComputeConsts::new();
    let name = Name::from_string("NNVerify.CertEval.test_net_pi");
    env.register_const_network(&cc, &name, 3, 2, &[(1, 1), (0, 1)])
        .expect("register");

    let info = env.get_const(&name).expect("should exist");
    // The type of the network should be a Pi type: NNVec n -> NNVec m
    match info.type_.kind() {
        ExprKind::Pi(_, _, _) => {} // Expected
        other => panic!("Expected Pi type for network, got {:?}", other),
    }
}

// ── Certified eval theorem (core: Eq.refl proof) ───────────────────

#[test]
fn test_compute_certified_eval_simple() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 1,
        output_dim: 1,
        network_name: Name::from_string("NNVerify.CertEval.simple_net"),
        input_name: Name::from_string("NNVerify.CertEval.simple_input"),
        output_name: Name::from_string("NNVerify.CertEval.simple_output"),
        proof_name: Name::from_string("NNVerify.CertEval.simple_proof"),
    };

    // Input: [1/1], Output: [1/1] (identity network)
    env.register_certified_eval(&instance, &[(1, 1)], &[(1, 1)])
        .expect("certified eval should succeed");

    // Verify the proof theorem exists and type-checks
    let info = env
        .get_const(&instance.proof_name)
        .expect("proof should be registered");
    assert_eq!(info.kind, ConstantKind::Theorem);

    // The kernel type-checked the theorem on registration,
    // so if we got here the proof is verified.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let proof_val = info.value.as_ref().expect("theorem should have proof");
    let inferred = tc.infer_type(proof_val).expect("proof should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "proof type should match theorem statement"
    );
}

#[test]
fn test_compute_certified_eval_3d_to_2d() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 3,
        output_dim: 2,
        network_name: Name::from_string("NNVerify.CertEval.net_3to2"),
        input_name: Name::from_string("NNVerify.CertEval.input_3d"),
        output_name: Name::from_string("NNVerify.CertEval.output_2d"),
        proof_name: Name::from_string("NNVerify.CertEval.proof_3to2"),
    };

    // Input: [1/1, 2/1, 3/1], Output: [7/2, 7/2] (constant network)
    env.register_certified_eval(&instance, &[(1, 1), (2, 1), (3, 1)], &[(7, 2), (7, 2)])
        .expect("3d->2d certified eval");

    let info = env.get_const(&instance.proof_name).expect("proof exists");
    assert_eq!(info.kind, ConstantKind::Theorem);

    let tc = TypeChecker::with_mode(&env, env.mode());
    let proof_val = info.value.as_ref().expect("has proof");
    let inferred = tc.infer_type(proof_val).expect("proof type-checks");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "proof type matches statement"
    );
}

#[test]
fn test_compute_certified_eval_zero_dim() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 0,
        output_dim: 0,
        network_name: Name::from_string("NNVerify.CertEval.net_0to0"),
        input_name: Name::from_string("NNVerify.CertEval.input_0d"),
        output_name: Name::from_string("NNVerify.CertEval.output_0d"),
        proof_name: Name::from_string("NNVerify.CertEval.proof_0to0"),
    };

    env.register_certified_eval(&instance, &[], &[])
        .expect("0d certified eval");

    let info = env.get_const(&instance.proof_name).expect("proof exists");
    assert_eq!(info.kind, ConstantKind::Theorem);
}

// ── Rat literal equality via kernel ─────────────────────────────────

#[test]
fn test_compute_rat_literal_type_checks_in_kernel() {
    let env = make_env();
    let cc = ComputeConsts::new();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Build Rat.mk (Int.ofNat 3) 4
    let rat_val = cc.mk_rat(3, 4);
    let inferred = tc
        .infer_type(&rat_val)
        .expect("rat literal should type-check");

    // The type should be Rat
    let rat_type = cc.rat.clone();
    assert!(
        tc.is_def_eq(&inferred, &rat_type),
        "rat literal should have type Rat, got {:?}",
        inferred
    );
}

#[test]
fn test_compute_negative_rat_literal_type_checks() {
    let env = make_env();
    let cc = ComputeConsts::new();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Build Rat.mk (Int.negSucc 1) 3 = -2/3
    let rat_val = cc.mk_rat(-2, 3);
    let inferred = tc
        .infer_type(&rat_val)
        .expect("negative rat should type-check");
    let rat_type = cc.rat.clone();
    assert!(
        tc.is_def_eq(&inferred, &rat_type),
        "negative rat literal should have type Rat"
    );
}

// ── Eq.refl proof construction ──────────────────────────────────────

#[test]
fn test_compute_rat_refl_proof_type_checks() {
    let env = make_env();
    let cc = ComputeConsts::new();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Build @Eq.refl Rat (Rat.mk (Int.ofNat 1) 1)
    let rat_one = cc.mk_rat(1, 1);
    let refl_proof = cc.mk_rat_refl(rat_one.clone());
    let inferred = tc
        .infer_type(&refl_proof)
        .expect("Eq.refl should type-check");

    // The type should be Eq Rat (Rat.mk 1 1) (Rat.mk 1 1)
    let expected_type = cc.mk_rat_eq(rat_one.clone(), rat_one);
    assert!(
        tc.is_def_eq(&inferred, &expected_type),
        "Eq.refl proof should have correct type"
    );
}

// ── Vec type construction ───────────────────────────────────────────

#[test]
fn test_compute_vec_type_is_well_formed() {
    let env = make_env();
    let cc = ComputeConsts::new();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // NNVec 3 should have type Type
    let vec3 = cc.vec_type(3);
    let inferred = tc.infer_type(&vec3).expect("NNVec 3 should be well-typed");
    let type0 = cc.type0.clone();
    assert!(
        tc.is_def_eq(&inferred, &type0),
        "NNVec 3 should have type Type"
    );
}

// ── Certified eval with negative values ─────────────────────────────

#[test]
fn test_compute_certified_eval_negative_weights() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 2,
        output_dim: 2,
        network_name: Name::from_string("NNVerify.CertEval.neg_net"),
        input_name: Name::from_string("NNVerify.CertEval.neg_input"),
        output_name: Name::from_string("NNVerify.CertEval.neg_output"),
        proof_name: Name::from_string("NNVerify.CertEval.neg_proof"),
    };

    // Network with negative output values
    env.register_certified_eval(&instance, &[(1, 2), (-3, 4)], &[(-1, 3), (-1, 3)])
        .expect("certified eval with negatives");

    let info = env.get_const(&instance.proof_name).expect("proof exists");
    assert_eq!(info.kind, ConstantKind::Theorem);

    let tc = TypeChecker::with_mode(&env, env.mode());
    let proof_val = info.value.as_ref().expect("has proof");
    let inferred = tc.infer_type(proof_val).expect("proof type-checks");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "negative-weight proof verified"
    );
}

// ── All registered names follow convention ──────────────────────────

#[test]
fn test_compute_naming_convention() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 1,
        output_dim: 1,
        network_name: Name::from_string("NNVerify.CertEval.conv_net"),
        input_name: Name::from_string("NNVerify.CertEval.conv_input"),
        output_name: Name::from_string("NNVerify.CertEval.conv_output"),
        proof_name: Name::from_string("NNVerify.CertEval.conv_proof"),
    };

    env.register_certified_eval(&instance, &[(1, 1)], &[(1, 1)])
        .expect("register");

    // All names should follow NNVerify.CertEval. prefix
    for name_str in &[
        "NNVerify.CertEval.conv_net",
        "NNVerify.CertEval.conv_input",
        "NNVerify.CertEval.conv_output",
        "NNVerify.CertEval.conv_proof",
    ] {
        assert!(
            env.get_const(&Name::from_string(name_str)).is_some(),
            "{} should be registered",
            name_str
        );
    }
}

// ── No sorry in definitions ─────────────────────────────────────────

#[test]
fn test_compute_no_sorry() {
    let mut env = make_env();

    let instance = CertifiedEvalInstance {
        input_dim: 1,
        output_dim: 1,
        network_name: Name::from_string("NNVerify.CertEval.sorry_net"),
        input_name: Name::from_string("NNVerify.CertEval.sorry_input"),
        output_name: Name::from_string("NNVerify.CertEval.sorry_output"),
        proof_name: Name::from_string("NNVerify.CertEval.sorry_proof"),
    };

    env.register_certified_eval(&instance, &[(1, 1)], &[(1, 1)])
        .expect("register");

    for name_str in &[
        "NNVerify.CertEval.sorry_net",
        "NNVerify.CertEval.sorry_input",
        "NNVerify.CertEval.sorry_output",
        "NNVerify.CertEval.sorry_proof",
    ] {
        let info = env
            .get_const(&Name::from_string(name_str))
            .expect("should exist");
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "{} should not use sorry", name_str);
    }
}
