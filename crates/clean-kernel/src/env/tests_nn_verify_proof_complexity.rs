// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity lower bounds for NN verification certificates.
//!
//! Part of #3260.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_proof_complexity()
        .expect("init_nn_verify_proof_complexity");
    env
}

#[test]
fn test_certificate_size_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.CertificateSize"
        ))
        .is_some());
}

#[test]
fn test_network_complexity_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.NetworkComplexity"
        ))
        .is_some());
}

#[test]
fn test_bound_tightness_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.BoundTightness"
        ))
        .is_some());
}

#[test]
fn test_verification_problem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.VerificationProblem"
        ))
        .is_some());
}

#[test]
fn test_certificate_types_registered() {
    let env = make_env();
    for name in &[
        "NNVerify.ProofComplexity.IBPCertificate",
        "NNVerify.ProofComplexity.ZonotopeCertificate",
        "NNVerify.ProofComplexity.DeepPolyCertificate",
        "NNVerify.ProofComplexity.ibp_cert_size",
        "NNVerify.ProofComplexity.zonotope_cert_size",
        "NNVerify.ProofComplexity.deep_poly_cert_size",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

#[test]
fn test_cert_size_lower_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.cert_size_lower_bound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.cert_size_lower_bound_axiom"
        ))
        .is_some());
}

#[test]
fn test_ibp_cert_polynomial_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.ibp_cert_polynomial"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.ibp_cert_polynomial_axiom"
        ))
        .is_some());
}

#[test]
fn test_tighter_bound_larger_cert_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.tighter_bound_larger_cert"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.tighter_bound_larger_cert_axiom"
        ))
        .is_some());
}

#[test]
fn test_depth_width_tradeoff_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.depth_width_tradeoff"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.depth_width_tradeoff_axiom"
        ))
        .is_some());
}

#[test]
fn test_cert_hierarchy_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.cert_hierarchy"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.ProofComplexity.cert_hierarchy_axiom"
        ))
        .is_some());
}

#[test]
fn test_certificate_size_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.ProofComplexity.CertificateSize"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer CertificateSize type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_network_complexity_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.ProofComplexity.NetworkComplexity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer NetworkComplexity type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cert_size_lower_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.ProofComplexity.cert_size_lower_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer cert_size_lower_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cert_hierarchy_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.ProofComplexity.cert_hierarchy"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer cert_hierarchy type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_tighter_bound_larger_cert_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.ProofComplexity.tighter_bound_larger_cert"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer tighter_bound_larger_cert type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_proof_complexity().expect("first init");
    env.init_nn_verify_proof_complexity().expect("second init");
}

/// Verify all declarations use the `NNVerify.ProofComplexity.` prefix.
#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.ProofComplexity.CertificateSize",
        "NNVerify.ProofComplexity.NetworkComplexity",
        "NNVerify.ProofComplexity.BoundTightness",
        "NNVerify.ProofComplexity.VerificationProblem",
        "NNVerify.ProofComplexity.IBPCertificate",
        "NNVerify.ProofComplexity.ZonotopeCertificate",
        "NNVerify.ProofComplexity.DeepPolyCertificate",
        "NNVerify.ProofComplexity.ibp_cert_size",
        "NNVerify.ProofComplexity.zonotope_cert_size",
        "NNVerify.ProofComplexity.deep_poly_cert_size",
        "NNVerify.ProofComplexity.cert_size_lower_bound",
        "NNVerify.ProofComplexity.cert_size_lower_bound_axiom",
        "NNVerify.ProofComplexity.ibp_cert_polynomial",
        "NNVerify.ProofComplexity.ibp_cert_polynomial_axiom",
        "NNVerify.ProofComplexity.tighter_bound_larger_cert",
        "NNVerify.ProofComplexity.tighter_bound_larger_cert_axiom",
        "NNVerify.ProofComplexity.depth_width_tradeoff",
        "NNVerify.ProofComplexity.depth_width_tradeoff_axiom",
        "NNVerify.ProofComplexity.cert_hierarchy",
        "NNVerify.ProofComplexity.cert_hierarchy_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.ProofComplexity."),
            "{} must use NNVerify.ProofComplexity. prefix",
            name,
        );
    }
}
