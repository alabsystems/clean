// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended Lipschitz theorems (nn_verify_lipschitz_ext).
//!
//! Part of #3205.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_ext()
        .expect("init_nn_verify_lipschitz_ext");
    env
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_nn_verify_lipschitz_ext_compose_chain_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.compose_chain"))
        .is_some());
}

#[test]
fn test_nn_verify_lipschitz_ext_residual_lipschitz_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.residual_lipschitz"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.Lipschitz.residual_lipschitz_axiom"
        ))
        .is_some());
}

#[test]
fn test_nn_verify_lipschitz_ext_nfold_product_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.nfold_product"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.nfold_product_axiom"))
        .is_some());
}

#[test]
fn test_nn_verify_lipschitz_ext_product_le_exp_sum_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Lipschitz.product_le_exp_sum"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.Lipschitz.product_le_exp_sum_axiom"
        ))
        .is_some());
}

#[test]
fn test_nn_verify_lipschitz_ext_spectral_norm_lipschitz_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.Lipschitz.spectral_norm_lipschitz"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.Lipschitz.spectral_norm_lipschitz_axiom"
        ))
        .is_some());
}

// =============================================================================
// Type-checking tests
// =============================================================================

#[test]
fn test_nn_verify_lipschitz_ext_residual_lipschitz_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.residual_lipschitz"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer residual_lipschitz type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_nn_verify_lipschitz_ext_nfold_product_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.nfold_product"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer nfold_product type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_nn_verify_lipschitz_ext_product_le_exp_sum_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.product_le_exp_sum"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer product_le_exp_sum type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_nn_verify_lipschitz_ext_spectral_norm_lipschitz_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.spectral_norm_lipschitz"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer spectral_norm_lipschitz type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_nn_verify_lipschitz_ext_compose_chain_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.compose_chain"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer compose_chain type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =============================================================================
// Idempotency and convention tests
// =============================================================================

#[test]
fn test_nn_verify_lipschitz_ext_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_ext().expect("first init");
    env.init_nn_verify_lipschitz_ext().expect("second init");
}

/// Verify all extended declarations use the `NNVerify.Lipschitz.` prefix.
#[test]
fn test_nn_verify_lipschitz_ext_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.Lipschitz.compose_chain",
        "NNVerify.Lipschitz.residual_lipschitz",
        "NNVerify.Lipschitz.residual_lipschitz_axiom",
        "NNVerify.Lipschitz.nfold_product",
        "NNVerify.Lipschitz.nfold_product_axiom",
        "NNVerify.Lipschitz.product_le_exp_sum",
        "NNVerify.Lipschitz.product_le_exp_sum_axiom",
        "NNVerify.Lipschitz.spectral_norm_lipschitz",
        "NNVerify.Lipschitz.spectral_norm_lipschitz_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.Lipschitz."),
            "{} must use NNVerify.Lipschitz. prefix",
            name,
        );
    }
}

/// Verify that base Lipschitz declarations are still present (dependency check).
#[test]
fn test_nn_verify_lipschitz_ext_base_deps_present() {
    let env = make_env();
    let base_names = [
        "NNVerify.Lipschitz.constant",
        "NNVerify.Lipschitz.residual_block",
        "NNVerify.Lipschitz.spectral_norm",
        "NNVerify.Lipschitz.lip_product",
        "NNVerify.Lipschitz.real_exp",
    ];
    for name in &base_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "base decl {} should be registered by dependency",
            name,
        );
    }
}
