// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `nn_verify_matrix_rank` module.
//!
//! Part of #3207.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_matrix_rank()
        .expect("init_nn_verify_matrix_rank");
    env
}

#[test]
fn test_ones_matrix_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ones_matrix"))
        .is_some());
}

#[test]
fn test_mean_projection_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.mean_projection"))
        .is_some());
}

#[test]
fn test_ones_matrix_rank_one_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ones_matrix_rank_one"))
        .is_some());
}

#[test]
fn test_mean_projection_idempotent_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.mean_projection_idempotent"))
        .is_some());
}

#[test]
fn test_identity_minus_projection_rank_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.identity_minus_projection_rank"
        ))
        .is_some());
}

#[test]
fn test_zonotope_rankdef_width_eq_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.zonotope_rankdef_width_eq"))
        .is_some());
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    let helpers = [
        "NNVerify.matrix_rank",
        "NNVerify.matrix_mul",
        "NNVerify.matrix_sub",
        "NNVerify.identity_matrix",
        "NNVerify.interval_hull_width",
        "NNVerify.linear_image_zonotope",
        "NNVerify.fresh_zonotope_from_hull",
    ];
    for name in &helpers {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

#[test]
fn test_ones_matrix_type_checks() {
    let env = make_env();
    let ones = Expr::const_(Name::from_string("NNVerify.ones_matrix"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ones)
        .expect("infer NNVerify.ones_matrix type");
    // Should be Nat -> NNMat n n (a Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mean_projection_type_checks() {
    let env = make_env();
    let mp = Expr::const_(Name::from_string("NNVerify.mean_projection"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&mp)
        .expect("infer NNVerify.mean_projection type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent_init() {
    let mut env = Environment::new();
    env.init_nn_verify_matrix_rank().expect("first init");
    env.init_nn_verify_matrix_rank().expect("second init");
}

/// Verify all declarations use the `NNVerify.` prefix.
#[test]
fn test_nn_verify_naming_convention() {
    let env = make_env();
    let nn_names = [
        "NNVerify.ones_matrix",
        "NNVerify.mean_projection",
        "NNVerify.ones_matrix_rank_one",
        "NNVerify.mean_projection_idempotent",
        "NNVerify.identity_minus_projection_rank",
        "NNVerify.zonotope_rankdef_width_eq",
        "NNVerify.matrix_rank",
        "NNVerify.matrix_mul",
        "NNVerify.matrix_sub",
        "NNVerify.identity_matrix",
        "NNVerify.interval_hull_width",
        "NNVerify.linear_image_zonotope",
        "NNVerify.fresh_zonotope_from_hull",
    ];
    for name in &nn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered with NNVerify. prefix",
            name,
        );
    }
}
