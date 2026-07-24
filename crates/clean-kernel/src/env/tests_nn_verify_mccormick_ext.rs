// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended McCormick envelope theorems (T50-T52, Phase 3).

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_mccormick_ext()
        .expect("init_nn_verify_mccormick_ext");
    env
}

#[test]
fn test_t50_mccormick_bilinear_sound_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.McCormick.mccormick_bilinear_sound"
        ))
        .is_some(),
        "T50: mccormick_bilinear_sound should be registered",
    );
}

#[test]
fn test_t51_mccormick_shared_input_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.McCormick.mccormick_shared_input"
        ))
        .is_some(),
        "T51: mccormick_shared_input should be registered",
    );
}

#[test]
fn test_t52_mccormick_linear_growth_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.McCormick.mccormick_linear_growth"
        ))
        .is_some(),
        "T52: mccormick_linear_growth should be registered",
    );
}

#[test]
fn test_total_gap_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.McCormick.total_gap"))
            .is_some(),
        "NNVerify.McCormick.total_gap should be registered",
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_mccormick_ext().expect("first init");
    env.init_nn_verify_mccormick_ext()
        .expect("second init should be idempotent");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.McCormick.mccormick_bilinear_sound",
        "NNVerify.McCormick.mccormick_shared_input",
        "NNVerify.McCormick.mccormick_linear_growth",
        "NNVerify.McCormick.total_gap",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "all names must start with NNVerify. prefix: {}",
            name,
        );
    }
}

#[test]
fn test_t50_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.McCormick.mccormick_bilinear_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer mccormick_bilinear_sound type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T50 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t51_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.McCormick.mccormick_shared_input"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer mccormick_shared_input type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T51 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_t52_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.McCormick.mccormick_linear_growth"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer mccormick_linear_growth type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "T52 should have Pi type (universally quantified)",
    );
}

#[test]
fn test_base_mccormick_still_accessible() {
    let env = make_env();
    // Verify that extending McCormick doesn't break base theorems
    assert!(
        env.get_const(&Name::from_string("NNVerify.McCormick.envelope_lower"))
            .is_some(),
        "Base McCormick envelope_lower should still be accessible",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.McCormick.mccormick_sound"))
            .is_some(),
        "Base McCormick mccormick_sound should still be accessible",
    );
}
