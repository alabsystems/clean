// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for ECLipsE Lipschitz composition theorems (T30-T33).
//!
//! Part of #3152.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_eclipse()
        .expect("init_nn_verify_lipschitz_eclipse");
    env
}

fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered"
    );
}

fn assert_type_checks_as_pi(env: &Environment, name: &str) {
    let e = Expr::const_(Name::from_string(name), vec![]);
    let tc = TypeChecker::with_mode(env, env.mode());
    let ty = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{name} should type-check, got: {err:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "{name} type should be Pi, got {:?}",
        ty.kind()
    );
}

// ---------------------------------------------------------------
// Type registration tests
// ---------------------------------------------------------------

#[test]
fn test_network_block_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.NetworkBlock");
}

#[test]
fn test_block_lipschitz_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.block_lipschitz");
}

#[test]
fn test_t30_lipschitz_compose_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.lipschitz_compose");
}

#[test]
fn test_t31_eclipse_block_lipschitz_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.eclipse_block_lipschitz");
}

#[test]
fn test_t32_eclipse_network_lipschitz_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.eclipse_network_lipschitz");
}

#[test]
fn test_t33_residual_lipschitz_sum_registered() {
    assert_registered(&make_env(), "NNVerify.Lipschitz.residual_lipschitz_sum");
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_network_block_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.NetworkBlock");
}

#[test]
fn test_block_lipschitz_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.block_lipschitz");
}

#[test]
fn test_t30_lipschitz_compose_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.lipschitz_compose");
}

#[test]
fn test_t31_eclipse_block_lipschitz_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.eclipse_block_lipschitz");
}

#[test]
fn test_t32_eclipse_network_lipschitz_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.eclipse_network_lipschitz");
}

#[test]
fn test_t33_residual_lipschitz_sum_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.Lipschitz.residual_lipschitz_sum");
}

// ---------------------------------------------------------------
// Kind tests
// ---------------------------------------------------------------

#[test]
fn test_declaration_kinds() {
    let env = make_env();
    // Opaque definitions (type/function, upgraded from Axiom)
    let opaque_names = [
        "NNVerify.Lipschitz.NetworkBlock",
        "NNVerify.Lipschitz.block_lipschitz",
    ];
    for name in &opaque_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should be Opaque (upgraded from Axiom), got {:?}",
            info.kind
        );
    }
    // T30-T33 are registered as Theorem (backed by *_axiom constants)
    let theorem_names = [
        "NNVerify.Lipschitz.lipschitz_compose",
        "NNVerify.Lipschitz.eclipse_block_lipschitz",
        "NNVerify.Lipschitz.eclipse_network_lipschitz",
        "NNVerify.Lipschitz.residual_lipschitz_sum",
    ];
    for name in &theorem_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be Theorem (backed by {name}_axiom), got {:?}",
            info.kind
        );
    }
}

// ---------------------------------------------------------------
// Dependency tests
// ---------------------------------------------------------------

#[test]
fn test_base_lipschitz_deps_present() {
    let env = make_env();
    // Core Lipschitz defs
    assert_registered(&env, "NNVerify.Lipschitz.constant");
    assert_registered(&env, "NNVerify.Lipschitz.residual_block");
    assert_registered(&env, "NNVerify.Lipschitz.lip_product");
    // Extended defs
    assert_registered(&env, "NNVerify.Lipschitz.compose_chain");
    assert_registered(&env, "NNVerify.Lipschitz.nfold_product");
}

// ---------------------------------------------------------------
// Naming convention test
// ---------------------------------------------------------------

#[test]
fn test_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.Lipschitz.NetworkBlock",
        "NNVerify.Lipschitz.block_lipschitz",
        "NNVerify.Lipschitz.lipschitz_compose",
        "NNVerify.Lipschitz.eclipse_block_lipschitz",
        "NNVerify.Lipschitz.eclipse_network_lipschitz",
        "NNVerify.Lipschitz.residual_lipschitz_sum",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
        assert!(
            name.starts_with("NNVerify.Lipschitz."),
            "{name} must use NNVerify.Lipschitz. prefix"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_lipschitz_eclipse().expect("first init");
    env.init_nn_verify_lipschitz_eclipse()
        .expect("second init (idempotent)");
}
