// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C003 ECLipsE convergence rate kernel theorems.
//!
//! Part of #3311, Part of #3150.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_eclipse_convergence()
        .expect("init_nn_verify_eclipse_convergence");
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
// Definition registration tests
// ---------------------------------------------------------------

#[test]
fn test_rat_pow_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.rat_pow");
}

#[test]
fn test_width_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.width");
}

#[test]
fn test_refine_op_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.refine_op");
}

#[test]
fn test_refine_apply_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.refine_apply");
}

#[test]
fn test_log_rat_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.log_rat");
}

#[test]
fn test_ceil_nat_registered() {
    assert_registered(&make_env(), "NNVerify.ECLipsE.ceil_nat");
}

// ---------------------------------------------------------------
// Theorem registration tests
// ---------------------------------------------------------------

#[test]
fn test_c003a_geometric_decay_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ECLipsE.geometric_decay");
    assert_registered(&env, "NNVerify.ECLipsE.geometric_decay_axiom");
}

#[test]
fn test_c003b_termination_bound_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ECLipsE.termination_bound");
    assert_registered(&env, "NNVerify.ECLipsE.termination_bound_axiom");
}

#[test]
fn test_c003c_fixed_point_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ECLipsE.fixed_point");
    assert_registered(&env, "NNVerify.ECLipsE.fixed_point_axiom");
}

#[test]
fn test_c003d_contraction_compose_registered() {
    let env = make_env();
    assert_registered(&env, "NNVerify.ECLipsE.contraction_compose");
    assert_registered(&env, "NNVerify.ECLipsE.contraction_compose_axiom");
}

// ---------------------------------------------------------------
// Type checking tests (definitions)
// ---------------------------------------------------------------

#[test]
fn test_rat_pow_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.rat_pow");
}

#[test]
fn test_width_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.width");
}

#[test]
fn test_refine_op_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.refine_op");
}

#[test]
fn test_refine_apply_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.refine_apply");
}

#[test]
fn test_log_rat_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.log_rat");
}

#[test]
fn test_ceil_nat_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.ceil_nat");
}

// ---------------------------------------------------------------
// Type checking tests (theorems)
// ---------------------------------------------------------------

#[test]
fn test_c003a_geometric_decay_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.geometric_decay");
}

#[test]
fn test_c003b_termination_bound_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.termination_bound");
}

#[test]
fn test_c003c_fixed_point_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.fixed_point");
}

#[test]
fn test_c003d_contraction_compose_type_checks() {
    assert_type_checks_as_pi(&make_env(), "NNVerify.ECLipsE.contraction_compose");
}

// ---------------------------------------------------------------
// Kind tests
// ---------------------------------------------------------------

#[test]
fn test_definitions_are_opaque() {
    let env = make_env();
    let def_names = [
        "NNVerify.ECLipsE.rat_pow",
        "NNVerify.ECLipsE.width",
        "NNVerify.ECLipsE.refine_op",
        "NNVerify.ECLipsE.refine_apply",
        "NNVerify.ECLipsE.log_rat",
        "NNVerify.ECLipsE.ceil_nat",
    ];
    for name in &def_names {
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
}

#[test]
fn test_theorem_backing_opaques_exist() {
    let env = make_env();
    // Upgraded from Axiom to Opaque with sorry-based proof inhabitation (#3381).
    let opaque_names = [
        "NNVerify.ECLipsE.geometric_decay_axiom",
        "NNVerify.ECLipsE.termination_bound_axiom",
        "NNVerify.ECLipsE.fixed_point_axiom",
        "NNVerify.ECLipsE.contraction_compose_axiom",
    ];
    for name in &opaque_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Opaque,
            "{name} should be Opaque (upgraded from Axiom #3381), got {:?}",
            info.kind
        );
    }
}

#[test]
fn test_theorems_are_theorems() {
    let env = make_env();
    let thm_names = [
        "NNVerify.ECLipsE.geometric_decay",
        "NNVerify.ECLipsE.termination_bound",
        "NNVerify.ECLipsE.fixed_point",
        "NNVerify.ECLipsE.contraction_compose",
    ];
    for name in &thm_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be Theorem, got {:?}",
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
    assert_registered(&env, "NNVerify.Lipschitz.constant");
    assert_registered(&env, "NNVerify.Lipschitz.residual_block");
    assert_registered(&env, "NNVerify.Lipschitz.lip_product");
}

#[test]
fn test_eq_and_exists_deps_present() {
    let env = make_env();
    assert_registered(&env, "Eq");
    assert_registered(&env, "And");
    assert_registered(&env, "Exists");
}

// ---------------------------------------------------------------
// Naming convention test
// ---------------------------------------------------------------

#[test]
fn test_naming_convention() {
    let env = make_env();
    let all_names = [
        "NNVerify.ECLipsE.rat_pow",
        "NNVerify.ECLipsE.width",
        "NNVerify.ECLipsE.refine_op",
        "NNVerify.ECLipsE.refine_apply",
        "NNVerify.ECLipsE.log_rat",
        "NNVerify.ECLipsE.ceil_nat",
        "NNVerify.ECLipsE.geometric_decay",
        "NNVerify.ECLipsE.geometric_decay_axiom",
        "NNVerify.ECLipsE.termination_bound",
        "NNVerify.ECLipsE.termination_bound_axiom",
        "NNVerify.ECLipsE.fixed_point",
        "NNVerify.ECLipsE.fixed_point_axiom",
        "NNVerify.ECLipsE.contraction_compose",
        "NNVerify.ECLipsE.contraction_compose_axiom",
    ];
    for name in &all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
        assert!(
            name.starts_with("NNVerify.ECLipsE."),
            "{name} must use NNVerify.ECLipsE. prefix"
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_eclipse_convergence()
        .expect("first init");
    env.init_nn_verify_eclipse_convergence()
        .expect("second init (idempotent)");
}

// ---------------------------------------------------------------
// Declaration count test
// ---------------------------------------------------------------

#[test]
fn test_declaration_count() {
    let env = make_env();
    // 6 definitions + 4 theorem axioms + 4 theorems = 14
    let all_names = [
        "NNVerify.ECLipsE.rat_pow",
        "NNVerify.ECLipsE.width",
        "NNVerify.ECLipsE.refine_op",
        "NNVerify.ECLipsE.refine_apply",
        "NNVerify.ECLipsE.log_rat",
        "NNVerify.ECLipsE.ceil_nat",
        "NNVerify.ECLipsE.geometric_decay",
        "NNVerify.ECLipsE.geometric_decay_axiom",
        "NNVerify.ECLipsE.termination_bound",
        "NNVerify.ECLipsE.termination_bound_axiom",
        "NNVerify.ECLipsE.fixed_point",
        "NNVerify.ECLipsE.fixed_point_axiom",
        "NNVerify.ECLipsE.contraction_compose",
        "NNVerify.ECLipsE.contraction_compose_axiom",
    ];
    for name in &all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} missing — expected 14 declarations"
        );
    }
}
