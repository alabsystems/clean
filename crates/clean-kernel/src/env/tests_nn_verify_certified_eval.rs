// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for certified computation mode (NNVerify.certified_eval).
//!
//! Validates that all 5 definitions and 5 axioms are correctly registered,
//! type-check through the kernel, and follow the NNVerify. naming convention.
//!
//! Part of #3186.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_certified_eval()
        .expect("init_nn_verify_certified_eval");
    env
}

// ── Definition registration ──────────────────────────────────────────

#[test]
fn test_certified_eval_concrete_input_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.concrete_input"))
            .is_some(),
        "NNVerify.concrete_input should be registered"
    );
}

#[test]
fn test_certified_eval_concrete_output_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.concrete_output"))
            .is_some(),
        "NNVerify.concrete_output should be registered"
    );
}

#[test]
fn test_certified_eval_eval_trace_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.eval_trace"))
            .is_some(),
        "NNVerify.eval_trace should be registered"
    );
}

#[test]
fn test_certified_eval_eval_certificate_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.eval_certificate"))
            .is_some(),
        "NNVerify.eval_certificate should be registered"
    );
}

#[test]
fn test_certified_eval_eval_matches_spec_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.eval_matches_spec"))
            .is_some(),
        "NNVerify.eval_matches_spec should be registered"
    );
}

// ── Definition type checking ──────────────────────────────────────────

#[test]
fn test_certified_eval_concrete_input_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let info = env
        .get_const(&Name::from_string("NNVerify.concrete_input"))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_certified_eval_concrete_output_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let info = env
        .get_const(&Name::from_string("NNVerify.concrete_output"))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_certified_eval_eval_trace_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_trace"))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_certified_eval_eval_certificate_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_certificate"))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

#[test]
fn test_certified_eval_eval_matches_spec_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_matches_spec"))
        .expect("should exist");
    assert_eq!(info.kind, ConstantKind::Definition);
    let val = info.value.as_ref().expect("definition should have value");
    let inferred = tc.infer_type(val).expect("should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type should match declared type"
    );
}

// ── Axiom registration ───────────────────────────────────────────────

#[test]
fn test_certified_eval_trace_sound_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_trace_sound"))
        .expect("NNVerify.eval_trace_sound should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
}

#[test]
fn test_certified_eval_certificate_complete_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_certificate_complete"))
        .expect("NNVerify.eval_certificate_complete should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
}

#[test]
fn test_certified_eval_deterministic_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_deterministic"))
        .expect("NNVerify.eval_deterministic should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
}

#[test]
fn test_certified_eval_composition_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.certified_eval_composition"))
        .expect("NNVerify.certified_eval_composition should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
}

#[test]
fn test_certified_eval_within_bounds_registered() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.eval_within_bounds"))
        .expect("NNVerify.eval_within_bounds should be registered");
    assert_eq!(info.kind, ConstantKind::Axiom);
}

// ── Axiom type shapes ────────────────────────────────────────────────

#[test]
fn test_certified_eval_trace_sound_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let c = crate::expr::Expr::const_(Name::from_string("NNVerify.eval_trace_sound"), vec![]);
    let ty = tc.infer_type(&c).expect("infer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "eval_trace_sound should have Pi type"
    );
}

#[test]
fn test_certified_eval_certificate_complete_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let c = crate::expr::Expr::const_(
        Name::from_string("NNVerify.eval_certificate_complete"),
        vec![],
    );
    let ty = tc.infer_type(&c).expect("infer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "eval_certificate_complete should have Pi type"
    );
}

#[test]
fn test_certified_eval_deterministic_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let c = crate::expr::Expr::const_(Name::from_string("NNVerify.eval_deterministic"), vec![]);
    let ty = tc.infer_type(&c).expect("infer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "eval_deterministic should have Pi type"
    );
}

#[test]
fn test_certified_eval_composition_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let c = crate::expr::Expr::const_(
        Name::from_string("NNVerify.certified_eval_composition"),
        vec![],
    );
    let ty = tc.infer_type(&c).expect("infer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "certified_eval_composition should have Pi type"
    );
}

#[test]
fn test_certified_eval_within_bounds_type_is_pi() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let c = crate::expr::Expr::const_(Name::from_string("NNVerify.eval_within_bounds"), vec![]);
    let ty = tc.infer_type(&c).expect("infer type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "eval_within_bounds should have Pi type"
    );
}

// ── Naming convention ────────────────────────────────────────────────

#[test]
fn test_certified_eval_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.concrete_input",
        "NNVerify.concrete_output",
        "NNVerify.eval_trace",
        "NNVerify.eval_certificate",
        "NNVerify.eval_matches_spec",
        "NNVerify.eval_trace_sound",
        "NNVerify.eval_certificate_complete",
        "NNVerify.eval_deterministic",
        "NNVerify.certified_eval_composition",
        "NNVerify.eval_within_bounds",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered with NNVerify. prefix",
            name,
        );
    }
}

// ── Idempotency ──────────────────────────────────────────────────────

#[test]
fn test_certified_eval_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_certified_eval().expect("first init");
    env.init_nn_verify_certified_eval()
        .expect("second init should be idempotent");
}

// ── No sorry ─────────────────────────────────────────────────────────

#[test]
fn test_certified_eval_definitions_no_sorry() {
    let env = make_env();
    let defs = [
        "NNVerify.concrete_input",
        "NNVerify.concrete_output",
        "NNVerify.eval_trace",
        "NNVerify.eval_certificate",
        "NNVerify.eval_matches_spec",
    ];
    for name in &defs {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{} should exist", name));
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "{} should not use sorry", name,);
    }
}
