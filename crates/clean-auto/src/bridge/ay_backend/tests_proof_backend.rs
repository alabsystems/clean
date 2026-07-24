// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for AyProofBackend constructors, variable generation, assertions,
//! reset, scoping, and quantifier trigger formatting.

use super::proof_backend::{AyProofBackend, AyProofResult};
use super::triggers::SmtlibTriggerPattern;
use super::{AyBackendConfig, AyLogic, ProofProfile, TrustBudget, VariableMapping};
use clean_kernel::name::Name;
use clean_kernel::Expr;

#[test]
fn test_new_default_creates_backend_with_logic() {
    let backend = AyProofBackend::new_default(AyLogic::QfLia);
    assert_eq!(backend.logic(), AyLogic::QfLia);
    assert!(!backend.config().produces_proofs());
    assert!(backend.assertions.is_empty());
    assert!(backend.declarations.is_empty());
    assert_eq!(backend.fresh_counter, 0);
}

#[test]
fn test_new_with_proofs_enables_proof_production() {
    let backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    assert_eq!(backend.logic(), AyLogic::QfUf);
    assert!(backend.config().produces_proofs());
}

#[test]
fn test_fresh_int_increments_counter_and_declares() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    let name1 = backend.fresh_int("x");
    assert_eq!(backend.fresh_counter, 1);
    assert_eq!(backend.declarations.len(), 1);
    assert!(backend.declarations[0].contains("Int"));

    let name2 = backend.fresh_int("y");
    assert_eq!(backend.fresh_counter, 2);
    assert_eq!(backend.declarations.len(), 2);
    assert_ne!(name1, name2);
}

#[test]
fn test_fresh_bool_declares_bool_sort() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfUf);
    let name = backend.fresh_bool("b");
    assert_eq!(backend.declarations.len(), 1);
    assert!(
        backend.declarations[0].contains("Bool"),
        "declaration should contain Bool: {}",
        backend.declarations[0]
    );
    assert!(name.contains("b_0"));
}

#[test]
fn test_fresh_real_declares_real_sort() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLra);
    let _name = backend.fresh_real("r");
    assert_eq!(backend.declarations.len(), 1);
    assert!(backend.declarations[0].contains("Real"));
}

#[test]
fn test_assert_formula_wraps_in_assert() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    backend.assert_formula("(= x 1)");
    assert_eq!(backend.assertions.len(), 1);
    assert_eq!(backend.assertions[0], "(assert (= x 1))");
}

#[test]
fn test_reset_clears_all_state() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    backend.fresh_int("x");
    backend.assert_formula("(= x 1)");
    backend.last_problem = "something".to_string();

    backend.reset();

    assert!(backend.assertions.is_empty());
    assert!(backend.declarations.is_empty());
    assert_eq!(backend.fresh_counter, 0);
    assert!(backend.last_problem.is_empty());
}

#[test]
fn test_push_pop_add_scope_markers() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    backend.push();
    assert_eq!(backend.assertions.last().unwrap(), "(push 1)");

    backend.assert_formula("(= x 1)");
    backend.pop();
    assert_eq!(backend.assertions.last().unwrap(), "(pop 1)");
    assert_eq!(backend.assertions.len(), 3); // push + assert + pop
}

#[test]
fn test_forall_with_triggers_no_triggers() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let result = backend.forall_with_triggers(&[("x", "Int"), ("y", "Int")], "(> (+ x y) 0)", &[]);
    assert_eq!(result, "(forall ((x Int) (y Int)) (> (+ x y) 0))");
}

#[test]
fn test_forall_with_triggers_single_trigger() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let trigger = SmtlibTriggerPattern::single("(f x)");
    let result = backend.forall_with_triggers(&[("x", "Int")], "(> (f x) 0)", &[trigger]);
    assert!(
        result.contains(":pattern"),
        "should contain trigger: {result}"
    );
    assert!(
        result.contains("(f x)"),
        "should contain trigger term: {result}"
    );
}

#[test]
fn test_exists_with_triggers_produces_exists() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let result = backend.exists_with_triggers(&[("x", "Int")], "(= x 42)", &[]);
    assert!(
        result.starts_with("(exists"),
        "should start with exists: {result}"
    );
}

#[test]
fn test_with_config_proof_profile_enables_proofs() {
    let config =
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::carcara_verified());
    let backend = AyProofBackend::with_config(config);
    assert!(backend.config().produces_proofs());
    assert_eq!(
        backend
            .config()
            .profile()
            .expect("proof profile should stay attached to the backend config")
            .verification_tier(),
        1
    );
}

#[test]
fn test_attempt_kernel_reconstruction_returns_none_without_last_proof() {
    let backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    let neg_false = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert!(
        backend
            .attempt_kernel_reconstruction(&VariableMapping::new(), &neg_false)
            .is_none(),
        "no proof should yield no accepted reconstruction candidate"
    );
}

#[test]
fn test_attempt_kernel_reconstruction_with_budget_returns_none_without_last_proof() {
    let backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    let neg_false = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert!(
        backend
            .attempt_kernel_reconstruction_with_budget(
                &VariableMapping::new(),
                &neg_false,
                TrustBudget::ZeroTrust,
            )
            .is_none(),
        "no proof should yield no accepted reconstruction candidate under any budget"
    );
}

#[test]
fn test_check_sat_simple_sat() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    backend.fresh_int("x");
    backend.assert_formula("(> x_0 0)");
    let result = backend.check_sat().unwrap();
    assert!(
        matches!(result, AyProofResult::Sat),
        "x > 0 should be satisfiable"
    );
}
