// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trigger API coverage tests.

use super::*;

#[test]
fn test_trigger_pattern_single() {
    let mut backend = AyBackend::new(AyLogic::QfUf);
    let x = backend.fresh_int("x");

    // Create a single-term trigger
    let trigger = AyTriggerPattern::single(x);
    assert!(!trigger.is_empty());
    assert_eq!(trigger.len(), 1);
}

#[test]
fn test_trigger_pattern_multi() {
    let mut backend = AyBackend::new(AyLogic::QfUf);
    let x = backend.fresh_int("x");
    let y = backend.fresh_int("y");

    // Create a multi-term trigger
    let trigger = AyTriggerPattern::multi(vec![x, y]);
    assert!(!trigger.is_empty());
    assert_eq!(trigger.len(), 2);
}

#[test]
fn test_trigger_pattern_empty() {
    let trigger = AyTriggerPattern::default();
    assert!(trigger.is_empty());
    assert_eq!(trigger.len(), 0);
}

#[test]
fn test_trigger_policy_default() {
    // Default should be Auto
    let policy = TriggerPolicy::default();
    assert_eq!(policy, TriggerPolicy::Auto);
}

#[test]
fn test_config_trigger_policy() {
    // Test builder method for trigger policy
    let config = AyBackendConfig::new(AyLogic::QfUf).trigger_policy(TriggerPolicy::UserOnly);
    assert_eq!(config.trigger_policy_value(), TriggerPolicy::UserOnly);

    // Default config should have Auto policy
    let default_config = AyBackendConfig::new(AyLogic::QfUf);
    assert_eq!(default_config.trigger_policy_value(), TriggerPolicy::Auto);
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![
        SmtlibTriggerPattern::single("(f x)"),
        SmtlibTriggerPattern::multi(vec!["(g x)".to_string(), "(h x)".to_string()]),
    ];

    let formula = backend.forall_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(
        formula,
        "(forall ((x Int)) (! (= x x) :pattern ((f x)) :pattern ((g x) (h x))))"
    );
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting_exists() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![SmtlibTriggerPattern::single("(p x)")];

    let formula = backend.exists_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(formula, "(exists ((x Int)) (! (= x x) :pattern ((p x))))");
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting_exists_multi() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![
        SmtlibTriggerPattern::single("(f x)"),
        SmtlibTriggerPattern::multi(vec!["(g x)".to_string(), "(h x)".to_string()]),
    ];

    let formula = backend.exists_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(
        formula,
        "(exists ((x Int)) (! (= x x) :pattern ((f x)) :pattern ((g x) (h x))))"
    );
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting_exists_empty_patterns() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![SmtlibTriggerPattern::default()];

    let formula = backend.exists_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(formula, "(exists ((x Int)) (= x x))");
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting_mixed_empty_patterns() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![
        SmtlibTriggerPattern::default(),
        SmtlibTriggerPattern::single("(f x)"),
    ];

    let formula = backend.forall_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(formula, "(forall ((x Int)) (! (= x x) :pattern ((f x))))");
}

#[test]
fn test_proof_backend_trigger_smtlib_formatting_exists_mixed_empty_patterns() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![
        SmtlibTriggerPattern::default(),
        SmtlibTriggerPattern::single("(f x)"),
    ];

    let formula = backend.exists_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(formula, "(exists ((x Int)) (! (= x x) :pattern ((f x))))");
}

#[test]
fn test_proof_backend_ignores_empty_trigger_patterns() {
    let backend = AyProofBackend::new_default(AyLogic::Uf);
    let triggers = vec![SmtlibTriggerPattern::default()];

    let formula = backend.forall_with_triggers(&[("x", "Int")], "(= x x)", &triggers);

    assert_eq!(formula, "(forall ((x Int)) (= x x))");
}
