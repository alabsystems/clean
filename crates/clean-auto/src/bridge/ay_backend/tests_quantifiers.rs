// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier-focused tests for the ay backend term API.

use super::*;

/// Test basic forall quantifier creation
///
/// # Contract
///
/// VERIFIES: `forall` creates a valid term that can be asserted
/// VERIFIES: API returns `Ok` for valid quantified formulas
///
/// Note: ay typically returns Unknown for quantified formulas as it uses
/// CDCL+E-matching which cannot prove validity, only satisfiability.
#[test]
fn test_forall_basic() {
    let mut backend = AyBackend::new(AyLogic::Uf);

    // forall x. x = x (trivially true, but ay may return Unknown)
    let x = backend.fresh_int("x");
    let x_eq_x = backend.eq(x, x);
    let quantified = backend
        .forall(&[x], x_eq_x)
        .expect("valid quantified formula");

    backend.assert_term(quantified);
    // ay may return Sat or Unknown for quantified formulas (CDCL+E-matching
    // cannot prove validity), but must never return Unsat for a tautology
    let result = backend.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "forall x. x = x should be Sat or Unknown, got {:?}",
        result
    );
}

/// Test forall with user-provided trigger patterns
///
/// # Contract
///
/// VERIFIES: Triggered quantifier construction returns `Ok` for valid input
/// VERIFIES: Trigger patterns are passed through to ay
/// VERIFIES: Result is Sat or Unknown (not Unsat for tautology)
///
/// Note: ay may return Unknown for quantified formulas.
#[test]
fn test_forall_with_triggers() {
    let mut backend = AyBackend::new(AyLogic::Uflia);

    // Declare bound variable
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_plus_zero = backend.add(x, zero);

    // forall x. x = x with trigger (x + 0)
    let x_eq_x = backend.eq(x, x);
    let triggers = vec![AyTriggerPattern::single(x_plus_zero)];
    let quantified = backend
        .forall_with_triggers(&[x], x_eq_x, &triggers)
        .expect("valid quantified formula");

    backend.assert_term(quantified);
    let result = backend.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "forall x. x = x (with triggers) should be Sat or Unknown, got {:?}",
        result
    );
}

/// Test basic exists quantifier creation
///
/// # Contract
///
/// VERIFIES: `exists` creates a valid term that can be asserted
/// VERIFIES: Result is Sat or Unknown (not Unsat for trivially satisfiable formula)
///
/// Note: ay may return Unknown or Sat for existentials depending on the formula.
#[test]
fn test_exists_basic() {
    let mut backend = AyBackend::new(AyLogic::Uf);

    // exists x. x = x (trivially satisfiable)
    let x = backend.fresh_int("x");
    let x_eq_x = backend.eq(x, x);
    let quantified = backend
        .exists(&[x], x_eq_x)
        .expect("valid quantified formula");

    backend.assert_term(quantified);
    let result = backend.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "exists x. x = x should be Sat or Unknown, got {:?}",
        result
    );
}

/// Test exists with user-provided trigger patterns
///
/// # Contract
///
/// VERIFIES: Triggered existential construction returns `Ok` for valid input
/// VERIFIES: Trigger patterns are passed through to ay
/// VERIFIES: Result is Sat or Unknown (not Unsat)
///
/// Note: ay may return Unknown for quantified formulas.
#[test]
fn test_exists_with_triggers() {
    let mut backend = AyBackend::new(AyLogic::Uflia);

    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_plus_zero = backend.add(x, zero);

    // exists x. x = x with trigger (x + 0)
    let x_eq_x = backend.eq(x, x);
    let triggers = vec![AyTriggerPattern::single(x_plus_zero)];
    let quantified = backend
        .exists_with_triggers(&[x], x_eq_x, &triggers)
        .expect("valid quantified formula");

    backend.assert_term(quantified);
    let result = backend.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "exists x. x = x (with triggers) should be Sat or Unknown, got {:?}",
        result
    );
}

/// Test multi-pattern triggers
///
/// # Contract
///
/// VERIFIES: Multi-patterns (multiple terms in one pattern) work correctly
/// VERIFIES: Multi-patterns are passed through to ay with a successful `Ok` result
/// VERIFIES: Result is Sat or Unknown (not Unsat)
///
/// Note: ay may return Unknown for quantified formulas.
#[test]
fn test_multi_pattern_triggers() {
    let mut backend = AyBackend::new(AyLogic::Uflia);

    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let one = backend.int_const(1);
    let x_plus_zero = backend.add(x, zero);
    let x_times_one = backend.mul(x, one);

    // forall x. x = x with multi-pattern trigger {x + 0, x * 1}
    let x_eq_x = backend.eq(x, x);
    let multi_trigger = AyTriggerPattern::multi(vec![x_plus_zero, x_times_one]);
    let quantified = backend
        .forall_with_triggers(&[x], x_eq_x, &[multi_trigger])
        .expect("valid quantified formula");

    backend.assert_term(quantified);
    let result = backend.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "forall x. x = x (multi-pattern) should be Sat or Unknown, got {:?}",
        result
    );
}

#[test]
fn test_forall_invalid_body_returns_type_mismatch() {
    let mut backend = AyBackend::new(AyLogic::Uf);
    let x = backend.fresh_int("x");

    let err = backend
        .forall(&[x], x)
        .expect_err("non-Bool quantifier body should be rejected");

    assert!(matches!(
        err,
        AyError::TypeMismatch { expected, got } if expected == "Bool" && got == "Int"
    ));
}

#[test]
fn test_forall_invalid_trigger_returns_invalid_input() {
    let mut backend = AyBackend::new(AyLogic::Uflia);
    let x = backend.fresh_int("x");
    let y = backend.fresh_int("y");
    let one = backend.int_const(1);
    let body = backend.eq(x, x);
    let unrelated_trigger = backend.add(y, one);

    let err = backend
        .forall_with_triggers(&[x], body, &[AyTriggerPattern::single(unrelated_trigger)])
        .expect_err("trigger without a bound variable should be rejected");

    assert!(matches!(
        err,
        AyError::InvalidInput { operation, message }
            if operation == "forall_with_triggers"
                && message.contains("trigger must contain at least one bound variable")
    ));
}

/// Test convert_triggers helper function
///
/// # Contract
///
/// VERIFIES: Conversion preserves trigger structure
/// VERIFIES: Empty triggers are handled correctly
#[test]
fn test_convert_triggers_helper() {
    let mut backend = AyBackend::new(AyLogic::Uf);
    let x = backend.fresh_int("x");
    let y = backend.fresh_int("y");

    // Test single pattern
    let single = AyTriggerPattern::single(x);
    let converted = AyBackend::convert_triggers(&[single]);
    assert_eq!(converted.len(), 1);
    assert_eq!(converted[0].len(), 1);

    // Test multi-pattern
    let multi = AyTriggerPattern::multi(vec![x, y]);
    let converted = AyBackend::convert_triggers(&[multi]);
    assert_eq!(converted.len(), 1);
    assert_eq!(converted[0].len(), 2);

    // Test empty triggers
    let empty: Vec<AyTriggerPattern> = vec![];
    let converted = AyBackend::convert_triggers(&empty);
    assert!(converted.is_empty());

    // Test multiple trigger groups
    let group1 = AyTriggerPattern::single(x);
    let group2 = AyTriggerPattern::single(y);
    let converted = AyBackend::convert_triggers(&[group1, group2]);
    assert_eq!(converted.len(), 2);
    assert_eq!(converted[0].len(), 1);
    assert_eq!(converted[1].len(), 1);
}
