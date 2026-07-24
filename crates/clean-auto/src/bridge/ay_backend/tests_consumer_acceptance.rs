// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for the ay consumer acceptance boundary.

use super::*;
use ay::Sort;

#[test]
fn test_fp_to_real_sat_is_validated_at_consumer_boundary() {
    let mut backend = AyBackend::new(AyLogic::All);
    let x = backend
        .solver
        .declare_const("x", Sort::FloatingPoint(5, 11));
    let r = backend.solver.declare_const("r", Sort::Real);
    let fp_to_real = backend
        .solver
        .try_fp_to_real(x)
        .expect("ALL solver should support fp.to_real");
    let eq = backend
        .solver
        .try_eq(r, fp_to_real)
        .expect("test invariant: fp.to_real equality should be well-typed");
    backend.assert_term(AyTerm::from_inner(eq));
    let one = backend.real_const(1.0);
    let gt = backend
        .solver
        .try_gt(r, one.into_inner())
        .expect("test invariant: real comparison should be well-typed");
    backend.assert_term(AyTerm::from_inner(gt));

    let result = backend.check_sat();
    assert_eq!(
        result,
        AySolveResult::Sat,
        "consumer boundary should accept SAT after model validation"
    );
    assert_eq!(result.unknown_reason(), None);
    let verification = result
        .verification()
        .expect("consumer-accepted SAT should retain solve verification metadata");
    assert!(
        verification.summary.sat_model_validated,
        "verification summary must record that model validation ran"
    );
    assert!(
        result.was_model_validated(),
        "consumer-accepted SAT must preserve model-validation provenance"
    );
    assert!(
        backend.get_model().is_some(),
        "consumer-accepted SAT must expose the validated solver model"
    );
    assert_eq!(result.panic_reason(), None);
}

#[test]
fn test_contradiction_yields_consumer_accepted_unsat() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_bool("x");
    let not_x = backend.not(x);
    backend.assert_term(x);
    backend.assert_term(not_x);

    let result = backend.check_sat();
    assert!(
        result.is_unsat(),
        "contradiction must produce UNSAT, got: {:?}",
        result.kind()
    );
    assert_eq!(result.kind(), AySolveResult::Unsat);
    assert_eq!(
        result.panic_reason(),
        None,
        "UNSAT result must not carry a panic payload"
    );
    assert_eq!(
        result.unknown_reason(),
        None,
        "UNSAT result must not carry an unknown reason"
    );
    let verification = result
        .verification()
        .expect("consumer-accepted UNSAT should retain verification metadata");
    assert!(
        !verification.summary.sat_model_validated,
        "UNSAT path should not claim SAT model validation"
    );
    assert!(
        !result.was_model_validated(),
        "UNSAT must not claim model validation"
    );
    assert!(
        backend.get_model().is_none(),
        "UNSAT must not expose a model"
    );
}

#[test]
fn test_trivial_sat_yields_consumer_accepted_sat_with_model() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_bool("x");
    backend.assert_term(x);

    let result = backend.check_sat();
    assert!(
        result.is_sat(),
        "trivially satisfiable formula must produce SAT, got: {:?}",
        result.kind()
    );
    assert_eq!(result.kind(), AySolveResult::Sat);
    assert_eq!(
        result.panic_reason(),
        None,
        "consumer-accepted SAT must not carry a panic payload"
    );
    assert!(
        result.verification().is_some(),
        "consumer-accepted SAT must retain verification metadata"
    );
    assert!(
        backend.get_model().is_some(),
        "consumer-accepted SAT must expose the solver model"
    );
}

#[test]
fn test_panic_unknown_envelope_degrades_all_accessors() {
    let envelope = AySolveEnvelope::PanicUnknown {
        panic_reason: "test: internal solver assertion failed".to_string(),
    };
    assert!(envelope.is_unknown(), "PanicUnknown must report as unknown");
    assert!(!envelope.is_sat(), "PanicUnknown must not report as SAT");
    assert!(
        !envelope.is_unsat(),
        "PanicUnknown must not report as UNSAT"
    );
    assert_eq!(envelope.kind(), AySolveResult::Unknown);
    assert_eq!(
        envelope.panic_reason(),
        Some("test: internal solver assertion failed"),
        "PanicUnknown must preserve the panic payload"
    );
    assert_eq!(
        envelope.unknown_reason(),
        None,
        "PanicUnknown must not carry a structured unknown reason"
    );
    assert!(
        !envelope.was_model_validated(),
        "PanicUnknown must not claim model validation"
    );
    assert!(
        envelope.verification().is_none(),
        "PanicUnknown must not carry verification metadata"
    );
    assert!(
        envelope.verification_summary().is_none(),
        "PanicUnknown must not expose verification summary"
    );
    assert!(
        envelope.verification_level().is_none(),
        "PanicUnknown must not expose verification level"
    );
}
