// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Solve provenance regressions for the clean ay backend.

use super::*;
use num_bigint::BigInt;

#[test]
fn test_basic_sat_preserves_validation_provenance() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);

    let result = backend.check_sat();
    assert_eq!(result, AySolveResult::Sat);
    assert!(
        result.was_model_validated(),
        "SAT solve should preserve model-validation provenance"
    );
    let verification = result
        .verification()
        .expect("SAT solve should retain verification metadata");
    assert!(
        verification.summary.sat_model_validated,
        "SAT solve should retain the model-validation flag in the verification summary"
    );
    assert_eq!(
        result.verification_summary(),
        Some(verification.summary),
        "summary accessor should expose the retained verification counters"
    );
    assert_eq!(
        result.verification_level(),
        Some(verification.level),
        "level accessor should expose the retained runtime verification mode"
    );
    assert_eq!(result.unknown_reason(), None);
    assert_eq!(result.panic_reason(), None);
}

#[test]
fn test_zero_timeout_preserves_unknown_reason() {
    let config = AyBackendConfig::new(AyLogic::QfLia).timeout(0);
    let mut backend = AyBackend::with_config(config);

    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);

    let result = backend.check_sat();
    assert_eq!(result, AySolveResult::Unknown);
    assert_eq!(result.unknown_reason(), Some(AyUnknownReason::Timeout));
    assert!(
        result.verification_summary().is_some(),
        "timeout solves should still preserve verification counters from the detailed solve path"
    );
    assert!(
        result.verification_level().is_some(),
        "timeout solves should still preserve the runtime verification level"
    );
    assert_eq!(result.panic_reason(), None);
}

#[test]
fn test_fp_to_real_sat_preserves_validation_provenance() {
    let mut backend = AyBackend::new(AyLogic::QfFp);
    let x = backend
        .solver
        .declare_const("x", ay::Sort::FloatingPoint(5, 11));
    let r = backend.solver.declare_const("r", ay::Sort::Real);
    let fp_to_real = backend
        .solver
        .try_fp_to_real(x)
        .expect("QfFp solver should support fp.to_real");
    let eq = backend
        .solver
        .try_eq(r, fp_to_real)
        .expect("eq over Real terms should succeed");
    backend.assert_term(AyTerm::from_inner(eq));
    let one = backend.real_const(1.0);
    let gt = backend
        .solver
        .try_gt(r, one.into_inner())
        .expect("gt over Real terms should succeed");
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
    assert_eq!(result.panic_reason(), None);
}

#[test]
fn test_panic_unknown_exposes_no_verification_metadata() {
    let result = AySolveEnvelope::PanicUnknown {
        panic_reason: "panic".to_string(),
    };

    assert_eq!(result.verification(), None);
    assert_eq!(result.verification_summary(), None);
    assert_eq!(result.verification_level(), None);
}

#[test]
fn test_get_model_returns_legacy_model_after_verified_sat() {
    let mut backend = AyBackend::new(AyLogic::QfLia);
    let x = backend.fresh_int("x");
    let one = backend.int_const(1);
    let x_eq_one = backend.eq(x, one);
    backend.assert_term(x_eq_one);

    let result = backend.check_sat();
    assert_eq!(result, AySolveResult::Sat);

    let model = backend
        .get_model()
        .expect("SAT solve should expose a legacy Model after VerifiedModel unwrap");
    assert_eq!(
        model.int_val("x0"),
        Some(&BigInt::from(1u8)),
        "legacy Model API should expose the exact SAT assignment after VerifiedModel unwrap"
    );
}
