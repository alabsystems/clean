// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

#[test]
#[serial]
fn test_select_verified_certificate_proof_verifystrict_qf_lia_rejects_trusted_direct_proof_without_recovery(
) {
    reset_all_trust_counters();
    let mut state = ProofState::new(setup_certificate_env(), prop_p());
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let trusted_ay_proof = trusted_ay_proof(target.clone());

    let err = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(trusted_ay_proof),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfLia,
        "test_cert",
        "DRAT",
    )
    .expect_err(
        "VerifyStrict + QF_LIA should reject a trusted direct certificate proof without recovery",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "test_cert" && detail.contains("failing closed")
        ),
        "strict QF_LIA failure should preserve the tactic name and fail-closed detail: {err:?}"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LIA rejection without recovery must not claim reconstruction success"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict QF_LIA rejection must not mirror the direct trustedAy debt"
    );
}

#[test]
#[serial]
fn test_select_verified_certificate_proof_verifystrict_qf_lra_rejects_trusted_direct_proof_without_recovery(
) {
    reset_all_trust_counters();
    let mut state = ProofState::new(setup_certificate_env(), prop_p());
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let trusted_ay_proof = trusted_ay_proof(target.clone());

    let err = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(trusted_ay_proof),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfLra,
        "test_cert",
        "DRAT",
    )
    .expect_err(
        "VerifyStrict + QF_LRA should reject a trusted direct certificate proof without recovery",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "test_cert" && detail.contains("failing closed")
        ),
        "strict QF_LRA failure should preserve the tactic name and fail-closed detail: {err:?}"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LRA rejection without recovery must not claim reconstruction success"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict QF_LRA rejection must not mirror the direct trustedAy debt"
    );
}

/// Regression: the public DRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_LIA`. Part of #2756.
#[test]
#[serial]
fn test_ay_decide_with_proof_verifystrict_qf_lia_rejects_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfLia,
        |state, config| ay_decide_with_proof(state, config, contradiction_drat_proof()),
    );

    let err = result.expect_err(
        "VerifyStrict + QF_LIA should fail closed when the only DRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_proof" && detail.contains("failing closed")
        ),
        "strict QF_LIA DRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_LIA case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict QF_LIA DRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_LIA should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LIA rejection should not record reconstruction success"
    );
}

/// Regression: the public DRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_LRA`. Part of #2756.
#[test]
#[serial]
fn test_ay_decide_with_proof_verifystrict_qf_lra_rejects_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfLra,
        |state, config| ay_decide_with_proof(state, config, contradiction_drat_proof()),
    );

    let err = result.expect_err(
        "VerifyStrict + QF_LRA should fail closed when the only DRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_proof" && detail.contains("failing closed")
        ),
        "strict QF_LRA DRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_LRA case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict QF_LRA DRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_LRA should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LRA rejection should not record reconstruction success"
    );
}

/// Regression: the public LRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_LIA`. Part of #2756.
#[test]
#[serial]
fn test_ay_decide_with_lrat_proof_verifystrict_qf_lia_rejects_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfLia,
        |state, config| ay_decide_with_lrat_proof(state, config, contradiction_lrat_proof()),
    );

    let err = result.expect_err(
        "VerifyStrict + QF_LIA should fail closed when the only LRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_lrat_proof" && detail.contains("failing closed")
        ),
        "strict QF_LIA LRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_LIA case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict QF_LIA LRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_LIA should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LIA rejection should not record reconstruction success"
    );
}

/// Regression: the public LRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_LRA`. Part of #2756.
#[test]
#[serial]
fn test_ay_decide_with_lrat_proof_verifystrict_qf_lra_rejects_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfLra,
        |state, config| ay_decide_with_lrat_proof(state, config, contradiction_lrat_proof()),
    );

    let err = result.expect_err(
        "VerifyStrict + QF_LRA should fail closed when the only LRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_lrat_proof" && detail.contains("failing closed")
        ),
        "strict QF_LRA LRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_LRA case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict QF_LRA LRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_LRA should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_LRA rejection should not record reconstruction success"
    );
}
