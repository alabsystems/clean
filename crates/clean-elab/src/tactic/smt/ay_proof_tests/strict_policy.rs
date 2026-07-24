// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

#[test]
#[serial]
fn test_select_verified_certificate_proof_verifystrict_rejects_trusted_direct_proof_without_recovery(
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
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect_err("VerifyStrict should reject a trusted direct certificate proof without recovery");
    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "test_cert" && detail.contains("failing closed")
        ),
        "strict failure should preserve the tactic name and fail-closed detail: {err:?}"
    );

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict rejection must not mirror the direct trustedAy debt"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict rejection without recovery must not claim reconstruction success"
    );
}

#[test]
#[serial]
fn test_select_verified_certificate_proof_verifystrict_recovers_instead_of_accepting_trusted_direct_proof(
) {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let trusted_ay_proof = trusted_ay_proof(target.clone());

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(trusted_ay_proof.clone()),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("VerifyStrict should reuse recovery instead of accepting the trusted direct proof");

    assert_ne!(
        returned, trusted_ay_proof,
        "VerifyStrict should not accept the trusted direct certificate proof unchanged"
    );
    assert_certificate_recovery_avoids_non_ay_fallbacks(
        &state,
        "VerifyStrict certificate recovery",
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict recovery should avoid mirroring the rejected direct trustedAy debt"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "strict recovery should record reconstruction success"
    );
}

/// Regression: the public DRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_UF`. Part of #2691.
#[test]
#[serial]
fn test_ay_decide_with_proof_verifystrict_qf_uf_rejects_same_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfUf,
        |state, config| ay_decide_with_proof(state, config, contradiction_drat_proof()),
    );
    let err = result.expect_err(
        "VerifyStrict + QF_UF should fail closed when the only DRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_proof" && detail.contains("failing closed")
        ),
        "strict DRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_UF case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict DRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_UF should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_UF rejection should not record reconstruction success"
    );
}

/// Regression: the public LRAT entrypoint must reject the same trusted bridge
/// candidate under `VerifyStrict + QF_UF`. Part of #2691.
#[test]
#[serial]
fn test_ay_decide_with_lrat_proof_verifystrict_qf_uf_rejects_same_trusted_recovery_candidate() {
    let (state, result, ay_delta) = run_verifystrict_public_certificate_with_injected_candidate(
        AyLogic::QfUf,
        |state, config| ay_decide_with_lrat_proof(state, config, contradiction_lrat_proof()),
    );
    let err = result.expect_err(
        "VerifyStrict + QF_UF should fail closed when the only LRAT recovery candidate carries trust debt",
    );

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "ay_decide_with_lrat_proof" && detail.contains("failing closed")
        ),
        "strict LRAT rejection should preserve fail-closed detail: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "failing closed should leave the goal open for the strict QF_UF case"
    );
    assert_eq!(
        ay_delta, 0,
        "strict LRAT rejection must not synthesize whole-goal trustedAy fallback"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "QF_UF should reject the injected trusted bridge candidate"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_UF rejection should not record reconstruction success"
    );
}

/// When a verified certificate produces no direct kernel proof and the policy
/// is `VerifyStrict + QF_UF`, recovery must use the zero-trust bridge variant
/// so that only candidates with `trust_subterm_count == 0` are accepted.
/// Part of #2684.
#[test]
#[serial]
fn test_select_verified_certificate_proof_verifystrict_none_proof_uses_zero_trust_recovery() {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        None,
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("VerifyStrict + QF_UF with no direct proof should recover via zero-trust bridge");

    assert_ne!(
        returned,
        Expr::prop(),
        "recovered proof should be a real proof term, not a placeholder"
    );
    assert_certificate_recovery_avoids_non_ay_fallbacks(
        &state,
        "VerifyStrict certificate zero-trust recovery (None proof)",
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "zero-trust recovery must not accept a candidate with embedded trustedAy debt"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "zero-trust bridge recovery should record reconstruction success"
    );
}

/// Non-strict policies with no direct kernel proof should use the permissive
/// recovery helper, preserving existing behavior. Part of #2684.
#[test]
#[serial]
fn test_select_verified_certificate_proof_non_strict_none_proof_uses_permissive_recovery() {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        None,
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("non-strict policy with no direct proof should recover via permissive fallback");

    assert_ne!(
        returned,
        Expr::prop(),
        "recovered proof should be a real proof term"
    );
    assert_certificate_recovery_avoids_non_ay_fallbacks(
        &state,
        "non-strict certificate permissive recovery (None proof)",
    );
}
