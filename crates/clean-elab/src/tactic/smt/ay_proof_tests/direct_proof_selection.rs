// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

/// When a certificate-reconstructed proof term contains embedded `trustedAy`
/// sub-terms, `select_verified_certificate_proof` must mirror them into the
/// proof-state trust ledger so downstream accounting sees the exact debt.
#[test]
#[serial]
fn test_select_verified_certificate_proof_mirrors_trust_subterms_to_ledger() {
    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::new(setup_certificate_env(), prop_p());
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let trusted_ay_proof = trusted_ay_proof(prop_p());

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(trusted_ay_proof.clone()),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("non-strict direct certificate proof should remain selectable");

    assert_eq!(
        returned, trusted_ay_proof,
        "direct proof term should be returned unchanged"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        1,
        "embedded trustedAy sub-term should be mirrored to the proof-state trust ledger"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "direct certificate proof selection should not claim ay reconstruction success"
    );
}

/// When a verified certificate produces a trusted direct proof but the native
/// bridge can reconstruct the same goal without trust, prefer the bridge proof.
#[test]
#[serial]
fn test_select_verified_certificate_proof_prefers_lower_trust_bridge_candidate() {
    reset_local_ay_reconstruction_success_counter();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let trusted_ay_proof = trusted_ay_proof(target.clone());

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(trusted_ay_proof.clone()),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("bridge-backed certificate selection should not fail");

    assert_ne!(
        returned, trusted_ay_proof,
        "certificate selector should prefer the lower-trust bridge proof when available"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "bridge-selected certificate proof should avoid mirroring direct trustedAy debt"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "choosing the bridge proof should record ay reconstruction success"
    );
    assert!(
        !state.trust_ledger().smt_recovery.has_events(),
        "selection-only bridge probe must not mutate smt_recovery counters"
    );
}

/// A clean certificate proof (no `trustedAy` sub-terms) should leave the trust
/// ledger at zero — the trust-mirroring call does not create spurious debt.
#[test]
fn test_select_verified_certificate_proof_clean_proof_leaves_ledger_zero() {
    let mut state = ProofState::with_context(
        setup_certificate_env(),
        prop_p(),
        vec![LocalDecl {
            fvar: FVarId::new(3),
            name: "hp".to_string(),
            ty: prop_p(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let clean_proof = Expr::fvar(FVarId::new(3));

    let _ = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(clean_proof),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
        "test_cert",
        "LRAT",
    )
    .expect("Clean certificate proof should remain selectable under VerifyStrict");

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "clean proof should leave zero trustedAy debt in the ledger"
    );
}

#[test]
#[serial]
fn test_select_verified_certificate_proof_rejects_invalid_clean_direct_proof_and_recovers() {
    reset_all_trust_counters();
    let mut state = contradiction_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);
    let invalid_direct_proof = Expr::type_();

    let returned = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(invalid_direct_proof.clone()),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect("invalid clean certificate proof should fall back to checked recovery");

    assert_ne!(
        returned, invalid_direct_proof,
        "certificate selector must not accept the invalid direct proof unchanged"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "recovering after rejecting an invalid direct proof must not add trust debt"
    );
    assert_eq!(
        state
            .trust_ledger()
            .smt_recovery
            .invalid_direct_certificate_candidates,
        1,
        "rejecting an invalid certificate direct proof must record one recovery event"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "certificate recovery after invalid direct proof should record reconstruction success"
    );
}

#[test]
#[serial]
fn test_select_verified_certificate_proof_preserves_validation_failure_when_recovery_exhausts() {
    reset_all_trust_counters();
    let mut state = ProofState::new(setup_certificate_env(), prop_p());
    let goal = state.current_goal().expect("should have a goal").clone();
    let target = state.metas.instantiate(&goal.target);

    let err = select_verified_certificate_proof_for_test(
        &mut state,
        &goal,
        &target,
        Some(Expr::type_()),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
        "test_cert",
        "DRAT",
    )
    .expect_err("invalid certificate direct proof without recovery should fail closed");

    assert!(
        matches!(
            &err,
            TacticError::SmtFailed { tactic, detail }
                if tactic == "test_cert"
                    && detail.contains("DRAT direct proof failed kernel validation before selection")
                    && detail.contains("recovery also failed")
        ),
        "certificate selector should preserve the validation failure after recovery exhaustion: {err:?}"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "failing closed after invalid certificate proof should not add trust debt"
    );
    assert_eq!(
        state
            .trust_ledger()
            .smt_recovery
            .invalid_direct_certificate_candidates,
        1,
        "failing closed still records the rejected invalid certificate candidate"
    );
}
