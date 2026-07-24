// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "ay-smt")]

use super::ay_solver::{create_smt_backend, DirectAyKernelProof};
use super::ay_tactics::{
    assert_goal_hypotheses_with_drop_count, prepare_kernel_ay_proof, select_verified_ay_proof,
};
use super::ay_types::SmtVerifyPolicy;
use super::*;
use crate::tactic::tc_app::nat_le_tc;
use crate::tactic::{LocalDecl, ProofState};
use clean_auto::bridge::ay_contract::test_utils::{
    empty_residual_trust_summary, residual_trust_summary_from_source,
};
use clean_auto::bridge::ay_contract::{AyLogic, ResidualTrustSource};
use clean_kernel::mode::CleanMode;
use clean_kernel::sorry::local_ay_reconstruction_success_count;
use clean_kernel::{env::Declaration, Environment, Expr, FVarId, Level, Name};
use serial_test::serial;

fn make_trusted_ay_term(target: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![Level::zero()]),
        target,
    )
}

fn setup_nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_le().unwrap();
    env
}

fn setup_prop_env(with_trusted_ay: bool) -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_classical().unwrap();
    if with_trusted_ay {
        env.init_trusted_ay().unwrap();
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P axiom should register");
    env
}

fn supported_nat_hypothesis() -> Expr {
    nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(0))
}

#[test]
fn test_assert_goal_hypotheses_with_drop_count_skips_sort_hypotheses() {
    let target = supported_nat_hypothesis();
    let state = ProofState::with_context(
        setup_nat_env(),
        target,
        vec![LocalDecl {
            fvar: FVarId::new(1),
            name: "A".to_string(),
            ty: Expr::type_(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut backend = create_smt_backend(&AyConfig::default(), AyLogic::QfLia);
    backend
        .register_fvars_from_context(&goal.local_ctx, state.metas())
        .expect("sort-valued locals should not fail FVar registration");

    let dropped = assert_goal_hypotheses_with_drop_count(&state, &goal, &mut backend);

    assert_eq!(dropped, 0, "sort-valued hypotheses should be ignored");
}

#[test]
fn test_assert_goal_hypotheses_with_drop_count_counts_unsupported_non_sort_hypotheses() {
    let target = supported_nat_hypothesis();
    let state = ProofState::with_context(
        setup_nat_env(),
        target,
        vec![LocalDecl {
            fvar: FVarId::new(2),
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("Nat"), vec![]),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut backend = create_smt_backend(&AyConfig::default(), AyLogic::QfLia);
    backend
        .register_fvars_from_context(&goal.local_ctx, state.metas())
        .expect("Nat locals should register before hypothesis translation");

    let dropped = assert_goal_hypotheses_with_drop_count(&state, &goal, &mut backend);

    assert_eq!(
        dropped, 1,
        "unsupported non-sort hypotheses should count as dropped"
    );
}

#[test]
fn test_assert_goal_hypotheses_with_drop_count_accepts_supported_hypotheses() {
    let supported = supported_nat_hypothesis();
    let state = ProofState::with_context(
        setup_nat_env(),
        supported.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(3),
            name: "h".to_string(),
            ty: supported,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut backend = create_smt_backend(&AyConfig::default(), AyLogic::QfLia);
    backend
        .register_fvars_from_context(&goal.local_ctx, state.metas())
        .expect("supported SMT hypotheses should register before solving");

    let dropped = assert_goal_hypotheses_with_drop_count(&state, &goal, &mut backend);

    assert_eq!(
        dropped, 0,
        "supported hypotheses should be asserted without drops"
    );
}

#[test]
fn test_prepare_kernel_ay_proof_returns_smt_failed_in_cubical_mode() {
    let mut env = Environment::with_mode(CleanMode::Cubical);
    env.init_true_false().expect("True/False should initialize");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("P axiom should register");
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = prepare_kernel_ay_proof(&mut state, "test_ay_cubical_bootstrap")
        .expect_err("cubical mode should reject classical bootstrap before proof reconstruction");

    assert!(
        matches!(
            &err,
            crate::tactic::TacticError::SmtFailed { tactic, detail }
                if tactic == "test_ay_cubical_bootstrap"
                    && detail.contains("classical bootstrap failed")
                    && detail.contains("Cubical")
        ),
        "ay preflight should preserve the tactic name and cubical bootstrap reason: {err:?}"
    );
}

#[test]
fn test_select_verified_ay_proof_returns_fully_verified_direct_proof_without_trust() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = Expr::fvar(FVarId::new(4));
    let state = ProofState::with_context(
        setup_prop_env(false),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(4),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_ay_direct",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            0,
            empty_residual_trust_summary(),
        )),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
    )
    .expect("fully verified direct proof should not fail");

    assert_eq!(
        returned, direct_proof,
        "fully verified direct proof should be returned unchanged"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "fully verified direct proofs should not add trustedAy debt"
    );
}

#[test]
#[serial]
fn test_select_verified_ay_proof_rejects_invalid_clean_direct_proof_and_recovers() {
    reset_ay_reconstruction_success_counter();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let invalid_direct_proof = Expr::type_();
    let state = ProofState::with_context(
        setup_prop_env(false),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(14),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_invalid_direct_recovers",
        Some(DirectAyKernelProof::new(
            invalid_direct_proof.clone(),
            0,
            empty_residual_trust_summary(),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    )
    .expect("invalid clean direct proof should fall back to zero-trust recovery");

    assert_ne!(
        returned, invalid_direct_proof,
        "selector must not accept the invalid direct proof unchanged"
    );
    assert_eq!(
        returned,
        Expr::fvar(FVarId::new(14)),
        "selector should recover via the existing zero-trust bridge lane"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "recovering from an invalid direct proof must not add trust debt"
    );
    assert_eq!(
        state
            .trust_ledger()
            .smt_recovery
            .invalid_direct_ay_candidates,
        1,
        "rejecting an invalid direct ay proof must record one recovery event"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "recovery after rejecting an invalid direct proof should record reconstruction success"
    );
}

#[test]
fn test_select_verified_ay_proof_preserves_validation_failure_when_recovery_exhausts() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(setup_prop_env(false), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let err = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_invalid_direct_fail_closed",
        Some(DirectAyKernelProof::new(
            Expr::type_(),
            0,
            empty_residual_trust_summary(),
        )),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
    )
    .expect_err("invalid direct proof without recovery should fail closed");

    assert!(
        matches!(
            &err,
            crate::tactic::TacticError::SmtFailed { tactic, detail }
                if tactic == "test_invalid_direct_fail_closed"
                    && detail.contains("failed kernel validation before selection")
                    && detail.contains("recovery also failed")
        ),
        "error should preserve the selector-side validation failure after recovery exhaustion: {err:?}"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "failing closed after invalid direct proof should not add trust debt"
    );
    assert_eq!(
        state
            .trust_ledger()
            .smt_recovery
            .invalid_direct_ay_candidates,
        1,
        "failing closed still records the rejected invalid direct ay candidate"
    );
}

#[test]
#[serial]
fn test_select_verified_ay_proof_prefers_cleaner_bridge_candidate() {
    reset_ay_reconstruction_success_counter();

    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let state = ProofState::with_context(
        setup_prop_env(true),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(5),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_ay_bridge",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
    )
    .expect("bridge-backed direct proof selection should not fail");

    assert_ne!(
        returned, direct_proof,
        "a lower-trust bridge candidate should replace the partially trusted direct proof"
    );
    assert_eq!(
        trusted_subterms::count_embedded_trusted_ay_terms(&returned),
        0,
        "bridge-selected proof should avoid embedded trustedAy debt"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "bridge preference should not mirror the direct proof's trustedAy debt"
    );
    assert!(
        !state.trust_ledger().smt_recovery.has_events(),
        "selection-only bridge probe must not mutate smt_recovery counters"
    );
}

#[test]
fn test_select_verified_ay_proof_keeps_partially_trusted_direct_proof_without_bridge_candidate() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let mut state = ProofState::new(setup_prop_env(true), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_ay_no_bridge",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
    )
    .expect("partially trusted direct proof should still be selectable");

    assert_eq!(
        returned, direct_proof,
        "when bridge reconstruction is unavailable the tactic should keep the direct proof"
    );
    assert_eq!(
        trusted_subterms::count_embedded_trusted_ay_terms(&returned),
        1,
        "kept direct proof should still expose its embedded trustedAy debt"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        1,
        "kept direct proof should mirror its trustedAy debt into the proof-state ledger"
    );
}

// --- VerifyStrict QF_UF zero-trust enforcement tests (#2677) ---

#[test]
fn test_strict_qf_uf_rejects_partially_trusted_direct_proof_without_bridge() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let mut state = ProofState::new(setup_prop_env(true), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let result = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_reject",
        Some(DirectAyKernelProof::new(
            direct_proof,
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    );

    assert!(
        result.is_err(),
        "VerifyStrict QF_UF must reject a partially trusted direct proof when no zero-trust bridge exists"
    );
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("VerifyStrict") && err_msg.contains("zero-trust"),
        "error message should mention VerifyStrict and zero-trust: {err_msg}"
    );
}

#[test]
#[serial]
fn test_strict_qf_uf_replaces_partially_trusted_direct_proof_with_zero_trust_recovery() {
    reset_ay_reconstruction_success_counter();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let state = ProofState::with_context(
        setup_prop_env(false),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(12),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_bridge_from_direct",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    )
    .expect("VerifyStrict QF_UF should replace a trusted direct proof with zero-trust recovery");

    assert_ne!(
        returned, direct_proof,
        "strict zero-trust recovery must not keep the partially trusted direct proof"
    );
    assert_eq!(
        returned,
        Expr::fvar(FVarId::new(12)),
        "strict zero-trust recovery should reuse the clean recovered proof from the hypothesis"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict zero-trust recovery should not add trustedAy debt"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "strict zero-trust recovery should record ay reconstruction success"
    );
}

#[test]
fn test_strict_qf_uf_accepts_fully_verified_direct_proof() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = Expr::fvar(FVarId::new(10));
    let state = ProofState::with_context(
        setup_prop_env(false),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(10),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_accept",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            0,
            empty_residual_trust_summary(),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    )
    .expect("VerifyStrict QF_UF must accept a fully verified direct proof");

    assert_eq!(
        returned, direct_proof,
        "fully verified direct proof should pass through VerifyStrict unchanged"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "fully verified proof should not add trust debt"
    );
}

#[test]
#[serial]
fn test_strict_qf_uf_without_direct_proof_uses_zero_trust_recovery() {
    reset_ay_reconstruction_success_counter();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let state = ProofState::with_context(
        setup_prop_env(false),
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(11),
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal").clone();
    let mut state = state;

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_bridge_fallback",
        None,
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfUf,
    )
    .expect("VerifyStrict QF_UF should accept zero-trust recovery");

    assert_eq!(
        returned,
        Expr::fvar(FVarId::new(11)),
        "zero-trust recovery should recover the existing hypothesis proof"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "zero-trust recovery should not add trust debt"
    );
    assert!(
        local_ay_reconstruction_success_count() >= 1,
        "zero-trust recovery should record ay reconstruction success"
    );
}

#[test]
fn test_non_strict_policy_preserves_partially_trusted_direct_proof() {
    // ExtractOnly + QF_UF: same scenario as strict test, but should accept.
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let mut state = ProofState::new(setup_prop_env(true), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let returned = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_non_strict",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::ExtractOnly,
        AyLogic::QfUf,
    )
    .expect("non-strict policy should accept partially trusted direct proof");

    assert_eq!(
        returned, direct_proof,
        "non-strict policy should keep the partially trusted direct proof"
    );
}

#[test]
fn test_strict_qf_lia_rejects_partially_trusted_direct_proof_without_zero_trust_bridge() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let mut state = ProofState::new(setup_prop_env(true), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let result = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_lia",
        Some(DirectAyKernelProof::new(
            direct_proof.clone(),
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfLia,
    );

    let err = result.expect_err(
        "VerifyStrict QF_LIA must reject a partially trusted direct proof when no zero-trust bridge exists",
    );
    let err_msg = format!("{err}");
    assert!(
        err_msg.contains("VerifyStrict QF_LIA") && err_msg.contains("zero-trust"),
        "strict QF_LIA failure should mention the logic and zero-trust policy: {err_msg}"
    );
}

#[test]
fn test_strict_qf_lra_rejects_partially_trusted_direct_proof_without_zero_trust_bridge() {
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let direct_proof = make_trusted_ay_term(target.clone());
    let mut state = ProofState::new(setup_prop_env(true), target.clone());
    let goal = state.current_goal().expect("goal").clone();

    let result = select_verified_ay_proof(
        &mut state,
        &goal,
        &target,
        "test_strict_lra",
        Some(DirectAyKernelProof::new(
            direct_proof,
            1,
            residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
        )),
        SmtVerifyPolicy::VerifyStrict,
        AyLogic::QfLra,
    );

    let err = result.expect_err(
        "VerifyStrict QF_LRA must reject a partially trusted direct proof when no zero-trust bridge exists",
    );
    let err_msg = format!("{err}");
    assert!(
        err_msg.contains("VerifyStrict QF_LRA") && err_msg.contains("zero-trust"),
        "strict QF_LRA failure should mention the logic and zero-trust policy: {err_msg}"
    );
}
