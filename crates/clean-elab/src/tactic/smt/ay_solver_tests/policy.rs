// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::{create_smt_backend, SmtSolver};
use super::super::ay_types::{
    requires_zero_trust_reconstruction, verify_strict_logic_behavior, verify_strict_proof_profile,
    StrictLogicBehavior,
};
use super::super::*;
use clean_auto::bridge::ay_contract::{AyLogic, ProofProfile, TrustBudget};

#[test]
fn test_direct_reconstruction_budget_is_zero_trust_for_supported_strict_logics() {
    for logic in [AyLogic::QfUf, AyLogic::QfLia, AyLogic::QfLra] {
        assert_eq!(
            SmtSolver::direct_reconstruction_budget(SmtVerifyPolicy::VerifyStrict, logic),
            TrustBudget::ZeroTrust,
            "VerifyStrict {logic} should select the zero-trust budget",
        );
    }
}

#[test]
fn test_verify_strict_logic_behavior_marks_supported_logics_as_zero_trust() {
    for logic in [AyLogic::QfUf, AyLogic::QfLia, AyLogic::QfLra] {
        assert_eq!(
            verify_strict_logic_behavior(logic),
            StrictLogicBehavior::SupportedZeroTrust,
            "VerifyStrict {logic} should stay in the supported zero-trust set",
        );
    }
}

#[test]
fn test_verify_strict_logic_behavior_marks_other_logics_for_reject_and_fallback() {
    for logic in [
        AyLogic::All,
        AyLogic::QfUflia,
        AyLogic::QfBv,
        AyLogic::QfAuflia,
        AyLogic::QfFp,
        AyLogic::Uf,
        AyLogic::Uflia,
    ] {
        assert_eq!(
            verify_strict_logic_behavior(logic),
            StrictLogicBehavior::UnsupportedRejectAndFallback,
            "VerifyStrict {logic} should reject the ay proof lane and fall back",
        );
    }
}

#[test]
fn test_requires_zero_trust_reconstruction_is_true_for_supported_strict_logics() {
    for logic in [AyLogic::QfUf, AyLogic::QfLia, AyLogic::QfLra] {
        assert!(
            requires_zero_trust_reconstruction(SmtVerifyPolicy::VerifyStrict, logic),
            "VerifyStrict {logic} should require zero-trust reconstruction",
        );
    }
}

#[test]
fn test_requires_zero_trust_reconstruction_keeps_other_pairs_false() {
    assert!(
        !requires_zero_trust_reconstruction(SmtVerifyPolicy::ExtractOnly, AyLogic::QfUf),
        "non-strict QF_UF should keep permissive reconstruction behavior"
    );
    assert!(
        !requires_zero_trust_reconstruction(SmtVerifyPolicy::VerifyStrict, AyLogic::QfBv),
        "strict QF_BV must stay outside the zero-trust rollout"
    );
}

#[test]
fn test_direct_reconstruction_budget_keeps_non_strict_qf_uf_unlimited() {
    assert_eq!(
        SmtSolver::direct_reconstruction_budget(SmtVerifyPolicy::ExtractOnly, AyLogic::QfUf),
        TrustBudget::Unlimited
    );
}

#[test]
fn test_create_smt_backend_trust_solver_uses_fast_backend() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::TrustSolver);

    let solver = create_smt_backend(&config, AyLogic::QfLia);
    assert_eq!(solver.effective_policy(), SmtVerifyPolicy::TrustSolver);
    assert!(
        matches!(solver, SmtSolver::Fast(_)),
        "TrustSolver should use the fast backend"
    );
}

#[test]
fn test_create_smt_backend_extract_only_uses_verifiable_without_profile() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);

    let solver = create_smt_backend(&config, AyLogic::QfLia);
    assert_eq!(solver.effective_policy(), SmtVerifyPolicy::ExtractOnly);

    let SmtSolver::Verifiable {
        backend, policy, ..
    } = solver
    else {
        panic!("ExtractOnly should use the verifiable backend");
    };
    assert_eq!(policy, SmtVerifyPolicy::ExtractOnly);
    assert!(
        backend.config().produces_proofs(),
        "ExtractOnly should still request proof production"
    );
    assert!(
        backend.config().profile().is_none(),
        "ExtractOnly should not wire a proof profile"
    );
}

#[test]
fn test_create_smt_backend_verify_carcara_wires_carcara_profile() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyCarcara);

    let solver = create_smt_backend(&config, AyLogic::QfLia);
    assert_eq!(solver.effective_policy(), SmtVerifyPolicy::VerifyCarcara);

    let SmtSolver::Verifiable {
        backend, policy, ..
    } = solver
    else {
        panic!("VerifyCarcara should use the verifiable backend");
    };
    assert_eq!(policy, SmtVerifyPolicy::VerifyCarcara);
    assert!(
        backend.config().produces_proofs(),
        "VerifyCarcara should request proof production"
    );

    let profile = backend
        .config()
        .profile()
        .expect("VerifyCarcara should wire a proof profile");
    let expected = ProofProfile::carcara_verified();

    assert_eq!(profile, &expected);
    assert!(
        profile.accepts_all_theories(),
        "carcara-verified profile should accept every theory"
    );
    assert!(
        profile.accepts_theory("QF_BV"),
        "carcara-verified profile should not restrict theories"
    );
}

#[test]
fn test_create_smt_backend_verify_strict_wires_supported_strict_profile() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict);

    let solver = create_smt_backend(&config, AyLogic::QfLia);
    assert_eq!(solver.effective_policy(), SmtVerifyPolicy::VerifyStrict);

    let SmtSolver::Verifiable {
        backend, policy, ..
    } = solver
    else {
        panic!("VerifyStrict should use the verifiable backend");
    };
    assert_eq!(policy, SmtVerifyPolicy::VerifyStrict);
    assert!(
        backend.config().produces_proofs(),
        "VerifyStrict should request proof production"
    );

    let profile = backend
        .config()
        .profile()
        .expect("VerifyStrict should wire a proof profile");
    let expected = verify_strict_proof_profile();

    assert_eq!(profile, &expected);
    assert!(
        profile.accepts_theory("QF_LIA"),
        "strict profile should accept QF_LIA"
    );
    assert!(
        profile.accepts_theory("QF_UF"),
        "strict profile should accept QF_UF"
    );
    assert!(
        !profile.accepts_theory("QF_BV"),
        "strict profile should reject QF_BV"
    );
    assert!(
        !profile.accepts_theory("QF_UFLIA"),
        "strict profile should reject combined logics outside the zero-trust rollout"
    );
}

#[test]
fn test_verify_strict_profile_matches_supported_strict_logic_behavior() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict);
    let solver = create_smt_backend(&config, AyLogic::QfUf);

    let SmtSolver::Verifiable { backend, .. } = solver else {
        panic!("VerifyStrict should use the verifiable backend");
    };
    let profile = backend
        .config()
        .profile()
        .expect("VerifyStrict should wire a proof profile");

    for logic in [
        AyLogic::QfUf,
        AyLogic::QfLia,
        AyLogic::QfLra,
        AyLogic::QfUflia,
        AyLogic::QfBv,
        AyLogic::QfAuflia,
        AyLogic::QfFp,
        AyLogic::Uf,
        AyLogic::Uflia,
    ] {
        let accepts = profile.accepts_theory(&logic.to_string());
        let expected_acceptance = matches!(
            verify_strict_logic_behavior(logic),
            StrictLogicBehavior::SupportedZeroTrust
        );
        assert_eq!(
            accepts, expected_acceptance,
            "strict backend profile should stay aligned with VerifyStrict logic behavior for {logic}",
        );
    }
}
