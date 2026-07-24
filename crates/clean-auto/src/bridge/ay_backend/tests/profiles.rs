// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-profile, timeout, and policy tests for the Ay backend.

use super::support::build_unsat_proof_backend;
use super::*;
use ay::ProofQuality;

#[test]
fn test_profile_trusted_unsat_unverified() {
    let config = AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::trusted());
    let mut backend = build_unsat_proof_backend(config);

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat {
            proof, verified, ..
        } => {
            assert!(
                proof.is_none(),
                "Trusted profile should not auto-enable proofs"
            );
            assert!(!verified, "Trusted profile should not verify proofs");
        }
        other => panic!("Expected UNSAT, got {:?}", other),
    }
}

#[test]
fn test_profile_ay_native_verified() {
    // Tier 1 verification works via native ay-proof checker without carcara-verify feature
    let config =
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::carcara_verified());
    let mut backend = build_unsat_proof_backend(config);

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat {
            proof,
            verified,
            quality,
        } => {
            assert!(proof.is_some(), "Expected proof to be present");
            assert!(verified, "Expected verified via native ay-proof checker");
            assert!(quality.is_some(), "Expected quality metrics from ay-proof");
            let q = quality.unwrap();
            assert!(q.total_steps > 0, "Expected non-empty proof");
            // #2258: verify the proof is complete (no trust/hole steps)
            assert!(
                q.is_complete(),
                "Expected complete proof with no trust/hole steps, got: trust={}, hole={}",
                q.trust_count,
                q.hole_count
            );
        }
        other => panic!("Expected UNSAT, got {:?}", other),
    }
}

/// Regression test for #2258: ProofQuality with trust_count > 0 must NOT be treated
/// as a verified proof. The is_complete() check prevents trust-containing proofs
/// from being accepted as fully verified by the native checker path.
#[test]
fn test_trust_containing_quality_is_not_complete() {
    let mut q = ProofQuality::default();
    q.trust_count = 1;
    q.total_steps = 5;
    q.resolution_count = 2;
    q.assume_count = 2;
    assert!(
        !q.is_complete(),
        "ProofQuality with trust_count > 0 must not be considered complete"
    );
    assert_eq!(q.fallback_count(), 1);

    let mut q_hole = ProofQuality::default();
    q_hole.hole_count = 1;
    q_hole.total_steps = 3;
    assert!(
        !q_hole.is_complete(),
        "ProofQuality with hole_count > 0 must not be considered complete"
    );
}

#[cfg(feature = "carcara-verify")]
#[test]
fn test_profile_carcara_verified_marks_verified() {
    let config =
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::carcara_verified());
    let mut backend = build_unsat_proof_backend(config);

    match backend.check_sat().unwrap() {
        AyProofResult::Unsat {
            proof, verified, ..
        } => {
            assert!(proof.is_some(), "Expected proof to be present");
            assert!(verified, "Expected proof to be verified with Carcara");
        }
        other => panic!("Expected UNSAT, got {:?}", other),
    }
}

#[test]
fn test_profile_kernel_accepted_rejects_bv() {
    let config = AyBackendConfig::new(AyLogic::QfBv).proof_profile(ProofProfile::kernel_accepted());
    let mut backend = build_unsat_proof_backend(config);

    match backend.check_sat() {
        Err(AyError::TheoryRejected(msg)) => {
            assert!(
                msg.contains("theory QF_BV not accepted"),
                "Expected theory rejection, got: {}",
                msg
            );
        }
        other => panic!("Expected theory rejection, got {:?}", other),
    }
}

#[test]
fn test_profile_kernel_critical_unimplemented_tier() {
    let config =
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::kernel_critical());
    let mut backend = build_unsat_proof_backend(config);

    match backend.check_sat() {
        Err(AyError::VerificationFailed(msg)) => {
            assert!(
                msg.contains("verification tier 2 not yet implemented"),
                "Expected tier error, got: {}",
                msg
            );
        }
        other => panic!("Expected tier error, got {:?}", other),
    }
}

#[test]
fn test_verify_error_conversion_preserves_ay_error_contract() {
    match AyError::from(VerifyError::VerificationFailed("invalid".to_string())) {
        AyError::VerificationFailed(message) => assert_eq!(message, "invalid"),
        other => panic!("expected verification failure, got {other:?}"),
    }

    match AyError::from(VerifyError::UnsupportedFormat("lfsc".to_string())) {
        AyError::VerificationFailed(message) => {
            assert_eq!(message, "unsupported proof format: lfsc");
        }
        other => panic!("expected verification failure, got {other:?}"),
    }

    match AyError::from(VerifyError::TheoryRejected("QF_BV".to_string())) {
        AyError::TheoryRejected(message) => assert_eq!(message, "QF_BV"),
        other => panic!("expected theory rejection, got {other:?}"),
    }

    match AyError::from(VerifyError::CarcaraNotEnabled) {
        AyError::VerificationFailed(message) => {
            assert_eq!(
                message,
                "proof verification required but no checker available"
            );
        }
        other => panic!("expected verification failure, got {other:?}"),
    }
}

#[cfg(feature = "carcara-verify")]
#[test]
fn test_verify_error_conversion_preserves_carcara_error_message() {
    match AyError::from(VerifyError::CarcaraError("parse failed".to_string())) {
        AyError::VerificationFailed(message) => {
            assert_eq!(message, "Carcara verification error: parse failed");
        }
        other => panic!("expected verification failure, got {other:?}"),
    }
}

#[test]
fn test_proof_backend_parse_error_uses_script_error() {
    let mut backend = AyProofBackend::new_default(AyLogic::QfLia);
    backend.add_raw_declaration("(declare-const x Int");

    match backend.check_sat() {
        Err(AyError::ScriptError(msg)) => {
            assert!(
                msg.contains("parse error"),
                "Expected parse error classification, got: {}",
                msg
            );
        }
        other => panic!("Expected script error, got {:?}", other),
    }
}

#[test]
fn test_timeout_config() {
    // Test that timeout configuration is applied to the solver
    let config = AyBackendConfig::new(AyLogic::QfLia).timeout(1000);
    let mut backend = AyBackend::with_config(config);

    // Simple SAT problem should complete within timeout
    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);
    assert_eq!(backend.check_sat(), AySolveResult::Sat);
}

#[test]
fn test_zero_timeout_returns_unknown() {
    // Zero timeout should cause Unknown result
    let config = AyBackendConfig::new(AyLogic::QfLia).timeout(0);
    let mut backend = AyBackend::with_config(config);

    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let x_gt_zero = backend.gt(x, zero);
    backend.assert_term(x_gt_zero);
    assert_eq!(backend.check_sat(), AySolveResult::Unknown);
}

#[test]
fn test_no_timeout_completes() {
    // Default config (no timeout) should solve correctly
    // Verifies that None timeout case works
    let mut backend = AyBackend::new(AyLogic::QfLia);

    let x = backend.fresh_int("x");
    let zero = backend.int_const(0);
    let ten = backend.int_const(10);

    // More complex constraints that still solve quickly
    let x_gt_zero = backend.gt(x, zero);
    let x_lt_ten = backend.lt(x, ten);
    let constraint = backend.and(x_gt_zero, x_lt_ten);
    backend.assert_term(constraint);

    // Should complete without timeout (SAT: x can be 1-9)
    assert_eq!(backend.check_sat(), AySolveResult::Sat);
}

#[test]
fn test_proof_profile_configuration() {
    // Test tier 0 (trusted) profile
    let profile = ProofProfile::trusted();
    assert_eq!(profile.verification_tier(), 0);
    assert_eq!(profile.format(), &ProofFormat::None);
    assert!(profile.accepts_all_theories());
    assert!(profile.accepts_theory("QF_LIA"));

    // Test tier 1 (Carcara verified) profile
    let profile = ProofProfile::carcara_verified();
    assert_eq!(profile.verification_tier(), 1);
    assert!(matches!(profile.format(), ProofFormat::Alethe { .. }));
    assert!(profile.accepts_all_theories());
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("QF_LRA"));

    // Test theory-restricted profile
    let profile = ProofProfile::carcara_verified_with_theories(&["QF_LIA", "QF_UF"]);
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("QF_UF"));
    assert!(!profile.accepts_theory("QF_BV")); // Not in whitelist
}

#[test]
fn test_config_with_proof_profile() {
    // Test that setting proof profile automatically enables proof production
    let config =
        AyBackendConfig::new(AyLogic::QfLia).proof_profile(ProofProfile::carcara_verified());

    assert!(
        config.produces_proofs(),
        "Proof production should be auto-enabled for tier 1"
    );
    let profile = config
        .profile()
        .expect("proof profile should be set for tier 1");
    assert_eq!(profile, &ProofProfile::carcara_verified());
}

/// Test proof format constants and constructors (Part of #615)
#[test]
fn test_proof_format_constants() {
    // Test Alethe format
    let alethe = ProofFormat::alethe();
    assert!(
        matches!(&alethe, ProofFormat::Alethe { version } if version == proof_formats::ALETHE_VERSION)
    );
    assert_eq!(alethe.format_id(), "alethe");
    assert_eq!(alethe.file_extension(), proof_formats::ALETHE_EXT);

    // Test LRAT text format
    let lrat_text = ProofFormat::lrat_text();
    assert!(matches!(lrat_text, ProofFormat::Lrat { binary: false }));
    assert_eq!(lrat_text.format_id(), proof_formats::LRAT_TEXT);
    assert_eq!(lrat_text.file_extension(), proof_formats::LRAT_EXT);

    // Test LRAT binary format
    let lrat_binary = ProofFormat::lrat_binary();
    assert!(matches!(lrat_binary, ProofFormat::Lrat { binary: true }));
    assert_eq!(lrat_binary.format_id(), proof_formats::LRAT_BINARY);
    assert_eq!(lrat_binary.file_extension(), proof_formats::LRAT_EXT);

    // Test None format
    let none = ProofFormat::None;
    assert_eq!(none.format_id(), "none");
    assert_eq!(none.file_extension(), "");

    // Verify constants
    assert_eq!(proof_formats::ALETHE_VERSION, "2.0");
    assert_eq!(proof_formats::CARCARA_MIN_VERSION, "1.1.0");
}

/// Test kernel acceptance policy profiles (Part of #617)
#[test]
fn test_kernel_acceptance_policy() {
    // Production profile: kernel-accepted theories only
    let prod_profile = ProofProfile::kernel_accepted();
    assert_eq!(prod_profile.verification_tier(), 1);
    assert!(matches!(prod_profile.format(), ProofFormat::Alethe { .. }));
    assert!(!prod_profile.accepts_all_theories());
    assert!(prod_profile.requires_carcara());
    assert!(!prod_profile.requires_lrat());

    // Accepted theories: LIA, LRA, UF, UFLIA, UFLRA (full Alethe support)
    assert!(prod_profile.accepts_theory("QF_LIA"));
    assert!(prod_profile.accepts_theory("QF_LRA"));
    assert!(prod_profile.accepts_theory("QF_UF"));
    assert!(prod_profile.accepts_theory("QF_UFLIA"));
    assert!(prod_profile.accepts_theory("QF_UFLRA"));

    // Rejected theories: BV (uses trust rule), AUFLIA (no standard rule)
    assert!(!prod_profile.accepts_theory("QF_BV"));
    assert!(!prod_profile.accepts_theory("QF_AUFLIA"));

    // Critical profile: SAT-only with LRAT verification
    let critical_profile = ProofProfile::kernel_critical();
    assert_eq!(critical_profile.verification_tier(), 2);
    assert!(matches!(
        critical_profile.format(),
        ProofFormat::Lrat { binary: true }
    ));
    assert!(!critical_profile.requires_carcara());
    assert!(critical_profile.requires_lrat());
    assert!(critical_profile.accepts_all_theories());

    // Critical profile accepts all theories (empty whitelist means no restriction)
    // This is intentional - SAT-only proofs don't use theory extensions
    assert!(critical_profile.accepts_theory("anything"));
}

/// Test Carcara theory verification static methods (Part of #619)
#[test]
fn test_carcara_theory_verification() {
    // Fully verified theories (no `trust` rules)
    assert!(ProofProfile::is_fully_verified_theory("QF_LIA"));
    assert!(ProofProfile::is_fully_verified_theory("QF_LRA"));
    assert!(ProofProfile::is_fully_verified_theory("QF_UF"));
    assert!(ProofProfile::is_fully_verified_theory("QF_UFLIA"));
    assert!(ProofProfile::is_fully_verified_theory("QF_UFLRA"));
    assert!(!ProofProfile::is_fully_verified_theory("QF_BV"));
    assert!(!ProofProfile::is_fully_verified_theory("QF_ABV"));
    assert!(!ProofProfile::is_fully_verified_theory("unknown"));

    // Partially supported theories (may use `trust` rules)
    assert!(ProofProfile::is_partially_supported_theory("QF_BV"));
    assert!(ProofProfile::is_partially_supported_theory("QF_ABV"));
    assert!(ProofProfile::is_partially_supported_theory("QF_AUFLIA"));
    assert!(!ProofProfile::is_partially_supported_theory("QF_LIA"));
    assert!(!ProofProfile::is_partially_supported_theory("QF_UF"));
    assert!(!ProofProfile::is_partially_supported_theory("unknown"));

    // has_carcara_support combines both
    assert!(ProofProfile::has_carcara_support("QF_LIA")); // fully verified
    assert!(ProofProfile::has_carcara_support("QF_BV")); // partially supported
    assert!(!ProofProfile::has_carcara_support("unknown")); // unsupported
    assert!(!ProofProfile::has_carcara_support("QF_AUFBV")); // not in either list

    // Verify the two theory lists are disjoint — no theory can be both
    // fully verified AND partially supported. (The membership and
    // has_carcara_support checks were tautological: iterating an array
    // and asserting .contains() on the same array always passes.)
    for theory in proof_formats::CARCARA_VERIFIED_THEORIES {
        assert!(
            !ProofProfile::is_partially_supported_theory(theory),
            "CARCARA_VERIFIED_THEORIES entry {theory} must NOT appear in PARTIAL list"
        );
    }
    for theory in proof_formats::CARCARA_PARTIAL_THEORIES {
        assert!(
            !ProofProfile::is_fully_verified_theory(theory),
            "CARCARA_PARTIAL_THEORIES entry {theory} must NOT appear in VERIFIED list"
        );
    }

    // Verify both lists are non-empty (guard against accidental clearing)
    assert!(
        !proof_formats::CARCARA_VERIFIED_THEORIES.is_empty(),
        "CARCARA_VERIFIED_THEORIES should not be empty"
    );
    assert!(
        !proof_formats::CARCARA_PARTIAL_THEORIES.is_empty(),
        "CARCARA_PARTIAL_THEORIES should not be empty"
    );
}
