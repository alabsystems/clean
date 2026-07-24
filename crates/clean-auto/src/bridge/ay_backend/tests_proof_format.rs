// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof format types and proof profiles.

use super::proof_format::*;

#[test]
fn test_proof_format_default_is_none() {
    let fmt = ProofFormat::default();
    assert_eq!(fmt, ProofFormat::None);
    assert_eq!(fmt.format_id(), "none");
    assert_eq!(fmt.file_extension(), "");
}

#[test]
fn test_proof_format_alethe_version_and_id() {
    let fmt = ProofFormat::alethe();
    assert_eq!(fmt.format_id(), "alethe");
    assert_eq!(fmt.file_extension(), ".alethe");
    match fmt {
        ProofFormat::Alethe { version } => {
            assert_eq!(version, proof_formats::ALETHE_VERSION);
        }
        _ => panic!("expected Alethe variant"),
    }
}

#[test]
fn test_proof_format_lrat_variants() {
    let text = ProofFormat::lrat_text();
    assert_eq!(text.format_id(), proof_formats::LRAT_TEXT);
    assert_eq!(text.file_extension(), proof_formats::LRAT_EXT);

    let binary = ProofFormat::lrat_binary();
    assert_eq!(binary.format_id(), proof_formats::LRAT_BINARY);
    assert_eq!(binary.file_extension(), proof_formats::LRAT_EXT);
}

#[test]
fn test_proof_profile_trusted_is_tier_zero() {
    let profile = ProofProfile::trusted();
    assert_eq!(profile.verification_tier(), 0);
    assert!(!profile.requires_carcara());
    assert!(!profile.requires_lrat());
    assert!(profile.accepts_all_theories());
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("anything"));
}

#[test]
fn test_proof_profile_carcara_verified_tier_one() {
    let profile = ProofProfile::carcara_verified();
    assert_eq!(profile.verification_tier(), 1);
    assert!(profile.requires_carcara());
    assert!(!profile.requires_lrat());
    assert!(profile.accepts_all_theories());
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("QF_BV"));
}

#[test]
fn test_proof_profile_with_theories_whitelist() {
    let profile = ProofProfile::carcara_verified_with_theories(&["QF_LIA", "QF_UF"]);
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("QF_UF"));
    assert!(!profile.accepts_theory("QF_BV"));
    assert!(!profile.accepts_theory("QF_LRA"));
}

#[test]
fn test_proof_profile_kernel_accepted_excludes_partial_theories() {
    let profile = ProofProfile::kernel_accepted();
    assert_eq!(profile.verification_tier(), 1);
    assert!(!profile.accepts_all_theories());
    // Fully verified theories should be accepted
    assert!(profile.accepts_theory("QF_LIA"));
    assert!(profile.accepts_theory("QF_UF"));
    // Partial theories should NOT be accepted
    assert!(!profile.accepts_theory("QF_BV"));
    assert!(!profile.accepts_theory("QF_ABV"));
}

#[test]
fn test_proof_profile_kernel_critical_tier_two() {
    let profile = ProofProfile::kernel_critical();
    assert_eq!(profile.verification_tier(), 2);
    assert!(!profile.requires_carcara());
    assert!(profile.requires_lrat());
}

#[test]
fn test_is_fully_verified_theory_classification() {
    assert!(ProofProfile::is_fully_verified_theory("QF_LIA"));
    assert!(ProofProfile::is_fully_verified_theory("QF_LRA"));
    assert!(ProofProfile::is_fully_verified_theory("QF_UF"));
    assert!(!ProofProfile::is_fully_verified_theory("QF_BV"));
    assert!(!ProofProfile::is_fully_verified_theory("nonexistent"));
}

#[test]
fn test_is_partially_supported_theory_classification() {
    assert!(ProofProfile::is_partially_supported_theory("QF_BV"));
    assert!(ProofProfile::is_partially_supported_theory("QF_ABV"));
    assert!(!ProofProfile::is_partially_supported_theory("QF_LIA"));
    assert!(!ProofProfile::is_partially_supported_theory("nonexistent"));
}

#[test]
fn test_has_carcara_support_covers_both() {
    // Full support
    assert!(ProofProfile::has_carcara_support("QF_LIA"));
    // Partial support
    assert!(ProofProfile::has_carcara_support("QF_BV"));
    // No support
    assert!(!ProofProfile::has_carcara_support("nonexistent"));
}
