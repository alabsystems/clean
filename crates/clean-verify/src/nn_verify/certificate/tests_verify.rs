// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the generic certificate verification framework (`verify.rs`).

use super::chain::{
    verify_chain_coverage, CertificateChain, CertificateEntry, ChainTrustLevel, VerificationMethod,
};
use super::verify::{
    certificate_strength, merge_reports, report_summary, verify_bound_containment,
    verify_chain_certificate, verify_layer_certificate, verify_specification,
    verify_trust_consistency, CertificateStatus, ClassificationSpec, VerificationReport,
    C01_CHAIN_CONTINUITY, C02_CHAIN_COVERAGE, C03_BOUND_SOUNDNESS,
};
use crate::spec::ProofStatus;

// -- helpers --

fn entry(
    idx: usize,
    method: VerificationMethod,
    inp: Vec<(f64, f64)>,
    out: Vec<(f64, f64)>,
    trust: ChainTrustLevel,
) -> CertificateEntry {
    CertificateEntry {
        layer_index: idx,
        method,
        input_bounds: inp,
        output_bounds: out,
        trust_level: trust,
    }
}

fn chain(entries: Vec<CertificateEntry>, prop: &str, net: &str) -> CertificateChain {
    CertificateChain {
        entries,
        property: prop.to_owned(),
        network_id: net.to_owned(),
    }
}

/// Linear layer: [0,1]^2 -> [0.5,2.5]^2, Formal trust
fn linear() -> CertificateEntry {
    entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(0.5, 2.5), (0.5, 2.5)],
        ChainTrustLevel::Formal,
    )
}

/// ReLU layer: [0.5,2.5]^2 -> [0.5,2.5]^2, Numerical trust
fn relu() -> CertificateEntry {
    entry(
        1,
        VerificationMethod::CROWN,
        vec![(0.5, 2.5), (0.5, 2.5)],
        vec![(0.5, 2.5), (0.5, 2.5)],
        ChainTrustLevel::Numerical,
    )
}

/// Third layer: [0.5,2.5]^2 -> [1.0,3.0] x [0.0,1.0], Formal trust
fn third() -> CertificateEntry {
    entry(
        2,
        VerificationMethod::AlphaCROWN,
        vec![(0.5, 2.5), (0.5, 2.5)],
        vec![(1.0, 3.0), (0.0, 1.0)],
        ChainTrustLevel::Formal,
    )
}

fn simple_report(
    statuses: Vec<CertificateStatus>,
    overall: CertificateStatus,
    trust: ChainTrustLevel,
    coverage: f64,
) -> VerificationReport {
    VerificationReport {
        layer_statuses: statuses,
        overall_status: overall,
        trust_level: trust,
        coverage,
        elapsed: None,
        notes: vec![],
    }
}

// -- proof status constants --

#[test]
fn test_proof_status_constants() {
    assert!(matches!(C01_CHAIN_CONTINUITY, ProofStatus::DerivedPending));
    assert!(matches!(C02_CHAIN_COVERAGE, ProofStatus::DerivedPending));
    assert!(matches!(C03_BOUND_SOUNDNESS, ProofStatus::DerivedPending));
}

// -- single layer verification --

#[test]
fn test_verify_layer_linear_valid() {
    assert_eq!(
        verify_layer_certificate(&linear()),
        CertificateStatus::Valid
    );
}

#[test]
fn test_verify_layer_relu_valid() {
    assert_eq!(verify_layer_certificate(&relu()), CertificateStatus::Valid);
}

#[test]
fn test_verify_layer_empty_input_bounds() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    assert!(matches!(
        verify_layer_certificate(&e),
        CertificateStatus::Invalid { .. }
    ));
}

#[test]
fn test_verify_layer_empty_output_bounds() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![],
        ChainTrustLevel::Formal,
    );
    assert!(matches!(
        verify_layer_certificate(&e),
        CertificateStatus::Invalid { .. }
    ));
}

#[test]
fn test_verify_layer_inverted_input() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(2.0, 1.0)],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    match verify_layer_certificate(&e) {
        CertificateStatus::Invalid { reason } => assert!(reason.contains("input dim 0")),
        other => panic!("expected Invalid, got {other:?}"),
    }
}

#[test]
fn test_verify_layer_inverted_output() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(3.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    match verify_layer_certificate(&e) {
        CertificateStatus::Invalid { reason } => assert!(reason.contains("output dim 0")),
        other => panic!("expected Invalid, got {other:?}"),
    }
}

#[test]
fn test_verify_layer_nan_bounds() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(f64::NAN, 1.0)],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    assert!(matches!(
        verify_layer_certificate(&e),
        CertificateStatus::Invalid { .. }
    ));
}

#[test]
fn test_verify_layer_infinity_bounds() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, f64::INFINITY)],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    assert!(matches!(
        verify_layer_certificate(&e),
        CertificateStatus::Invalid { .. }
    ));
}

// -- chain verification (2-layer and 3-layer) --

#[test]
fn test_verify_chain_two_layer_valid() {
    let r = verify_chain_certificate(&chain(vec![linear(), relu()], "robustness", "net0"));
    assert_eq!(r.overall_status, CertificateStatus::Valid);
    assert_eq!(r.layer_statuses.len(), 2);
    assert!((r.coverage - 1.0).abs() < 1e-9);
    assert_eq!(r.trust_level, ChainTrustLevel::Numerical);
}

#[test]
fn test_verify_chain_three_layer_valid() {
    let r = verify_chain_certificate(&chain(
        vec![linear(), relu(), third()],
        "robustness",
        "net0",
    ));
    assert_eq!(r.overall_status, CertificateStatus::Valid);
    assert_eq!(r.layer_statuses.len(), 3);
    assert_eq!(r.trust_level, ChainTrustLevel::Numerical);
}

// -- continuity --

#[test]
fn test_chain_continuity_passes() {
    let r = verify_chain_certificate(&chain(vec![linear(), relu()], "t", "n"));
    assert_eq!(r.overall_status, CertificateStatus::Valid);
    assert!(r.notes.is_empty());
}

#[test]
fn test_chain_continuity_fails_on_gap() {
    let gap = entry(
        1,
        VerificationMethod::CROWN,
        vec![(10.0, 20.0), (10.0, 20.0)],
        vec![(0.0, 1.0), (0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let r = verify_chain_certificate(&chain(vec![linear(), gap], "t", "n"));
    assert!(matches!(
        r.overall_status,
        CertificateStatus::Invalid { .. }
    ));
    assert!(r.notes.iter().any(|n| n.contains("not continuous")));
}

#[test]
fn test_chain_continuity_dimension_mismatch() {
    let e1 = entry(
        1,
        VerificationMethod::IBP,
        vec![(0.5, 2.5)],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let r = verify_chain_certificate(&chain(vec![linear(), e1], "t", "n"));
    assert!(matches!(
        r.overall_status,
        CertificateStatus::Invalid { .. }
    ));
}

// -- coverage --

#[test]
fn test_chain_coverage_passes() {
    let c = chain(vec![linear(), relu()], "t", "n");
    assert!(verify_chain_coverage(
        &c,
        &[(0.0, 1.0), (0.0, 1.0)],
        &[(0.5, 2.5), (0.5, 2.5)]
    ));
}

#[test]
fn test_chain_coverage_fails_wrong_output() {
    let c = chain(vec![linear(), relu()], "t", "n");
    assert!(!verify_chain_coverage(
        &c,
        &[(0.0, 1.0), (0.0, 1.0)],
        &[(99.0, 100.0), (99.0, 100.0)]
    ));
}

// -- empty and single-layer chains --

#[test]
fn test_verify_chain_empty() {
    let r = verify_chain_certificate(&chain(vec![], "t", "n"));
    assert!(matches!(
        r.overall_status,
        CertificateStatus::Invalid { .. }
    ));
    assert_eq!(r.layer_statuses.len(), 0);
}

#[test]
fn test_verify_chain_single_layer() {
    let r = verify_chain_certificate(&chain(vec![linear()], "t", "n"));
    assert_eq!(r.overall_status, CertificateStatus::Valid);
    assert_eq!(r.layer_statuses.len(), 1);
    assert_eq!(r.trust_level, ChainTrustLevel::Formal);
}

// -- trust consistency --

#[test]
fn test_trust_consistency_correct() {
    let c = chain(vec![linear(), relu()], "t", "n");
    assert!(verify_trust_consistency(&c, ChainTrustLevel::Numerical));
}

#[test]
fn test_trust_consistency_incorrect() {
    let c = chain(vec![linear(), relu()], "t", "n");
    assert!(!verify_trust_consistency(&c, ChainTrustLevel::Formal));
}

#[test]
fn test_trust_consistency_all_formal() {
    let e0 = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(0.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = entry(
        1,
        VerificationMethod::IBP,
        vec![(0.0, 2.0)],
        vec![(0.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    assert!(verify_trust_consistency(
        &chain(vec![e0, e1], "t", "n"),
        ChainTrustLevel::Formal
    ));
}

#[test]
fn test_trust_consistency_heuristic_dominates() {
    let e0 = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(0.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = entry(
        1,
        VerificationMethod::Zonotope,
        vec![(0.0, 2.0)],
        vec![(0.0, 3.0)],
        ChainTrustLevel::Heuristic,
    );
    let c = chain(vec![e0, e1], "t", "n");
    assert!(verify_trust_consistency(&c, ChainTrustLevel::Heuristic));
    assert!(!verify_trust_consistency(&c, ChainTrustLevel::Numerical));
}

// -- bound containment --

#[test]
fn test_bound_containment_exact() {
    assert!(verify_bound_containment(
        &[(1.0, 2.0), (3.0, 4.0)],
        &[(1.0, 2.0), (3.0, 4.0)]
    ));
}

#[test]
fn test_bound_containment_proper_subset() {
    assert!(verify_bound_containment(
        &[(1.1, 1.9), (3.1, 3.9)],
        &[(1.0, 2.0), (3.0, 4.0)]
    ));
}

#[test]
fn test_bound_containment_exceeds() {
    assert!(!verify_bound_containment(&[(0.5, 2.0)], &[(1.0, 2.0)]));
}

#[test]
fn test_bound_containment_dimension_mismatch() {
    assert!(!verify_bound_containment(
        &[(0.0, 1.0)],
        &[(0.0, 1.0), (0.0, 1.0)]
    ));
}

// -- specification verification --

#[test]
fn test_spec_classification_passes() {
    // dominant_min(3.0) >= other_max(1.0) + margin(1.0)
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(3.0, 5.0), (0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let spec = ClassificationSpec {
        dominant_class: 0,
        other_class: 1,
        margin: 1.0,
    };
    assert_eq!(
        verify_specification(&chain(vec![e], "cls", "n"), &spec),
        CertificateStatus::Valid
    );
}

#[test]
fn test_spec_classification_fails_insufficient_margin() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.5, 5.0), (0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let spec = ClassificationSpec {
        dominant_class: 0,
        other_class: 1,
        margin: 1.0,
    };
    assert!(matches!(
        verify_specification(&chain(vec![e], "cls", "n"), &spec),
        CertificateStatus::Invalid { .. }
    ));
}

#[test]
fn test_spec_classification_out_of_bounds_dim() {
    let e = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let spec = ClassificationSpec {
        dominant_class: 0,
        other_class: 5,
        margin: 0.0,
    };
    assert!(matches!(
        verify_specification(&chain(vec![e], "cls", "n"), &spec),
        CertificateStatus::Invalid { .. }
    ));
}

#[test]
fn test_spec_empty_chain() {
    let spec = ClassificationSpec {
        dominant_class: 0,
        other_class: 1,
        margin: 0.0,
    };
    assert!(matches!(
        verify_specification(&chain(vec![], "cls", "n"), &spec),
        CertificateStatus::Invalid { .. }
    ));
}

// -- report merging --

#[test]
fn test_merge_reports_both_valid() {
    let ra = verify_chain_certificate(&chain(vec![linear()], "A", "n"));
    let rb = verify_chain_certificate(&chain(vec![relu()], "B", "n"));
    let m = merge_reports(&ra, &rb);
    assert_eq!(m.overall_status, CertificateStatus::Valid);
    assert_eq!(m.layer_statuses.len(), 2);
    assert_eq!(m.trust_level, ChainTrustLevel::Numerical);
    assert!((m.coverage - 1.0).abs() < 1e-9);
}

#[test]
fn test_merge_reports_one_invalid() {
    let ra = verify_chain_certificate(&chain(vec![linear()], "A", "n"));
    let rb = simple_report(
        vec![CertificateStatus::Invalid {
            reason: "bad".to_owned(),
        }],
        CertificateStatus::Invalid {
            reason: "bad".to_owned(),
        },
        ChainTrustLevel::Heuristic,
        0.0,
    );
    let m = merge_reports(&ra, &rb);
    assert!(matches!(
        m.overall_status,
        CertificateStatus::Invalid { .. }
    ));
    assert_eq!(m.trust_level, ChainTrustLevel::Heuristic);
}

#[test]
fn test_merge_reports_coverage_weighted() {
    let ra = simple_report(
        vec![CertificateStatus::Valid, CertificateStatus::Valid],
        CertificateStatus::Valid,
        ChainTrustLevel::Formal,
        1.0,
    );
    let rb = simple_report(
        vec![CertificateStatus::Valid],
        CertificateStatus::Valid,
        ChainTrustLevel::Formal,
        0.0,
    );
    let m = merge_reports(&ra, &rb);
    assert!((m.coverage - 2.0 / 3.0).abs() < 1e-9);
}

// -- report summary --

#[test]
fn test_report_summary_format() {
    let r = verify_chain_certificate(&chain(vec![linear(), relu()], "t", "n"));
    let s = report_summary(&r);
    assert!(s.contains("VerificationReport"));
    assert!(s.contains("Valid"));
    assert!(s.contains("Numerical"));
    assert!(s.contains("2/2"));
}

#[test]
fn test_report_summary_includes_notes() {
    let mut r = simple_report(
        vec![],
        CertificateStatus::Inconclusive,
        ChainTrustLevel::Heuristic,
        0.0,
    );
    r.notes.push("something went wrong".to_owned());
    assert!(report_summary(&r).contains("something went wrong"));
}

// -- certificate strength --

#[test]
fn test_strength_perfect_collapse() {
    let s = certificate_strength(&[(5.0, 5.0), (5.0, 5.0)], &[(0.0, 10.0), (0.0, 10.0)]).unwrap();
    assert!((s - 1.0).abs() < 1e-9);
}

#[test]
fn test_strength_no_improvement() {
    let s = certificate_strength(&[(0.0, 10.0), (0.0, 10.0)], &[(0.0, 10.0), (0.0, 10.0)]).unwrap();
    assert!(s.abs() < 1e-9);
}

#[test]
fn test_strength_partial() {
    let s = certificate_strength(&[(2.5, 7.5)], &[(0.0, 10.0)]).unwrap();
    assert!((s - 0.5).abs() < 1e-9);
}

#[test]
fn test_strength_zero_width_bbox_returns_none() {
    assert!(certificate_strength(&[(0.0, 0.0)], &[(5.0, 5.0)]).is_none());
}

#[test]
fn test_strength_dimension_mismatch_returns_none() {
    assert!(certificate_strength(&[(0.0, 1.0)], &[(0.0, 1.0), (0.0, 1.0)]).is_none());
}

#[test]
fn test_strength_empty_returns_none() {
    assert!(certificate_strength(&[], &[]).is_none());
}

// -- CertificateStatus Display --

#[test]
fn test_certificate_status_display() {
    assert_eq!(format!("{}", CertificateStatus::Valid), "Valid");
    assert_eq!(
        format!(
            "{}",
            CertificateStatus::Invalid {
                reason: "oops".to_owned()
            }
        ),
        "Invalid: oops"
    );
    assert_eq!(
        format!("{}", CertificateStatus::Inconclusive),
        "Inconclusive"
    );
}

// -- edge cases --

#[test]
fn test_chain_partial_invalid_layers() {
    let bad = entry(
        1,
        VerificationMethod::IBP,
        vec![(0.5, 2.5), (0.5, 2.5)],
        vec![(f64::NAN, 1.0), (0.0, 1.0)],
        ChainTrustLevel::Formal,
    );
    let r = verify_chain_certificate(&chain(vec![linear(), bad], "t", "n"));
    assert!(matches!(
        r.overall_status,
        CertificateStatus::Invalid { .. }
    ));
    assert!((r.coverage - 0.5).abs() < 1e-9);
}

#[test]
fn test_chain_mismatched_dimensions() {
    let e0 = entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(0.0, 2.0), (0.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = entry(
        1,
        VerificationMethod::IBP,
        vec![(0.0, 2.0)],
        vec![(0.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let r = verify_chain_certificate(&chain(vec![e0, e1], "t", "n"));
    assert!(matches!(
        r.overall_status,
        CertificateStatus::Invalid { .. }
    ));
}
