// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for PC certificate serialization, deserialization, and replay.

use std::collections::BTreeSet;

use super::gf2_algebra::{PcProof, PcStepTracked};
use super::pc_certificate::*;

// =========================================================================
// Text format serialization
// =========================================================================

#[test]
fn test_certificate_to_text_basic() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let cert = PcCertificate::from_proof(&proof, 2);
    let text = cert.to_text();

    assert!(text.contains("PC-GF2 v1"));
    assert!(text.contains("CLAUSES 2"));
    assert!(text.contains("STEPS 3"));
    assert!(text.contains("MAXDEG 1"));
    assert!(text.contains("0 AXIOM 0"));
    assert!(text.contains("1 AXIOM 1"));
    assert!(text.contains("2 ADD 0 1"));
    assert!(text.contains("RESULT 1"));
}

#[test]
fn test_certificate_to_text_mulvar() {
    let cert = PcCertificate::new(
        3,
        vec![PcStepTracked::ClauseAxiom(0), PcStepTracked::MulVar(0, 1)],
        2,
    );
    let text = cert.to_text();
    assert!(text.contains("1 MULVAR 0 1"));
}

#[test]
fn test_certificate_to_text_mulpoly() {
    let cert = PcCertificate::new(
        2,
        vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::ClauseAxiom(1),
            PcStepTracked::MulPoly(0, 1),
        ],
        2,
    );
    let text = cert.to_text();
    assert!(text.contains("2 MULPOLY 0 1"));
}

#[test]
fn test_certificate_to_text_boolax() {
    let cert = PcCertificate::new(1, vec![PcStepTracked::BooleanAxiom(3)], 0);
    let text = cert.to_text();
    assert!(text.contains("0 BOOLAX 3"));
}

#[test]
fn test_certificate_to_text_weaken() {
    let mut mono = BTreeSet::new();
    mono.insert(0u32);
    mono.insert(2u32);
    let cert = PcCertificate::new(
        1,
        vec![
            PcStepTracked::ClauseAxiom(0),
            PcStepTracked::Weaken(0, mono),
        ],
        2,
    );
    let text = cert.to_text();
    // BTreeSet iterates in order: 0, 2
    assert!(text.contains("1 WEAKEN 0 0,2"));
}

// =========================================================================
// Text format deserialization
// =========================================================================

#[test]
fn test_certificate_roundtrip_text() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps.clone()).expect("should build");
    let cert = PcCertificate::from_proof(&proof, 2);
    let text = cert.to_text();
    let parsed = PcCertificate::from_text(&text).expect("should parse");

    assert_eq!(parsed.num_clauses, 2);
    assert_eq!(parsed.steps.len(), 3);
    assert_eq!(parsed.max_degree, 1);
    assert_eq!(parsed.steps, steps);
}

#[test]
fn test_certificate_roundtrip_php() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let proof = PcProof::build(&clauses, steps.clone()).expect("should build");
    let cert = PcCertificate::from_proof(&proof, 3);
    let text = cert.to_text();
    let parsed = PcCertificate::from_text(&text).expect("should parse");

    assert_eq!(parsed.steps, steps);
    assert_eq!(parsed.max_degree, 2);
}

#[test]
fn test_certificate_roundtrip_all_step_types() {
    let mut mono = BTreeSet::new();
    mono.insert(1u32);
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::BooleanAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::MulPoly(0, 2),
        PcStepTracked::Weaken(0, mono.clone()),
    ];
    let cert = PcCertificate::new(2, steps.clone(), 3);
    let text = cert.to_text();
    let parsed = PcCertificate::from_text(&text).expect("should parse");
    assert_eq!(parsed.steps, steps);
}

#[test]
fn test_certificate_parse_malformed_header() {
    let result = PcCertificate::from_text("GARBAGE\n");
    assert!(result.is_err());
}

#[test]
fn test_certificate_parse_empty() {
    let result = PcCertificate::from_text("");
    assert!(result.is_err());
}

#[test]
fn test_certificate_parse_step_count_mismatch() {
    let text = "PC-GF2 v1\nCLAUSES 2\nSTEPS 5\nMAXDEG 1\n---\n0 AXIOM 0\n---\nRESULT 1\n";
    let result = PcCertificate::from_text(text);
    assert!(result.is_err());
}

#[test]
fn test_certificate_parse_unknown_operation() {
    let text = "PC-GF2 v1\nCLAUSES 1\nSTEPS 1\nMAXDEG 0\n---\n0 FOOBAR 0\n---\nRESULT 1\n";
    let result = PcCertificate::from_text(text);
    assert!(result.is_err());
}

// =========================================================================
// Replay verification
// =========================================================================

#[test]
fn test_replay_x_and_not_x() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let cert = PcCertificate::new(2, steps, 1);
    let result = PcCertificateVerifier::verify(&cert, &clauses).expect("should verify");
    assert!(result.verified);
    assert_eq!(result.num_steps, 3);
    assert_eq!(result.max_degree, 1);
    assert!(result.degree_matches);
}

#[test]
fn test_replay_php_2_1() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let cert = PcCertificate::new(3, steps, 2);
    let result = PcCertificateVerifier::verify(&cert, &clauses).expect("should verify");
    assert!(result.verified);
    assert_eq!(result.max_degree, 2);
}

#[test]
fn test_replay_invalid_step() {
    let clauses = vec![vec![1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::Add(0, 5), // invalid
    ];
    let cert = PcCertificate::new(1, steps, 1);
    let result = PcCertificateVerifier::verify(&cert, &clauses);
    assert!(result.is_err());
}

#[test]
fn test_replay_no_contradiction() {
    let clauses = vec![vec![1]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)];
    let cert = PcCertificate::new(1, steps, 1);
    let result = PcCertificateVerifier::verify(&cert, &clauses);
    assert!(result.is_err());
}

#[test]
fn test_replay_degree_mismatch_detected() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    // Claim wrong max degree.
    let cert = PcCertificate::new(2, steps, 5);
    let result = PcCertificateVerifier::verify(&cert, &clauses).expect("should verify");
    assert!(result.verified);
    assert!(!result.degree_matches); // claimed 5, actual 1
}

// =========================================================================
// Full pipeline: serialize -> deserialize -> replay
// =========================================================================

#[test]
fn test_full_pipeline_x_and_not_x() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");

    // Create certificate from proof
    let cert = PcCertificate::from_proof(&proof, 2);

    // Serialize to text
    let text = cert.to_text();

    // Deserialize from text
    let parsed = PcCertificate::from_text(&text).expect("should parse");

    // Replay against clauses
    let result = PcCertificateVerifier::verify(&parsed, &clauses).expect("should verify");
    assert!(result.verified);
    assert!(result.degree_matches);
}

#[test]
fn test_full_pipeline_php_2_1() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let cert = PcCertificate::from_proof(&proof, 3);
    let text = cert.to_text();
    let parsed = PcCertificate::from_text(&text).expect("should parse");
    let result = PcCertificateVerifier::verify(&parsed, &clauses).expect("should verify");
    assert!(result.verified);
    assert!(result.degree_matches);
    assert_eq!(result.max_degree, 2);
}
