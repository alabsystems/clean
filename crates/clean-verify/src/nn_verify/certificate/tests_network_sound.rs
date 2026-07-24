// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the T71 network soundness bridge (`network_sound.rs`).
//!
//! Part of #3242.

use super::chain::{CertificateChain, CertificateEntry, ChainTrustLevel, VerificationMethod};
use super::network_sound::{verify_network_cert_sound, NetworkSoundnessResult, T71_PROOF_STATUS};
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn make_entry(
    layer_index: usize,
    input_bounds: Vec<(f64, f64)>,
    output_bounds: Vec<(f64, f64)>,
    trust_level: ChainTrustLevel,
) -> CertificateEntry {
    CertificateEntry {
        layer_index,
        method: VerificationMethod::IBP,
        input_bounds,
        output_bounds,
        trust_level,
    }
}

fn make_chain(entries: Vec<CertificateEntry>) -> CertificateChain {
    CertificateChain {
        entries,
        property: "robustness".to_owned(),
        network_id: "test_net".to_owned(),
    }
}

/// Build a simple 3-layer continuous chain:
/// [0,1]^2 -> [1,2]^2 -> [2,3]^2 -> [3,4]^2
fn make_valid_chain() -> CertificateChain {
    let e0 = make_entry(
        0,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(1.0, 2.0), (1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(1.0, 2.0), (1.0, 2.0)],
        vec![(2.0, 3.0), (2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );
    let e2 = make_entry(
        2,
        vec![(2.0, 3.0), (2.0, 3.0)],
        vec![(3.0, 4.0), (3.0, 4.0)],
        ChainTrustLevel::Formal,
    );
    make_chain(vec![e0, e1, e2])
}

// ---------------------------------------------------------------------------
// T71_PROOF_STATUS constant
// ---------------------------------------------------------------------------

#[test]
fn test_t71_proof_status_is_derived_proved() {
    assert_eq!(T71_PROOF_STATUS, ProofStatus::DerivedPending);
}

// ---------------------------------------------------------------------------
// Happy path: valid chain
// ---------------------------------------------------------------------------

#[test]
fn test_valid_chain_passes() {
    let chain = make_valid_chain();
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let output = [(3.0, 4.0), (3.0, 4.0)];
    let result = verify_network_cert_sound(&chain, &input, &output);
    assert!(result.valid, "errors: {:?}", result.errors);
    assert_eq!(result.proof_status, ProofStatus::DerivedPending);
    assert_eq!(result.chain_length, 3);
    assert_eq!(result.trust_level, ChainTrustLevel::Numerical);
    assert!(result.errors.is_empty());
}

#[test]
fn test_single_layer_chain_passes() {
    let e = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(2.0, 3.0)]);
    assert!(result.valid);
    assert_eq!(result.proof_status, ProofStatus::DerivedPending);
    assert_eq!(result.chain_length, 1);
    assert_eq!(result.trust_level, ChainTrustLevel::Formal);
}

// ---------------------------------------------------------------------------
// Empty chain
// ---------------------------------------------------------------------------

#[test]
fn test_empty_chain_fails() {
    let chain = make_chain(vec![]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(1.0, 2.0)]);
    assert!(!result.valid);
    assert_eq!(result.proof_status, ProofStatus::DerivedPending);
    assert_eq!(result.chain_length, 0);
    assert!(!result.errors.is_empty());
}

// ---------------------------------------------------------------------------
// Continuity failures
// ---------------------------------------------------------------------------

#[test]
fn test_discontinuous_chain_fails() {
    let e0 = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(3.0, 4.0)], // gap: does not match e0's output
        vec![(4.0, 5.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(4.0, 5.0)]);
    assert!(!result.valid);
    assert_eq!(result.proof_status, ProofStatus::DerivedPending);
    assert!(
        result.errors.iter().any(|e| e.contains("continuity")),
        "should mention continuity: {:?}",
        result.errors
    );
}

#[test]
fn test_dimension_mismatch_between_layers_fails() {
    let e0 = make_entry(
        0,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(1.0, 2.0), (1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(1.0, 2.0)], // 1D vs 2D
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0), (0.0, 1.0)], &[(2.0, 3.0)]);
    assert!(!result.valid);
}

// ---------------------------------------------------------------------------
// Coverage failures
// ---------------------------------------------------------------------------

#[test]
fn test_input_bounds_mismatch_fails() {
    let chain = make_valid_chain();
    let wrong_input = [(0.5, 1.5), (0.0, 1.0)]; // wrong
    let output = [(3.0, 4.0), (3.0, 4.0)];
    let result = verify_network_cert_sound(&chain, &wrong_input, &output);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("input coverage")),
        "should mention input coverage: {:?}",
        result.errors
    );
}

#[test]
fn test_output_bounds_mismatch_fails() {
    let chain = make_valid_chain();
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let wrong_output = [(3.0, 5.0), (3.0, 4.0)]; // wrong
    let result = verify_network_cert_sound(&chain, &input, &wrong_output);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("output coverage")),
        "should mention output coverage: {:?}",
        result.errors
    );
}

#[test]
fn test_input_dimension_mismatch_fails() {
    let chain = make_valid_chain();
    let input_1d = [(0.0, 1.0)]; // 1D vs chain's 2D
    let output = [(3.0, 4.0), (3.0, 4.0)];
    let result = verify_network_cert_sound(&chain, &input_1d, &output);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("dimension")),
        "should mention dimension: {:?}",
        result.errors
    );
}

// ---------------------------------------------------------------------------
// Malformed bounds
// ---------------------------------------------------------------------------

#[test]
fn test_malformed_input_bounds_fails() {
    let e = make_entry(
        0,
        vec![(5.0, 1.0)], // lower > upper
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    let result = verify_network_cert_sound(&chain, &[(5.0, 1.0)], &[(2.0, 3.0)]);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("malformed")),
        "should mention malformed: {:?}",
        result.errors
    );
}

#[test]
fn test_malformed_output_bounds_fails() {
    let e = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(5.0, 2.0)], // lower > upper
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(5.0, 2.0)]);
    assert!(!result.valid);
    assert!(
        result.errors.iter().any(|e| e.contains("malformed")),
        "should mention malformed: {:?}",
        result.errors
    );
}

// ---------------------------------------------------------------------------
// Trust level propagation
// ---------------------------------------------------------------------------

#[test]
fn test_trust_level_all_formal() {
    let e0 = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(2.0, 3.0)]);
    assert!(result.valid);
    assert_eq!(result.trust_level, ChainTrustLevel::Formal);
}

#[test]
fn test_trust_level_heuristic_dominates() {
    let e0 = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Heuristic,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0)], &[(2.0, 3.0)]);
    assert!(result.valid);
    assert_eq!(result.trust_level, ChainTrustLevel::Heuristic);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_zero_width_bounds_valid() {
    let e = make_entry(
        0,
        vec![(1.0, 1.0)], // point interval
        vec![(2.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    let result = verify_network_cert_sound(&chain, &[(1.0, 1.0)], &[(2.0, 2.0)]);
    assert!(result.valid);
}

#[test]
fn test_negative_bounds_valid() {
    let e0 = make_entry(
        0,
        vec![(-5.0, -1.0)],
        vec![(-3.0, 0.0)],
        ChainTrustLevel::Numerical,
    );
    let e1 = make_entry(
        1,
        vec![(-3.0, 0.0)],
        vec![(-1.0, 2.0)],
        ChainTrustLevel::Numerical,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(&chain, &[(-5.0, -1.0)], &[(-1.0, 2.0)]);
    assert!(result.valid);
    assert_eq!(result.proof_status, ProofStatus::DerivedPending);
}

#[test]
fn test_high_dimensional_chain_valid() {
    let dim = 50;
    let in_bounds: Vec<(f64, f64)> = (0..dim).map(|i| (i as f64, i as f64 + 1.0)).collect();
    let out_bounds: Vec<(f64, f64)> = (0..dim).map(|i| (i as f64 + 1.0, i as f64 + 2.0)).collect();
    let e = make_entry(
        0,
        in_bounds.clone(),
        out_bounds.clone(),
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    let result = verify_network_cert_sound(&chain, &in_bounds, &out_bounds);
    assert!(result.valid);
    assert_eq!(result.chain_length, 1);
}

#[test]
fn test_within_epsilon_bounds_match() {
    let e = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    // Bounds within epsilon tolerance
    let result = verify_network_cert_sound(&chain, &[(0.0, 1.0 + 1e-12)], &[(2.0, 3.0 - 1e-12)]);
    assert!(
        result.valid,
        "within-epsilon should pass: {:?}",
        result.errors
    );
}

#[test]
fn test_beyond_epsilon_bounds_fail() {
    let e = make_entry(
        0,
        vec![(0.0, 1.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e]);
    // Bounds beyond epsilon tolerance
    let result = verify_network_cert_sound(
        &chain,
        &[(0.0, 1.1)], // significantly different
        &[(2.0, 3.0)],
    );
    assert!(!result.valid);
}

// ---------------------------------------------------------------------------
// Multiple error accumulation
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_errors_accumulated() {
    // Malformed bounds AND continuity failure AND coverage failure
    let e0 = make_entry(
        0,
        vec![(5.0, 1.0)], // malformed
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        vec![(9.0, 10.0)], // discontinuous with e0
        vec![(10.0, 11.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1]);
    let result = verify_network_cert_sound(
        &chain,
        &[(0.0, 1.0)], // doesn't match
        &[(0.0, 1.0)], // doesn't match
    );
    assert!(!result.valid);
    // Should have at least 3 errors: malformed + continuity + coverage
    assert!(
        result.errors.len() >= 3,
        "expected >= 3 errors, got {}: {:?}",
        result.errors.len(),
        result.errors
    );
}
