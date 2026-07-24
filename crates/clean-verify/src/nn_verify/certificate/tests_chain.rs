// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for certificate chain verification (`chain.rs`).

use super::chain::{
    chain_trust_level, format_chain_summary, merge_chains, verify_chain_continuity,
    verify_chain_coverage, CertificateChain, CertificateEntry, ChainTrustLevel, VerificationMethod,
};

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn make_entry(
    layer_index: usize,
    method: VerificationMethod,
    input_bounds: Vec<(f64, f64)>,
    output_bounds: Vec<(f64, f64)>,
    trust_level: ChainTrustLevel,
) -> CertificateEntry {
    CertificateEntry {
        layer_index,
        method,
        input_bounds,
        output_bounds,
        trust_level,
    }
}

fn make_chain(
    entries: Vec<CertificateEntry>,
    property: &str,
    network_id: &str,
) -> CertificateChain {
    CertificateChain {
        entries,
        property: property.to_owned(),
        network_id: network_id.to_owned(),
    }
}

/// Build a simple 3-layer continuous chain: [0,1]^2 -> [1,2]^2 -> [2,3]^2 -> [3,4]^2
fn make_continuous_chain() -> CertificateChain {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(1.0, 2.0), (1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::CROWN,
        vec![(1.0, 2.0), (1.0, 2.0)],
        vec![(2.0, 3.0), (2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );
    let e2 = make_entry(
        2,
        VerificationMethod::AlphaCROWN,
        vec![(2.0, 3.0), (2.0, 3.0)],
        vec![(3.0, 4.0), (3.0, 4.0)],
        ChainTrustLevel::Formal,
    );
    make_chain(vec![e0, e1, e2], "robustness", "net_001")
}

// ---------------------------------------------------------------------------
// verify_chain_continuity tests
// ---------------------------------------------------------------------------

#[test]
fn test_continuity_empty_chain() {
    let chain = make_chain(vec![], "empty", "net");
    assert!(verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_single_entry() {
    let e = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e], "single", "net");
    assert!(verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_valid_chain() {
    let chain = make_continuous_chain();
    assert!(verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_gap_in_bounds() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(3.0, 4.0)], // gap: does not match e0's output
        vec![(4.0, 5.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1], "gap", "net");
    assert!(!verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_dimension_mismatch() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0), (0.0, 1.0)],
        vec![(1.0, 2.0), (1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(1.0, 2.0)], // 1D vs 2D
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1], "dim_mismatch", "net");
    assert!(!verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_upper_bound_mismatch() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(1.0, 2.5)], // upper bound mismatch
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1], "upper_mismatch", "net");
    assert!(!verify_chain_continuity(&chain));
}

#[test]
fn test_continuity_within_epsilon() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(1.0, 2.0 + 1e-12)], // within epsilon
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1], "epsilon", "net");
    assert!(verify_chain_continuity(&chain));
}

// ---------------------------------------------------------------------------
// verify_chain_coverage tests
// ---------------------------------------------------------------------------

#[test]
fn test_coverage_full() {
    let chain = make_continuous_chain();
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let output = [(3.0, 4.0), (3.0, 4.0)];
    assert!(verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_coverage_partial_input_mismatch() {
    let chain = make_continuous_chain();
    let input = [(0.5, 1.5), (0.0, 1.0)]; // wrong input
    let output = [(3.0, 4.0), (3.0, 4.0)];
    assert!(!verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_coverage_partial_output_mismatch() {
    let chain = make_continuous_chain();
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let output = [(3.0, 5.0), (3.0, 4.0)]; // wrong output
    assert!(!verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_coverage_empty_chain() {
    let chain = make_chain(vec![], "empty", "net");
    let input = [(0.0, 1.0)];
    let output = [(1.0, 2.0)];
    assert!(!verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_coverage_single_entry() {
    let e = make_entry(
        0,
        VerificationMethod::Zonotope,
        vec![(0.0, 1.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );
    let chain = make_chain(vec![e], "single", "net");
    assert!(verify_chain_coverage(&chain, &[(0.0, 1.0)], &[(2.0, 3.0)]));
}

#[test]
fn test_coverage_dimension_mismatch_input() {
    let chain = make_continuous_chain();
    let input = [(0.0, 1.0)]; // 1D vs chain's 2D
    let output = [(3.0, 4.0), (3.0, 4.0)];
    assert!(!verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_coverage_dimension_mismatch_output() {
    let chain = make_continuous_chain();
    let input = [(0.0, 1.0), (0.0, 1.0)];
    let output = [(3.0, 4.0)]; // 1D vs chain's 2D
    assert!(!verify_chain_coverage(&chain, &input, &output));
}

// ---------------------------------------------------------------------------
// chain_trust_level tests
// ---------------------------------------------------------------------------

#[test]
fn test_trust_all_formal() {
    let entries = vec![
        make_entry(
            0,
            VerificationMethod::IBP,
            vec![(0.0, 1.0)],
            vec![(1.0, 2.0)],
            ChainTrustLevel::Formal,
        ),
        make_entry(
            1,
            VerificationMethod::CROWN,
            vec![(1.0, 2.0)],
            vec![(2.0, 3.0)],
            ChainTrustLevel::Formal,
        ),
    ];
    let chain = make_chain(entries, "formal", "net");
    assert_eq!(chain_trust_level(&chain), ChainTrustLevel::Formal);
}

#[test]
fn test_trust_mixed_levels() {
    let chain = make_continuous_chain(); // Formal, Numerical, Formal
    assert_eq!(chain_trust_level(&chain), ChainTrustLevel::Numerical);
}

#[test]
fn test_trust_single_heuristic_dominates() {
    let entries = vec![
        make_entry(
            0,
            VerificationMethod::IBP,
            vec![(0.0, 1.0)],
            vec![(1.0, 2.0)],
            ChainTrustLevel::Formal,
        ),
        make_entry(
            1,
            VerificationMethod::IBP,
            vec![(1.0, 2.0)],
            vec![(2.0, 3.0)],
            ChainTrustLevel::Heuristic,
        ),
        make_entry(
            2,
            VerificationMethod::IBP,
            vec![(2.0, 3.0)],
            vec![(3.0, 4.0)],
            ChainTrustLevel::Formal,
        ),
    ];
    let chain = make_chain(entries, "heuristic", "net");
    assert_eq!(chain_trust_level(&chain), ChainTrustLevel::Heuristic);
}

#[test]
fn test_trust_empty_chain_is_formal() {
    let chain = make_chain(vec![], "empty", "net");
    assert_eq!(chain_trust_level(&chain), ChainTrustLevel::Formal);
}

#[test]
fn test_trust_single_entry() {
    let entries = vec![make_entry(
        0,
        VerificationMethod::McCormick,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Numerical,
    )];
    let chain = make_chain(entries, "single", "net");
    assert_eq!(chain_trust_level(&chain), ChainTrustLevel::Numerical);
}

#[test]
fn test_trust_level_ordering() {
    assert!(ChainTrustLevel::Formal > ChainTrustLevel::Numerical);
    assert!(ChainTrustLevel::Numerical > ChainTrustLevel::Heuristic);
    assert!(ChainTrustLevel::Formal > ChainTrustLevel::Heuristic);
}

// ---------------------------------------------------------------------------
// merge_chains tests
// ---------------------------------------------------------------------------

#[test]
fn test_merge_compatible_chains() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::CROWN,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );

    let chain_a = make_chain(vec![e0], "robustness", "net_001");
    let chain_b = make_chain(vec![e1], "robustness", "net_001");

    let merged = merge_chains(&chain_a, &chain_b);
    assert!(merged.is_some());
    let merged = merged.unwrap();
    assert_eq!(merged.entries.len(), 2);
    assert_eq!(merged.network_id, "net_001");
    assert_eq!(merged.property, "robustness");
}

#[test]
fn test_merge_different_properties_concatenates() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::CROWN,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );

    let chain_a = make_chain(vec![e0], "prop_A", "net_001");
    let chain_b = make_chain(vec![e1], "prop_B", "net_001");

    let merged = merge_chains(&chain_a, &chain_b).unwrap();
    assert_eq!(merged.property, "prop_A + prop_B");
}

#[test]
fn test_merge_incompatible_network_id() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );

    let chain_a = make_chain(vec![e0], "rob", "net_001");
    let chain_b = make_chain(vec![e1], "rob", "net_002");

    assert!(merge_chains(&chain_a, &chain_b).is_none());
}

#[test]
fn test_merge_incompatible_bounds() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(5.0, 6.0)], // does not match e0 output
        vec![(6.0, 7.0)],
        ChainTrustLevel::Formal,
    );

    let chain_a = make_chain(vec![e0], "rob", "net_001");
    let chain_b = make_chain(vec![e1], "rob", "net_001");

    assert!(merge_chains(&chain_a, &chain_b).is_none());
}

#[test]
fn test_merge_empty_chain_a() {
    let chain_a = make_chain(vec![], "rob", "net_001");
    let e1 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let chain_b = make_chain(vec![e1], "rob", "net_001");

    assert!(merge_chains(&chain_a, &chain_b).is_none());
}

#[test]
fn test_merge_empty_chain_b() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let chain_a = make_chain(vec![e0], "rob", "net_001");
    let chain_b = make_chain(vec![], "rob", "net_001");

    assert!(merge_chains(&chain_a, &chain_b).is_none());
}

#[test]
fn test_merge_dimension_mismatch() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0), (1.0, 2.0)], // 2D output
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(1.0, 2.0)], // 1D input
        vec![(2.0, 3.0)],
        ChainTrustLevel::Formal,
    );

    let chain_a = make_chain(vec![e0], "rob", "net_001");
    let chain_b = make_chain(vec![e1], "rob", "net_001");

    assert!(merge_chains(&chain_a, &chain_b).is_none());
}

#[test]
fn test_merge_preserves_entry_order() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(0.0, 1.0)],
        vec![(1.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::CROWN,
        vec![(1.0, 2.0)],
        vec![(2.0, 3.0)],
        ChainTrustLevel::Numerical,
    );
    let e2 = make_entry(
        2,
        VerificationMethod::AlphaCROWN,
        vec![(2.0, 3.0)],
        vec![(3.0, 4.0)],
        ChainTrustLevel::Formal,
    );

    let chain_a = make_chain(vec![e0], "rob", "net");
    let chain_b = make_chain(vec![e1, e2], "rob", "net");

    let merged = merge_chains(&chain_a, &chain_b).unwrap();
    assert_eq!(merged.entries.len(), 3);
    assert_eq!(merged.entries[0].layer_index, 0);
    assert_eq!(merged.entries[1].layer_index, 1);
    assert_eq!(merged.entries[2].layer_index, 2);
}

// ---------------------------------------------------------------------------
// format_chain_summary tests
// ---------------------------------------------------------------------------

#[test]
fn test_format_summary_continuous_chain() {
    let chain = make_continuous_chain();
    let summary = format_chain_summary(&chain);
    assert!(summary.contains("net_001"));
    assert!(summary.contains("robustness"));
    assert!(summary.contains("layers=3"));
    assert!(summary.contains("continuous=true"));
    assert!(summary.contains("trust=Numerical")); // min of Formal, Numerical, Formal
}

#[test]
fn test_format_summary_empty_chain() {
    let chain = make_chain(vec![], "empty", "net");
    let summary = format_chain_summary(&chain);
    assert!(summary.contains("layers=0"));
    assert!(summary.contains("input_dim=0"));
    assert!(summary.contains("output_dim=0"));
}

#[test]
fn test_format_summary_shows_unique_methods() {
    let chain = make_continuous_chain(); // IBP, CROWN, alpha-CROWN
    let summary = format_chain_summary(&chain);
    assert!(summary.contains("IBP"));
    assert!(summary.contains("CROWN"));
    assert!(summary.contains("alpha-CROWN"));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_chain_with_zero_width_bounds() {
    let e0 = make_entry(
        0,
        VerificationMethod::IBP,
        vec![(1.0, 1.0)], // zero-width interval (point)
        vec![(2.0, 2.0)],
        ChainTrustLevel::Formal,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::IBP,
        vec![(2.0, 2.0)],
        vec![(3.0, 3.0)],
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e0, e1], "point", "net");
    assert!(verify_chain_continuity(&chain));
}

#[test]
fn test_chain_with_negative_bounds() {
    let e0 = make_entry(
        0,
        VerificationMethod::McCormick,
        vec![(-5.0, -1.0)],
        vec![(-3.0, 0.0)],
        ChainTrustLevel::Numerical,
    );
    let e1 = make_entry(
        1,
        VerificationMethod::McCormick,
        vec![(-3.0, 0.0)],
        vec![(-1.0, 2.0)],
        ChainTrustLevel::Numerical,
    );
    let chain = make_chain(vec![e0, e1], "negative", "net");
    assert!(verify_chain_continuity(&chain));
    assert!(verify_chain_coverage(
        &chain,
        &[(-5.0, -1.0)],
        &[(-1.0, 2.0)]
    ));
}

#[test]
fn test_chain_with_high_dimensional_bounds() {
    let dim = 100;
    let input: Vec<(f64, f64)> = (0..dim).map(|i| (i as f64, i as f64 + 1.0)).collect();
    let output: Vec<(f64, f64)> = (0..dim).map(|i| (i as f64 + 1.0, i as f64 + 2.0)).collect();
    let e = make_entry(
        0,
        VerificationMethod::Zonotope,
        input.clone(),
        output.clone(),
        ChainTrustLevel::Formal,
    );
    let chain = make_chain(vec![e], "high_dim", "net");
    assert!(verify_chain_coverage(&chain, &input, &output));
}

#[test]
fn test_verification_method_display() {
    assert_eq!(VerificationMethod::IBP.to_string(), "IBP");
    assert_eq!(VerificationMethod::CROWN.to_string(), "CROWN");
    assert_eq!(VerificationMethod::AlphaCROWN.to_string(), "alpha-CROWN");
    assert_eq!(VerificationMethod::McCormick.to_string(), "McCormick");
    assert_eq!(VerificationMethod::Zonotope.to_string(), "Zonotope");
    assert_eq!(VerificationMethod::Mixed.to_string(), "Mixed");
}

#[test]
fn test_chain_trust_level_display() {
    assert_eq!(ChainTrustLevel::Formal.to_string(), "Formal");
    assert_eq!(ChainTrustLevel::Numerical.to_string(), "Numerical");
    assert_eq!(ChainTrustLevel::Heuristic.to_string(), "Heuristic");
}
