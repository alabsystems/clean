// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Bonami-Beckner hypercontractivity module.
//!
//! Covers noise operator, level weights, hypercontractive norms,
//! Bonami-Beckner verification, and optimal rho computation.

use super::fourier::{compute_all_fourier, BooleanFunction};
use super::hypercontractivity::{
    bonami_beckner_bound, fourier_p_norm, hypercontractive_norm, level_k_weight,
    noise_operator_fourier, optimal_rho_for_q, verify_bonami_beckner, S50_BONAMI_BECKNER,
    S51_HYPERCONTRACTIVE_NORM,
};
use crate::spec::ProofStatus;

const TOL: f64 = 1e-8;

// -----------------------------------------------------------------------
// Noise operator tests
// -----------------------------------------------------------------------

#[test]
fn test_noise_operator_identity_at_rho_one() {
    // T_1 f = f: coefficients unchanged when rho = 1
    let coeffs = vec![0.5, 0.25, -0.25, 0.0];
    let result = noise_operator_fourier(&coeffs, 1.0);
    for (a, b) in result.iter().zip(coeffs.iter()) {
        assert!((a - b).abs() < TOL, "rho=1 should be identity");
    }
}

#[test]
fn test_noise_operator_zero_at_rho_zero() {
    // T_0 f = E[f]: only level-0 coefficient survives
    let coeffs = vec![0.5, 0.25, -0.25, 0.1];
    let result = noise_operator_fourier(&coeffs, 0.0);
    assert!((result[0] - 0.5).abs() < TOL, "level-0 should be preserved");
    assert!((result[1]).abs() < TOL, "level-1 should be zeroed");
    assert!((result[2]).abs() < TOL, "level-1 should be zeroed");
    assert!((result[3]).abs() < TOL, "level-2 should be zeroed");
}

#[test]
fn test_noise_operator_decay_by_level() {
    // For n=2: index 0 is level 0, indices 1,2 are level 1, index 3 is level 2
    let coeffs = vec![1.0, 1.0, 1.0, 1.0];
    let rho = 0.5;
    let result = noise_operator_fourier(&coeffs, rho);
    assert!((result[0] - 1.0).abs() < TOL, "level 0: rho^0 = 1");
    assert!((result[1] - 0.5).abs() < TOL, "level 1: rho^1 = 0.5");
    assert!((result[2] - 0.5).abs() < TOL, "level 1: rho^1 = 0.5");
    assert!((result[3] - 0.25).abs() < TOL, "level 2: rho^2 = 0.25");
}

#[test]
fn test_noise_operator_half_rho() {
    // Single coefficient at level 3 (n=3, index=0b111=7)
    let mut coeffs = vec![0.0; 8];
    coeffs[7] = 1.0;
    let rho = 0.5;
    let result = noise_operator_fourier(&coeffs, rho);
    assert!((result[7] - 0.125).abs() < TOL, "level 3: rho^3 = 0.125");
    // All others stay 0
    for (i, &v) in result.iter().enumerate() {
        if i != 7 {
            assert!(v.abs() < TOL, "index {i} should be 0");
        }
    }
}

#[test]
fn test_noise_operator_empty_input() {
    let result = noise_operator_fourier(&[], 0.5);
    assert!(result.is_empty());
}

// -----------------------------------------------------------------------
// Level-k weight tests
// -----------------------------------------------------------------------

#[test]
fn test_level_weight_constant_function() {
    // Constant function: all weight at level 0
    let f = BooleanFunction::constant(1.0, 3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let w0 = level_k_weight(&coeffs, 3, 0);
    assert!((w0 - 1.0).abs() < TOL, "constant: all weight at level 0");
    for k in 1..=3 {
        let wk = level_k_weight(&coeffs, 3, k);
        assert!(wk.abs() < TOL, "constant: zero weight at level {k}");
    }
}

#[test]
fn test_level_weight_dictator() {
    // Dictator x_0 on n=3: f_hat({0}) = 1, all others = 0
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let w0 = level_k_weight(&coeffs, 3, 0);
    assert!(w0.abs() < TOL, "dictator: no level-0 weight");
    let w1 = level_k_weight(&coeffs, 3, 1);
    assert!((w1 - 1.0).abs() < TOL, "dictator: all weight at level 1");
    for k in 2..=3 {
        let wk = level_k_weight(&coeffs, 3, k);
        assert!(wk.abs() < TOL, "dictator: zero weight at level {k}");
    }
}

#[test]
fn test_level_weight_parity() {
    // Parity on n=3: f_hat([n]) = 1, all others = 0 -> all weight at level n
    let f = BooleanFunction::parity(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    for k in 0..3 {
        let wk = level_k_weight(&coeffs, 3, k);
        assert!(wk.abs() < TOL, "parity: zero weight at level {k}");
    }
    let w3 = level_k_weight(&coeffs, 3, 3);
    assert!((w3 - 1.0).abs() < TOL, "parity: all weight at level n");
}

#[test]
fn test_level_weight_all_levels_sum_parseval() {
    // Sum of all level weights = E[f^2] (Parseval)
    let f = BooleanFunction::majority(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let total: f64 = (0..=3).map(|k| level_k_weight(&coeffs, 3, k)).sum();
    let energy: f64 = f.values().iter().map(|v| v * v).sum::<f64>() / 8.0;
    assert!(
        (total - energy).abs() < TOL,
        "sum of level weights = E[f^2]"
    );
}

#[test]
fn test_level_weight_beyond_n_returns_zero() {
    let coeffs = vec![1.0; 4]; // n=2
    let w5 = level_k_weight(&coeffs, 2, 5);
    assert!(w5.abs() < TOL, "k > n should return 0");
}

// -----------------------------------------------------------------------
// Hypercontractive norm tests
// -----------------------------------------------------------------------

#[test]
fn test_hypercontractive_norm_dictator_rho_one_q_two() {
    // ||T_1 f||_2 = ||f||_2 for dictator (Parseval)
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let norm = hypercontractive_norm(&coeffs, 3, 1.0, 2.0);
    let f2_norm = fourier_p_norm(&coeffs, 3, 2.0);
    assert!((norm - f2_norm).abs() < TOL, "||T_1 f||_2 = ||f||_2");
}

#[test]
fn test_hypercontractive_norm_constant() {
    // Constant function: T_rho c = c for any rho
    let f = BooleanFunction::constant(0.7, 2).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let norm = hypercontractive_norm(&coeffs, 2, 0.5, 4.0);
    assert!((norm - 0.7).abs() < TOL, "constant function norm = |c|");
}

#[test]
fn test_hypercontractive_norm_high_q() {
    // ||T_rho f||_q with large q converges to L-infinity norm of T_rho f
    let f = BooleanFunction::dictator(0, 2).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let norm_q100 = hypercontractive_norm(&coeffs, 2, 0.5, 100.0);
    // T_{0.5} dictator: dampened values are +-0.5
    // L-infinity should approach 0.5
    assert!(
        (norm_q100 - 0.5).abs() < 0.01,
        "high q norm approaches L-inf"
    );
}

#[test]
fn test_hypercontractive_norm_empty() {
    let norm = hypercontractive_norm(&[], 0, 0.5, 4.0);
    assert!(norm.abs() < TOL, "empty coefficients -> 0");
}

#[test]
fn test_hypercontractive_norm_q_below_one() {
    let norm = hypercontractive_norm(&[1.0], 0, 0.5, 0.5);
    assert!(norm.abs() < TOL, "q < 1 -> 0");
}

// -----------------------------------------------------------------------
// Bonami-Beckner verification tests
// -----------------------------------------------------------------------

#[test]
fn test_bonami_beckner_dictator_optimal_rho() {
    // Dictator with rho = 1/sqrt(3) should satisfy BB for q=4
    let f = BooleanFunction::dictator(0, 3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 3, rho),
        "BB should hold for dictator at optimal rho"
    );
}

#[test]
fn test_bonami_beckner_parity_optimal_rho() {
    // Parity function with optimal rho for q=4
    let f = BooleanFunction::parity(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 3, rho),
        "BB should hold for parity at optimal rho"
    );
}

#[test]
fn test_bonami_beckner_majority_optimal_rho() {
    // Majority function with optimal rho for q=4
    let f = BooleanFunction::majority(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 3, rho),
        "BB should hold for majority at optimal rho"
    );
}

#[test]
fn test_bonami_beckner_constant_any_rho() {
    // Constant function: T_rho c = c, so ||T_rho c||_q = |c| = ||c||_2
    let f = BooleanFunction::constant(1.0, 2).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    assert!(
        verify_bonami_beckner(&coeffs, 2, 0.99),
        "BB trivially holds for constants"
    );
}

#[test]
fn test_bonami_beckner_rho_zero() {
    // rho=0: T_0 f = E[f] (constant), always satisfies BB
    let f = BooleanFunction::and2(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    assert!(
        verify_bonami_beckner(&coeffs, 3, 0.0),
        "BB should hold at rho=0 (projection to mean)"
    );
}

#[test]
fn test_bonami_beckner_bound_ratio_at_optimal() {
    // The ratio ||T_rho f||_q / ||f||_2 should be <= 1 at optimal rho
    let f = BooleanFunction::dictator(0, 4).unwrap();
    let rho = optimal_rho_for_q(4.0);
    let ratio = bonami_beckner_bound(&f, rho, 4.0);
    assert!(
        ratio <= 1.0 + TOL,
        "BB ratio should be <= 1 at optimal rho, got {ratio}"
    );
}

#[test]
fn test_bonami_beckner_skewed_function() {
    // Skewed function: constant 0.8 for most inputs
    // All +1 except one entry -> nearly constant, BB should hold easily
    let mut table = vec![1.0; 8];
    table[0] = -1.0; // one -1 entry among 8
    let f = BooleanFunction::from_truth_table(&table).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 3, rho),
        "BB should hold for skewed function"
    );
}

// -----------------------------------------------------------------------
// Optimal rho tests
// -----------------------------------------------------------------------

#[test]
fn test_optimal_rho_q_two() {
    // rho = 1/sqrt(2-1) = 1
    let rho = optimal_rho_for_q(2.0);
    assert!((rho - 1.0).abs() < TOL, "q=2: rho = 1");
}

#[test]
fn test_optimal_rho_q_four() {
    // rho = 1/sqrt(3) ~ 0.5774
    let rho = optimal_rho_for_q(4.0);
    let expected = 1.0 / 3.0_f64.sqrt();
    assert!((rho - expected).abs() < TOL, "q=4: rho = 1/sqrt(3)");
}

#[test]
fn test_optimal_rho_q_ten() {
    // rho = 1/sqrt(9) = 1/3
    let rho = optimal_rho_for_q(10.0);
    assert!((rho - 1.0 / 3.0).abs() < TOL, "q=10: rho = 1/3");
}

#[test]
fn test_optimal_rho_large_q() {
    // As q -> infinity, rho -> 0
    let rho = optimal_rho_for_q(1000.0);
    assert!(rho < 0.04, "large q: rho should be small");
    assert!(rho > 0.0, "rho should be positive");
}

#[test]
fn test_optimal_rho_q_one_degenerate() {
    let rho = optimal_rho_for_q(1.0);
    assert!(rho.is_infinite(), "q=1 is degenerate -> infinity");
}

#[test]
fn test_optimal_rho_q_below_one() {
    let rho = optimal_rho_for_q(0.5);
    assert!(rho.is_infinite(), "q < 1 is degenerate -> infinity");
}

// -----------------------------------------------------------------------
// Edge case tests
// -----------------------------------------------------------------------

#[test]
fn test_level_weight_single_coefficient() {
    // n=0: single coefficient (the constant term)
    let coeffs = vec![0.75];
    let w0 = level_k_weight(&coeffs, 0, 0);
    assert!((w0 - 0.5625).abs() < TOL, "single coeff: W^0 = c^2");
}

#[test]
fn test_noise_operator_single_coefficient() {
    let coeffs = vec![3.0];
    let result = noise_operator_fourier(&coeffs, 0.5);
    assert_eq!(result.len(), 1);
    assert!((result[0] - 3.0).abs() < TOL, "level-0 unaffected by rho");
}

#[test]
fn test_fourier_p_norm_matches_two_norm_via_parseval() {
    // ||f||_2 via p-norm reconstruction should match Parseval: sqrt(sum c^2)
    let f = BooleanFunction::majority(3).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let p_norm = fourier_p_norm(&coeffs, 3, 2.0);
    let parseval: f64 = coeffs.iter().map(|c| c * c).sum::<f64>();
    assert!(
        (p_norm * p_norm - parseval).abs() < TOL,
        "||f||_2^2 should equal sum of f_hat(S)^2"
    );
}

#[test]
fn test_bonami_beckner_n_one_dictator() {
    // Smallest nontrivial case: n=1 dictator
    let f = BooleanFunction::dictator(0, 1).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 1, rho),
        "BB should hold for n=1 dictator"
    );
}

#[test]
fn test_bonami_beckner_larger_n() {
    // n=5 majority: verify BB still holds
    let f = BooleanFunction::majority(5).unwrap();
    let coeffs = compute_all_fourier(&f).unwrap();
    let rho = optimal_rho_for_q(4.0);
    assert!(
        verify_bonami_beckner(&coeffs, 5, rho),
        "BB should hold for n=5 majority"
    );
}

// -----------------------------------------------------------------------
// Proof status constant tests
// -----------------------------------------------------------------------

#[test]
fn test_s50_bonami_beckner_status() {
    assert_eq!(S50_BONAMI_BECKNER, ProofStatus::DerivedPending);
}

#[test]
fn test_s51_hypercontractive_norm_status() {
    assert_eq!(S51_HYPERCONTRACTIVE_NORM, ProofStatus::DerivedPending);
}
