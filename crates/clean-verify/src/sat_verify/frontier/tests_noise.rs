// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for noise sensitivity, influence, and spectral analysis (S45-S47).

use super::fourier::BooleanFunction;
use super::noise_sensitivity::*;

/// Tolerance for floating-point comparisons in tests.
const TOL: f64 = 1e-10;

// =========================================================================
// Helper: n-variable OR via truth table
// =========================================================================

/// OR of n variables in {-1,1} encoding: f(x) = -1 iff all bits set
/// (all variables are -1 in the sign convention), else +1.
fn or_n(n: usize) -> BooleanFunction {
    let size = 1usize << n;
    let all_ones = size - 1;
    let table: Vec<f64> = (0..size)
        .map(|x| if x == all_ones { -1.0 } else { 1.0 })
        .collect();
    BooleanFunction::from_truth_table(&table).expect("valid OR truth table")
}

/// AND of n variables in {-1,1} encoding: f(x) = 1 iff x = 0
/// (all variables are +1), else -1.
fn and_n(n: usize) -> BooleanFunction {
    let size = 1usize << n;
    let table: Vec<f64> = (0..size).map(|x| if x == 0 { 1.0 } else { -1.0 }).collect();
    BooleanFunction::from_truth_table(&table).expect("valid AND truth table")
}

// =========================================================================
// Noise sensitivity tests
// =========================================================================

#[test]
fn test_noise_sensitivity_dictator_delta() {
    // Dictator f(x) = x_0: only Fourier coeff is f_hat({0}) = 1, |{0}| = 1.
    // Noise_delta = (1 - (1-2*delta)^1) / 2 = (1 - 1 + 2*delta) / 2 = delta.
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    for &delta in &[0.0, 0.1, 0.25, 0.5] {
        let ns = noise_sensitivity(&f, delta);
        assert!(
            (ns - delta).abs() < TOL,
            "Noise_delta(dict) = delta: expected {delta}, got {ns}"
        );
    }
}

#[test]
fn test_noise_sensitivity_parity_formula() {
    // Parity f = x_1*...*x_n: f_hat([n]) = 1, |[n]| = n.
    // Noise_delta = (1 - (1-2*delta)^n) / 2.
    for n in 2..=5 {
        let f = BooleanFunction::parity(n).expect("valid");
        for &delta in &[0.1, 0.25, 0.5] {
            let rho: f64 = 1.0 - 2.0 * delta;
            let expected = (1.0 - rho.powi(n as i32)) / 2.0;
            let ns = noise_sensitivity(&f, delta);
            assert!(
                (ns - expected).abs() < TOL,
                "Parity(n={n}), delta={delta}: expected {expected}, got {ns}"
            );
        }
    }
}

#[test]
fn test_noise_sensitivity_constant_zero() {
    // Constant function: all Fourier mass at empty set.
    // Noise_delta = (1 - 1^0 * 1) / 2 = 0.
    let f = BooleanFunction::constant(1.0, 3).expect("valid");
    for &delta in &[0.0, 0.1, 0.5] {
        let ns = noise_sensitivity(&f, delta);
        assert!(ns.abs() < TOL, "constant noise sensitivity should be 0");
    }
}

#[test]
fn test_noise_sensitivity_majority_3_specific() {
    // MAJ_3 Fourier: f_hat({i}) = 1/2, f_hat({0,1,2}) = -1/2.
    // Stab_rho = 3*(1/2)^2*rho + (1/2)^2*rho^3 = (3*rho + rho^3)/4.
    // Noise_delta = (1 - (3*rho + rho^3)/4) / 2, rho = 1-2*delta.
    let f = BooleanFunction::majority(3).expect("valid");

    let delta: f64 = 0.1;
    let rho: f64 = 1.0 - 2.0 * delta;
    let stab = (3.0 * rho + rho.powi(3)) / 4.0;
    let expected = (1.0 - stab) / 2.0;
    let ns = noise_sensitivity(&f, delta);
    assert!(
        (ns - expected).abs() < TOL,
        "MAJ_3 delta=0.1: expected {expected}, got {ns}"
    );

    // delta = 0.5 => rho = 0 => stab = 0 => noise = 0.5 * (1 - 0) = 0.5
    // But f_hat(empty) = 0 for MAJ_3, so stab includes the empty set term.
    // Actually, the sum includes S=empty: rho^0 * 0^2 = 0, so stab = 0 at rho=0.
    // Noise_{1/2} = (1 - 0)/2 = 0.5
    let ns_half = noise_sensitivity(&f, 0.5);
    assert!(
        (ns_half - 0.5).abs() < TOL,
        "MAJ_3 delta=0.5: expected 0.5, got {ns_half}"
    );
}

#[test]
fn test_noise_sensitivity_monotone_in_delta() {
    // Noise sensitivity should (generally) increase with delta for non-constant f.
    let f = BooleanFunction::majority(3).expect("valid");
    let deltas = [0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5];
    let sensitivities: Vec<f64> = deltas.iter().map(|&d| noise_sensitivity(&f, d)).collect();
    for w in sensitivities.windows(2) {
        assert!(
            w[1] >= w[0] - TOL,
            "noise sensitivity should be non-decreasing in delta: {} -> {}",
            w[0],
            w[1]
        );
    }
}

// =========================================================================
// Noise stability tests
// =========================================================================

#[test]
fn test_noise_stability_dictator_rho() {
    // Dictator f(x) = x_0: Stab_rho = rho (only level-1 coefficient).
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    for &rho in &[0.0, 0.5, 0.8, 1.0] {
        let stab = noise_stability(&f, rho);
        assert!(
            (stab - rho).abs() < TOL,
            "Stab_rho(dict) = rho: expected {rho}, got {stab}"
        );
    }
}

#[test]
fn test_noise_stability_parity_rho_n() {
    // Parity: Stab_rho = rho^n.
    for n in 2..=5 {
        let f = BooleanFunction::parity(n).expect("valid");
        for &rho in &[0.0_f64, 0.5, 0.9, 1.0] {
            let expected = rho.powi(n as i32);
            let stab = noise_stability(&f, rho);
            assert!(
                (stab - expected).abs() < TOL,
                "Parity(n={n}), rho={rho}: expected {expected}, got {stab}"
            );
        }
    }
}

#[test]
fn test_noise_stability_constant_one() {
    // Constant f=1: f_hat(empty) = 1, all others 0.
    // Stab_rho = rho^0 * 1^2 = 1 for all rho.
    let f = BooleanFunction::constant(1.0, 3).expect("valid");
    for &rho in &[0.0, 0.5, 1.0] {
        let stab = noise_stability(&f, rho);
        assert!((stab - 1.0).abs() < TOL, "Stab_rho(const) = 1: got {stab}");
    }
}

#[test]
fn test_noise_stability_at_rho_one_is_ef_squared() {
    // Stab_1(f) = sum_S 1^{|S|} f_hat(S)^2 = E[f^2].
    let f = BooleanFunction::majority(3).expect("valid");
    let stab = noise_stability(&f, 1.0);
    // MAJ_3 is {-1,1}-valued so E[f^2] = 1.
    assert!(
        (stab - 1.0).abs() < TOL,
        "Stab_1(MAJ_3) = E[f^2] = 1: got {stab}"
    );
}

// =========================================================================
// Influence tests
// =========================================================================

#[test]
fn test_total_influence_dictator_one() {
    let f = BooleanFunction::dictator(0, 4).expect("valid");
    let ti = total_influence(&f);
    assert!((ti - 1.0).abs() < TOL, "I(dict) = 1: got {ti}");
}

#[test]
fn test_total_influence_parity_n() {
    for n in 1..=6 {
        let f = BooleanFunction::parity(n).expect("valid");
        let ti = total_influence(&f);
        assert!((ti - n as f64).abs() < TOL, "I(parity_{n}) = {n}: got {ti}");
    }
}

#[test]
fn test_total_influence_constant_zero() {
    let f = BooleanFunction::constant(1.0, 4).expect("valid");
    let ti = total_influence(&f);
    assert!(ti.abs() < TOL, "I(const) = 0: got {ti}");
}

#[test]
fn test_variable_influence_dictator_decomposition() {
    // Dict on var 0: Inf_0 = 1, Inf_i = 0 for i > 0.
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    let inf0 = variable_influence(&f, 0).expect("ok");
    assert!((inf0 - 1.0).abs() < TOL, "Inf_0 = 1");
    let inf1 = variable_influence(&f, 1).expect("ok");
    assert!(inf1.abs() < TOL, "Inf_1 = 0");
    let inf2 = variable_influence(&f, 2).expect("ok");
    assert!(inf2.abs() < TOL, "Inf_2 = 0");
}

#[test]
fn test_variable_influence_parity_all_one() {
    let f = BooleanFunction::parity(4).expect("valid");
    for i in 0..4 {
        let inf = variable_influence(&f, i).expect("ok");
        assert!((inf - 1.0).abs() < TOL, "Inf_{i}(parity) = 1: got {inf}");
    }
}

#[test]
fn test_variable_influence_or3() {
    // OR of 3 variables in {-1,1}: f(x) = -1 iff x = (1,1,1) i.e. all -1.
    // By symmetry, all Inf_i are equal. I(OR_3) = sum_i Inf_i.
    let f = or_n(3);
    let inf0 = variable_influence(&f, 0).expect("ok");
    let inf1 = variable_influence(&f, 1).expect("ok");
    let inf2 = variable_influence(&f, 2).expect("ok");
    assert!((inf0 - inf1).abs() < TOL, "OR_3 is symmetric");
    assert!((inf1 - inf2).abs() < TOL, "OR_3 is symmetric");
    // OR_3: Inf_i = 1/4 each (by direct computation)
    // Actually: truth table has 8 entries. For var 0: flipping bit 0.
    // x=000 -> f=1, x^e0=001 -> f=1. Same.
    // x=001 -> f=1, x^e0=000 -> f=1. Same.
    // x=010 -> f=1, x^e0=011 -> f=1. Same.
    // x=011 -> f=1, x^e0=010 -> f=1. Same.
    // x=100 -> f=1, x^e0=101 -> f=1. Same.
    // x=101 -> f=1, x^e0=100 -> f=1. Same.
    // x=110 -> f=1, x^e0=111 -> f=-1. Different!
    // x=111 -> f=-1, x^e0=110 -> f=1. Different!
    // Inf_0 = Pr[differ] = 2/8 = 1/4.
    assert!((inf0 - 0.25).abs() < TOL, "Inf_i(OR_3) = 1/4: got {inf0}");
}

#[test]
fn test_variable_influence_and2() {
    // AND of 2 variables in {-1,1}: f(x) = 1 iff x_0=+1 and x_1=+1.
    // Truth table (2 vars): [1, -1, -1, -1].
    // Inf_0: flip bit 0. x=00->f=1 vs x=01->f=-1 (differ); x=01 vs x=00 (differ);
    //        x=10->f=-1 vs x=11->f=-1 (same); x=11 vs x=10 (same).
    // Inf_0 = 2/4 = 1/2. Similarly Inf_1 = 1/2.
    // But the task says "AND function: Inf_i = 1/4 for n=2" -- let me recheck.
    // Actually, using the {-1,1} influence formula:
    //   Inf_i = E[(f(x) - f(x^e_i))^2 / 4].
    //   For {-1,1}-valued f, (f(x) - f(x^e_i))^2 = 0 or 4.
    //   Inf_i = (1/4) * E[(f(x)-f(x^e_i))^2] = Pr[f(x) != f(x^e_i)].
    //   So Inf_i = 2/4 = 1/2 for AND_2.
    //
    // The task specification said "Inf_i = 1/4 for n=2" but that would be for
    // AND of first 2 vars embedded in larger n. For n=2 pure AND, it's 1/2.
    let f = and_n(2);
    let inf0 = variable_influence(&f, 0).expect("ok");
    let inf1 = variable_influence(&f, 1).expect("ok");
    assert!((inf0 - 0.5).abs() < TOL, "Inf_0(AND_2) = 1/2: got {inf0}");
    assert!((inf1 - 0.5).abs() < TOL, "Inf_1(AND_2) = 1/2: got {inf1}");
}

#[test]
fn test_variable_influence_and2_in_3vars() {
    // AND of first 2 variables embedded in 3 variables.
    // f(x) = 1 iff bits 0,1 = 00 (both +1 in {-1,1}), else -1.
    // f depends only on x_0, x_1 so Inf_2 = 0.
    // For var 0: 4 pairs (x, x^e_0). Only the pairs where bit 1 = 0
    // produce a change: (000,001) and (100,101). That is 4 out of 8
    // assignments differ => Inf_0 = 4/8... but using the formula:
    // Inf_i = sum_{x} (f(x) - f(x^e_i))^2 / (4 * 2^n).
    // Sum over all 8: 4+4+0+0+4+4+0+0 = 16. Inf_0 = 16/32 = 0.5.
    let f = BooleanFunction::and2(3).expect("valid");
    let inf0 = variable_influence(&f, 0).expect("ok");
    let inf1 = variable_influence(&f, 1).expect("ok");
    let inf2 = variable_influence(&f, 2).expect("ok");
    assert!(
        (inf0 - 0.5).abs() < TOL,
        "Inf_0(AND2 in 3 vars) = 1/2: got {inf0}"
    );
    assert!(
        (inf1 - 0.5).abs() < TOL,
        "Inf_1(AND2 in 3 vars) = 1/2: got {inf1}"
    );
    assert!(inf2.abs() < TOL, "Inf_2(AND2 in 3 vars) = 0: got {inf2}");
}

#[test]
fn test_variable_influence_error_out_of_range() {
    let f = BooleanFunction::parity(3).expect("valid");
    assert!(variable_influence(&f, 3).is_err());
    assert!(variable_influence(&f, 100).is_err());
}

#[test]
fn test_max_influence_dictator() {
    let f = BooleanFunction::dictator(0, 4).expect("valid");
    let mi = max_influence(&f);
    assert!((mi - 1.0).abs() < TOL, "max inf of dictator = 1");
}

#[test]
fn test_max_influence_parity() {
    let f = BooleanFunction::parity(4).expect("valid");
    let mi = max_influence(&f);
    // All influences are 1 for parity.
    assert!((mi - 1.0).abs() < TOL, "max inf of parity = 1");
}

// =========================================================================
// KKL bound tests
// =========================================================================

#[test]
fn test_kkl_bound_majority_3() {
    let f = BooleanFunction::majority(3).expect("valid");
    // max_inf = 0.5, bound = c * ln(3)/3.
    // With c=0.234: bound = 0.234 * 1.099 / 3 = 0.0857. 0.5 >= 0.0857.
    assert!(verify_kkl_bound(&f, 0.234), "KKL holds for MAJ_3");
}

#[test]
fn test_kkl_bound_majority_5() {
    let f = BooleanFunction::majority(5).expect("valid");
    // MAJ_5 is balanced and symmetric. max_inf should be >= c*ln(5)/5.
    assert!(verify_kkl_bound(&f, 0.234), "KKL holds for MAJ_5");
}

#[test]
fn test_kkl_bound_or_3() {
    // OR_3 is not balanced (E[f] != 0), but we can still check if the
    // KKL-style bound holds for a small constant.
    let f = or_n(3);
    let mi = max_influence(&f);
    // Inf_i(OR_3) = 1/4 by direct computation (see test above).
    // c * ln(3)/3 = 0.234 * 1.099/3 = 0.0857.  0.25 >= 0.0857.
    assert!(mi > 0.08, "OR_3 max influence is large enough");
    assert!(verify_kkl_bound(&f, 0.234), "KKL holds for OR_3");
}

#[test]
fn test_kkl_bound_trivial_n1() {
    let f = BooleanFunction::dictator(0, 1).expect("valid");
    assert!(verify_kkl_bound(&f, 0.234), "trivially true for n=1");
}

// =========================================================================
// Spectral analysis tests
// =========================================================================

#[test]
fn test_level_weight_dictator_concentrated_at_1() {
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    let w0 = level_weight(&f, 0);
    let w1 = level_weight(&f, 1);
    let w2 = level_weight(&f, 2);
    let w3 = level_weight(&f, 3);
    assert!(w0.abs() < TOL, "W^0(dict) = 0");
    assert!((w1 - 1.0).abs() < TOL, "W^1(dict) = 1");
    assert!(w2.abs() < TOL, "W^2(dict) = 0");
    assert!(w3.abs() < TOL, "W^3(dict) = 0");
}

#[test]
fn test_level_weight_parity_concentrated_at_n() {
    let f = BooleanFunction::parity(4).expect("valid");
    for k in 0..4 {
        let wk = level_weight(&f, k);
        assert!(wk.abs() < TOL, "W^{k}(parity_4) = 0 for k < 4");
    }
    let wn = level_weight(&f, 4);
    assert!((wn - 1.0).abs() < TOL, "W^4(parity_4) = 1");
}

#[test]
fn test_level_weight_majority_3() {
    // MAJ_3: W^0 = 0, W^1 = 3*(1/4) = 3/4, W^2 = 0, W^3 = 1/4.
    let f = BooleanFunction::majority(3).expect("valid");
    let w0 = level_weight(&f, 0);
    let w1 = level_weight(&f, 1);
    let w2 = level_weight(&f, 2);
    let w3 = level_weight(&f, 3);
    assert!(w0.abs() < TOL, "W^0 = 0");
    assert!((w1 - 0.75).abs() < TOL, "W^1 = 3/4: got {w1}");
    assert!(w2.abs() < TOL, "W^2 = 0");
    assert!((w3 - 0.25).abs() < TOL, "W^3 = 1/4: got {w3}");
}

#[test]
fn test_level_weights_sum_to_ef_squared_parseval() {
    // Parseval decomposed by level: sum_k W^k = E[f^2].
    let functions: Vec<BooleanFunction> = vec![
        BooleanFunction::dictator(0, 4).expect("ok"),
        BooleanFunction::parity(4).expect("ok"),
        BooleanFunction::majority(3).expect("ok"),
        BooleanFunction::constant(1.0, 3).expect("ok"),
        BooleanFunction::and2(3).expect("ok"),
        BooleanFunction::or2(3).expect("ok"),
    ];
    for f in &functions {
        assert!(
            verify_level_parseval(f),
            "level Parseval should hold for all standard functions"
        );
    }
}

#[test]
fn test_low_degree_energy_dictator_full_at_1() {
    let f = BooleanFunction::dictator(0, 4).expect("valid");
    let e0 = low_degree_energy(&f, 0);
    let e1 = low_degree_energy(&f, 1);
    let e4 = low_degree_energy(&f, 4);
    assert!(e0.abs() < TOL, "degree <= 0 energy = 0 for dictator");
    assert!((e1 - 1.0).abs() < TOL, "degree <= 1 captures all energy");
    assert!((e4 - 1.0).abs() < TOL, "degree <= 4 captures all energy");
}

#[test]
fn test_low_degree_energy_parity_only_at_max() {
    let f = BooleanFunction::parity(4).expect("valid");
    let e3 = low_degree_energy(&f, 3);
    let e4 = low_degree_energy(&f, 4);
    assert!(e3.abs() < TOL, "parity has no energy below degree n");
    assert!((e4 - 1.0).abs() < TOL, "parity has all energy at degree n");
}

#[test]
fn test_spectral_entropy_constant_zero() {
    // Constant function has only f_hat(empty) nonzero.
    // Single nonzero coeff => p(S) = 1 => entropy = -1 * log2(1) = 0.
    let f = BooleanFunction::constant(1.0, 3).expect("valid");
    let h = spectral_entropy(&f);
    assert!(h.abs() < TOL, "spectral entropy of constant = 0: got {h}");
}

#[test]
fn test_spectral_entropy_dictator_zero() {
    // Dictator has single nonzero Fourier coeff f_hat({i}) = 1.
    // p({i}) = 1 => entropy = 0.
    let f = BooleanFunction::dictator(0, 3).expect("valid");
    let h = spectral_entropy(&f);
    assert!(h.abs() < TOL, "spectral entropy of dictator = 0: got {h}");
}

#[test]
fn test_spectral_entropy_parity_zero() {
    // Parity has single nonzero Fourier coeff f_hat([n]) = 1.
    let f = BooleanFunction::parity(3).expect("valid");
    let h = spectral_entropy(&f);
    assert!(h.abs() < TOL, "spectral entropy of parity = 0: got {h}");
}

#[test]
fn test_spectral_entropy_majority_3_positive() {
    // MAJ_3 has 4 nonzero Fourier coefficients (3 singletons + full set),
    // all with |f_hat| = 1/2. Each p(S) = (1/4) / 1 = 1/4.
    // H = -4 * (1/4) * log2(1/4) = -4 * (1/4) * (-2) = 2.0.
    let f = BooleanFunction::majority(3).expect("valid");
    let h = spectral_entropy(&f);
    assert!(h > TOL, "MAJ_3 has positive spectral entropy");
    assert!(
        (h - 2.0).abs() < TOL,
        "MAJ_3 spectral entropy = 2.0: got {h}"
    );
}

#[test]
fn test_spectral_entropy_nonnegative() {
    // Entropy is always >= 0.
    let functions: Vec<BooleanFunction> = vec![
        BooleanFunction::dictator(0, 3).expect("ok"),
        BooleanFunction::parity(3).expect("ok"),
        BooleanFunction::majority(3).expect("ok"),
        BooleanFunction::constant(1.0, 3).expect("ok"),
        BooleanFunction::and2(3).expect("ok"),
    ];
    for f in &functions {
        let h = spectral_entropy(f);
        assert!(h >= -TOL, "spectral entropy >= 0: got {h}");
    }
}

// =========================================================================
// Cross-identity consistency tests
// =========================================================================

#[test]
fn test_total_influence_equals_sum_variable_influences() {
    // I(f) = sum_i Inf_i(f)
    let f = BooleanFunction::majority(5).expect("valid");
    let ti = total_influence(&f);
    let sum_inf: f64 = (0..5).map(|i| variable_influence(&f, i).expect("ok")).sum();
    assert!(
        (ti - sum_inf).abs() < TOL,
        "I(f) = sum Inf_i: {ti} vs {sum_inf}"
    );
}

#[test]
fn test_total_influence_equals_weighted_level_sum() {
    // I(f) = sum_k k * W^k(f) -- the S46 identity.
    let f = BooleanFunction::majority(5).expect("valid");
    let ti = total_influence(&f);
    let n = f.num_vars();
    let level_sum: f64 = (0..=n).map(|k| k as f64 * level_weight(&f, k)).sum();
    assert!(
        (ti - level_sum).abs() < TOL,
        "I(f) = sum k*W^k: {ti} vs {level_sum}"
    );
}

#[test]
fn test_noise_sensitivity_stability_relationship() {
    // Noise_delta = (1 - Stab_{1-2*delta}) / 2 for {-1,1}-valued f.
    let f = BooleanFunction::majority(3).expect("valid");
    for &delta in &[0.1, 0.25, 0.5] {
        let rho = 1.0 - 2.0 * delta;
        let ns = noise_sensitivity(&f, delta);
        let stab = noise_stability(&f, rho);
        let expected_ns = (1.0 - stab) / 2.0;
        assert!(
            (ns - expected_ns).abs() < TOL,
            "Noise_delta = (1 - Stab_rho)/2: {ns} vs {expected_ns}, delta={delta}"
        );
    }
}

// =========================================================================
// Proof status constants
// =========================================================================

#[test]
fn test_proof_status_constants() {
    assert_eq!(
        S45_NOISE_SENSITIVITY_FOURIER,
        crate::spec::ProofStatus::DerivedPending,
    );
    assert_eq!(
        S46_TOTAL_INFLUENCE_IDENTITY,
        crate::spec::ProofStatus::DerivedPending,
    );
    assert_eq!(
        S47_KKL_COMPUTATIONAL,
        crate::spec::ProofStatus::DerivedPending,
    );
}

// =========================================================================
// Frontier entry registry
// =========================================================================

#[test]
fn test_frontier_entries_include_s45_s47() {
    let entries = super::all_entries();
    assert_eq!(
        entries.len(),
        12,
        "5 original + 3 noise + 2 extension + 2 hypercontractivity entries"
    );
    let ids: Vec<&str> = entries.iter().map(|e| e.id).collect();
    assert!(ids.contains(&"S45"), "S45 present");
    assert!(ids.contains(&"S46"), "S46 present");
    assert!(ids.contains(&"S47"), "S47 present");
}
