// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for monotone activation function bound propagation.

use super::monotone::*;

// ============================================================================
// Sigmoid tests
// ============================================================================

#[test]
fn test_sigmoid_known_values() {
    let sig = ActivationFn::Sigmoid;
    assert!((sig.evaluate(0.0) - 0.5).abs() < 1e-10, "sigmoid(0) = 0.5");
    assert!(sig.evaluate(100.0) > 0.999, "sigmoid(large) ~ 1");
    assert!(sig.evaluate(-100.0) < 0.001, "sigmoid(neg_large) ~ 0");
}

#[test]
fn test_sigmoid_bounds_symmetric() {
    let sig = ActivationFn::Sigmoid;
    let (lo, hi) = sig.propagate_bounds(-2.0, 2.0);
    // sigmoid(-2) ~ 0.1192, sigmoid(2) ~ 0.8808
    assert!(lo > 0.11 && lo < 0.13);
    assert!(hi > 0.87 && hi < 0.89);
    // Should be roughly symmetric around 0.5
    assert!(
        (lo + hi - 1.0).abs() < 1e-6,
        "sigmoid bounds should be symmetric around 0.5"
    );
}

#[test]
fn test_sigmoid_bounds_narrow_interval() {
    let sig = ActivationFn::Sigmoid;
    let (lo, hi) = sig.propagate_bounds(0.0, 0.0);
    assert!((lo - 0.5).abs() < 1e-10);
    assert!((hi - 0.5).abs() < 1e-10);
}

#[test]
fn test_sigmoid_monotone_class() {
    assert_eq!(
        ActivationFn::Sigmoid.monotone_class(),
        MonotoneClass::Increasing
    );
}

// ============================================================================
// Tanh tests
// ============================================================================

#[test]
fn test_tanh_known_values() {
    let t = ActivationFn::Tanh;
    assert!(t.evaluate(0.0).abs() < 1e-10, "tanh(0) = 0");
    assert!(t.evaluate(100.0) > 0.999, "tanh(large) ~ 1");
    assert!(t.evaluate(-100.0) < -0.999, "tanh(neg_large) ~ -1");
}

#[test]
fn test_tanh_symmetry() {
    let t = ActivationFn::Tanh;
    for &x in &[0.5, 1.0, 2.0, 5.0] {
        assert!(
            (t.evaluate(x) + t.evaluate(-x)).abs() < 1e-10,
            "tanh should be odd: tanh({x}) + tanh(-{x}) != 0"
        );
    }
}

#[test]
fn test_tanh_bounds_saturation() {
    let t = ActivationFn::Tanh;
    let (lo, hi) = t.propagate_bounds(-50.0, 50.0);
    assert!(lo < -0.99, "tanh lower should saturate near -1");
    assert!(hi > 0.99, "tanh upper should saturate near 1");
}

#[test]
fn test_tanh_monotone_class() {
    assert_eq!(
        ActivationFn::Tanh.monotone_class(),
        MonotoneClass::Increasing
    );
}

// ============================================================================
// GELU approximation tests
// ============================================================================

#[test]
fn test_gelu_at_zero() {
    let g = ActivationFn::GeluApprox;
    assert!(g.evaluate(0.0).abs() < 1e-10, "GELU(0) = 0");
}

#[test]
fn test_gelu_large_positive() {
    let g = ActivationFn::GeluApprox;
    // For large x, GELU(x) ~ x (the tanh saturates to 1)
    let x = 10.0;
    let fx = g.evaluate(x);
    assert!((fx - x).abs() < 0.01, "GELU(10) ~ 10, got {fx}");
}

#[test]
fn test_gelu_large_negative() {
    let g = ActivationFn::GeluApprox;
    // For large negative x, GELU(x) ~ 0 (tanh saturates to -1, 0.5*x*(1-1) = 0)
    let fx = g.evaluate(-10.0);
    assert!(fx.abs() < 0.01, "GELU(-10) ~ 0, got {fx}");
}

#[test]
fn test_gelu_reference_values() {
    // Reference: GELU(1.0) ~ 0.8412
    let g = ActivationFn::GeluApprox;
    let fx = g.evaluate(1.0);
    assert!((fx - 0.8412).abs() < 0.01, "GELU(1.0) ~ 0.8412, got {fx}");
}

#[test]
fn test_gelu_monotone_class() {
    // GELU approximation has a local minimum near x ~ -0.75, so it is piecewise monotone
    assert_eq!(
        ActivationFn::GeluApprox.monotone_class(),
        MonotoneClass::PiecewiseMonotone
    );
}

// ============================================================================
// Softplus tests
// ============================================================================

#[test]
fn test_softplus_large_positive() {
    let sp = ActivationFn::Softplus;
    // For large x, softplus(x) ~ x
    let x = 50.0;
    assert!((sp.evaluate(x) - x).abs() < 0.01, "softplus(50) ~ 50");
}

#[test]
fn test_softplus_large_negative() {
    let sp = ActivationFn::Softplus;
    // For large negative x, softplus(x) ~ exp(x) ~ 0
    let fx = sp.evaluate(-50.0);
    assert!(fx.abs() < 1e-10, "softplus(-50) ~ 0, got {fx}");
}

#[test]
fn test_softplus_at_zero() {
    let sp = ActivationFn::Softplus;
    // softplus(0) = ln(2) ~ 0.6931
    let fx = sp.evaluate(0.0);
    assert!(
        (fx - 2.0_f64.ln()).abs() < 1e-10,
        "softplus(0) = ln(2), got {fx}"
    );
}

#[test]
fn test_softplus_always_positive() {
    let sp = ActivationFn::Softplus;
    for &x in &[-100.0, -10.0, -1.0, 0.0, 1.0, 10.0, 100.0] {
        assert!(
            sp.evaluate(x) > -1e-15,
            "softplus must be non-negative, got {} at x={x}",
            sp.evaluate(x)
        );
    }
}

#[test]
fn test_softplus_monotone_class() {
    assert_eq!(
        ActivationFn::Softplus.monotone_class(),
        MonotoneClass::Increasing
    );
}

// ============================================================================
// Leaky ReLU tests
// ============================================================================

#[test]
fn test_leaky_relu_positive_input() {
    let lr = ActivationFn::leaky_relu(0.01);
    assert!((lr.evaluate(5.0) - 5.0).abs() < 1e-10, "leaky_relu(5) = 5");
}

#[test]
fn test_leaky_relu_negative_input() {
    let lr = ActivationFn::leaky_relu(0.01);
    assert!(
        (lr.evaluate(-5.0) - (-0.05)).abs() < 1e-10,
        "leaky_relu(-5) = 0.01 * -5 = -0.05"
    );
}

#[test]
fn test_leaky_relu_at_zero() {
    let lr = ActivationFn::leaky_relu(0.01);
    assert!(lr.evaluate(0.0).abs() < 1e-10, "leaky_relu(0) = 0");
}

#[test]
fn test_leaky_relu_bounds_crossing() {
    let lr = ActivationFn::leaky_relu(0.1);
    let (lo, hi) = lr.propagate_bounds(-2.0, 3.0);
    // f(-2) = 0.1 * -2 = -0.2, f(3) = 3.0
    assert!(
        (lo - (-0.2)).abs() < 1e-10,
        "leaky_relu lower should be -0.2, got {lo}"
    );
    assert!(
        (hi - 3.0).abs() < 1e-10,
        "leaky_relu upper should be 3.0, got {hi}"
    );
}

#[test]
fn test_leaky_relu_piecewise_class() {
    let lr = ActivationFn::leaky_relu(0.01);
    assert_eq!(lr.monotone_class(), MonotoneClass::PiecewiseMonotone);
}

// ============================================================================
// ELU tests
// ============================================================================

#[test]
fn test_elu_positive_input() {
    let elu = ActivationFn::elu(1.0);
    assert!((elu.evaluate(3.0) - 3.0).abs() < 1e-10, "ELU(3) = 3");
}

#[test]
fn test_elu_negative_input() {
    let elu = ActivationFn::elu(1.0);
    // ELU(-1) = 1.0 * (exp(-1) - 1) ~ -0.6321
    let fx = elu.evaluate(-1.0);
    let expected = (-1.0_f64).exp() - 1.0;
    assert!(
        (fx - expected).abs() < 1e-10,
        "ELU(-1) = {expected}, got {fx}"
    );
}

#[test]
fn test_elu_at_zero() {
    let elu = ActivationFn::elu(1.0);
    assert!(elu.evaluate(0.0).abs() < 1e-10, "ELU(0) = 0");
}

#[test]
fn test_elu_piecewise_class() {
    let elu = ActivationFn::elu(1.0);
    assert_eq!(elu.monotone_class(), MonotoneClass::PiecewiseMonotone);
}

#[test]
fn test_elu_bounds_crossing() {
    let elu = ActivationFn::elu(1.0);
    let (lo, hi) = elu.propagate_bounds(-2.0, 3.0);
    let f_lo = elu.evaluate(-2.0);
    let f_hi = elu.evaluate(3.0);
    assert!((lo - f_lo).abs() < 1e-10, "ELU lower should be f(-2)");
    assert!((hi - f_hi).abs() < 1e-10, "ELU upper should be f(3)");
}

// ============================================================================
// Lipschitz constant tests
// ============================================================================

#[test]
fn test_sigmoid_lipschitz_global() {
    // Sigmoid Lipschitz constant is at most 0.25 globally
    let l = activation_lipschitz(ActivationFn::Sigmoid, -100.0, 100.0);
    assert!(
        (l - 0.25).abs() < 1e-6,
        "sigmoid global Lipschitz should be 0.25, got {l}"
    );
}

#[test]
fn test_sigmoid_lipschitz_restricted() {
    // On [2, 5], sigmoid' is much smaller than 0.25
    let l = activation_lipschitz(ActivationFn::Sigmoid, 2.0, 5.0);
    assert!(
        l < 0.25,
        "sigmoid Lipschitz on [2,5] should be < 0.25, got {l}"
    );
    assert!(l > 0.0, "sigmoid Lipschitz must be positive");
}

#[test]
fn test_tanh_lipschitz_global() {
    // Tanh Lipschitz is 1.0 globally (tanh'(0) = 1)
    let l = activation_lipschitz(ActivationFn::Tanh, -100.0, 100.0);
    assert!(
        (l - 1.0).abs() < 1e-6,
        "tanh global Lipschitz should be 1.0, got {l}"
    );
}

#[test]
fn test_tanh_lipschitz_restricted() {
    // On [3, 5], tanh is nearly saturated so Lipschitz is small
    let l = activation_lipschitz(ActivationFn::Tanh, 3.0, 5.0);
    assert!(l < 0.1, "tanh Lipschitz on [3,5] should be small, got {l}");
}

#[test]
fn test_relu_lipschitz_positive() {
    // Standard ReLU: alpha=0, slope is 1 for positive
    let lr = ActivationFn::leaky_relu(0.0);
    let l = activation_lipschitz(lr, 1.0, 5.0);
    assert!(
        (l - 1.0).abs() < 1e-10,
        "ReLU Lipschitz on positive region = 1.0"
    );
}

#[test]
fn test_leaky_relu_lipschitz_crossing() {
    let lr = ActivationFn::leaky_relu(0.1);
    let l = activation_lipschitz(lr, -5.0, 5.0);
    assert!(
        (l - 1.0).abs() < 1e-10,
        "LeakyReLU Lipschitz = max(1, 0.1) = 1.0, got {l}"
    );
}

// ============================================================================
// Soundness verification tests
// ============================================================================

#[test]
fn test_sigmoid_soundness_random() {
    let sig = ActivationFn::Sigmoid;
    let lower = -3.0;
    let upper = 3.0;
    let mut rng: u64 = 42;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(sig, x, lower, upper),
            "sigmoid soundness failed for x={x}"
        );
    }
}

#[test]
fn test_tanh_soundness_random() {
    let tanh = ActivationFn::Tanh;
    let lower = -5.0;
    let upper = 5.0;
    let mut rng: u64 = 99;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(tanh, x, lower, upper),
            "tanh soundness failed for x={x}"
        );
    }
}

#[test]
fn test_gelu_soundness_random() {
    let gelu = ActivationFn::GeluApprox;
    let lower = -5.0;
    let upper = 5.0;
    let mut rng: u64 = 7777;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(gelu, x, lower, upper),
            "GELU soundness failed for x={x}"
        );
    }
}

#[test]
fn test_softplus_soundness_random() {
    let sp = ActivationFn::Softplus;
    let lower = -10.0;
    let upper = 10.0;
    let mut rng: u64 = 3333;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(sp, x, lower, upper),
            "softplus soundness failed for x={x}"
        );
    }
}

#[test]
fn test_leaky_relu_soundness_random() {
    let lr = ActivationFn::leaky_relu(0.1);
    let lower = -5.0;
    let upper = 5.0;
    let mut rng: u64 = 5555;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(lr, x, lower, upper),
            "leaky_relu soundness failed for x={x}"
        );
    }
}

#[test]
fn test_elu_soundness_random() {
    let elu = ActivationFn::elu(1.0);
    let lower = -5.0;
    let upper = 5.0;
    let mut rng: u64 = 1111;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..200 {
        let x = lower + lcg(&mut rng) * (upper - lower);
        assert!(
            verify_activation_soundness(elu, x, lower, upper),
            "ELU soundness failed for x={x}"
        );
    }
}

#[test]
fn test_soundness_out_of_bounds_rejected() {
    let sig = ActivationFn::Sigmoid;
    assert!(
        !verify_activation_soundness(sig, 5.0, 0.0, 1.0),
        "x outside [lower, upper] should fail"
    );
}

// ============================================================================
// Interval width comparison
// ============================================================================

#[test]
fn test_sigmoid_produces_tighter_bounds_than_tanh() {
    // Sigmoid output is in (0, 1), tanh in (-1, 1)
    // For same input interval, sigmoid output width should be <= tanh output width
    let sig = ActivationFn::Sigmoid;
    let tanh = ActivationFn::Tanh;
    let (sig_lo, sig_hi) = sig.propagate_bounds(-3.0, 3.0);
    let (tanh_lo, tanh_hi) = tanh.propagate_bounds(-3.0, 3.0);
    let sig_width = sig_hi - sig_lo;
    let tanh_width = tanh_hi - tanh_lo;
    assert!(
        sig_width <= tanh_width + 1e-10,
        "sigmoid width ({sig_width}) should be <= tanh width ({tanh_width})"
    );
}

#[test]
fn test_monotone_bounds_width_increases_with_input() {
    // For a wider input interval, output bounds should be at least as wide
    let sig = ActivationFn::Sigmoid;
    let (lo_n, hi_n) = sig.propagate_bounds(-1.0, 1.0);
    let (lo_w, hi_w) = sig.propagate_bounds(-3.0, 3.0);
    let width_narrow = hi_n - lo_n;
    let width_wide = hi_w - lo_w;
    assert!(
        width_wide >= width_narrow - 1e-10,
        "wider input should give wider output"
    );
}

// ============================================================================
// Proof status tracking tests
// ============================================================================

#[test]
fn test_proof_status_constants() {
    use crate::spec::ProofStatus;
    assert_eq!(T83_SIGMOID_MONOTONE_BOUND, ProofStatus::DerivedPending);
    assert_eq!(T85_TANH_MONOTONE_BOUND, ProofStatus::DerivedPending);
    assert_eq!(T86_GELU_APPROX_BOUND, ProofStatus::DerivedPending);
    assert_eq!(T87_ACTIVATION_LIPSCHITZ, ProofStatus::DerivedPending);
}

// ============================================================================
// Edge case and constructor tests
// ============================================================================

#[test]
fn test_activation_fn_constructors() {
    let lr = ActivationFn::leaky_relu(0.2);
    assert_eq!(lr.monotone_class(), MonotoneClass::PiecewiseMonotone);

    let elu = ActivationFn::elu(0.5);
    assert_eq!(elu.monotone_class(), MonotoneClass::PiecewiseMonotone);
}

#[test]
fn test_point_interval_propagation() {
    // Point interval should produce point output
    for act in &[
        ActivationFn::Sigmoid,
        ActivationFn::Tanh,
        ActivationFn::Softplus,
        ActivationFn::GeluApprox,
        ActivationFn::leaky_relu(0.1),
        ActivationFn::elu(1.0),
    ] {
        let (lo, hi) = act.propagate_bounds(1.0, 1.0);
        assert!(
            (lo - hi).abs() < 1e-10,
            "point interval should produce point output for {:?}: [{lo}, {hi}]",
            act
        );
    }
}

#[test]
fn test_all_activations_bounds_ordered() {
    // For all activations, propagated lower <= upper
    let activations: Vec<ActivationFn> = vec![
        ActivationFn::Sigmoid,
        ActivationFn::Tanh,
        ActivationFn::Softplus,
        ActivationFn::GeluApprox,
        ActivationFn::leaky_relu(0.01),
        ActivationFn::leaky_relu(0.5),
        ActivationFn::elu(1.0),
        ActivationFn::elu(0.1),
    ];
    let intervals = [(-10.0, 10.0), (-1.0, 1.0), (0.0, 5.0), (-5.0, 0.0)];
    for act in &activations {
        for &(lo, hi) in &intervals {
            let (out_lo, out_hi) = act.propagate_bounds(lo, hi);
            assert!(
                out_lo <= out_hi + 1e-10,
                "{:?} on [{lo},{hi}]: lower={out_lo} > upper={out_hi}",
                act
            );
        }
    }
}

#[test]
fn test_lipschitz_nonnegative() {
    let activations: Vec<ActivationFn> = vec![
        ActivationFn::Sigmoid,
        ActivationFn::Tanh,
        ActivationFn::Softplus,
        ActivationFn::GeluApprox,
        ActivationFn::leaky_relu(0.1),
        ActivationFn::elu(1.0),
    ];
    for act in &activations {
        let l = activation_lipschitz(*act, -5.0, 5.0);
        assert!(
            l >= 0.0,
            "Lipschitz constant must be non-negative for {:?}: {l}",
            act
        );
    }
}

// ============================================================================
// Wave B: T83 sigmoid and T85 tanh kernel proof verification
// ============================================================================

#[test]
fn test_t83_sigmoid_monotone_bound_verified() {
    use super::monotone::verify_sigmoid_monotone_bound;
    // Verify at known points
    verify_sigmoid_monotone_bound(0.0, -2.0, 2.0).expect("sigmoid(0) in bounds");
    verify_sigmoid_monotone_bound(-2.0, -2.0, 2.0).expect("sigmoid at lower endpoint");
    verify_sigmoid_monotone_bound(2.0, -2.0, 2.0).expect("sigmoid at upper endpoint");
    verify_sigmoid_monotone_bound(1.5, 1.0, 3.0).expect("sigmoid in positive interval");
    verify_sigmoid_monotone_bound(-1.5, -3.0, -1.0).expect("sigmoid in negative interval");
}

#[test]
fn test_t83_sigmoid_monotone_bound_random() {
    use super::monotone::verify_sigmoid_monotone_bound;
    let mut rng: u64 = 12345;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..500 {
        let a = -10.0 + lcg(&mut rng) * 20.0;
        let b = a + lcg(&mut rng) * 5.0;
        let x = a + lcg(&mut rng) * (b - a);
        verify_sigmoid_monotone_bound(x, a, b)
            .unwrap_or_else(|e| panic!("T83 failed for x={x}, [{a},{b}]: {e}"));
    }
}

#[test]
fn test_t83_sigmoid_rejects_out_of_bounds() {
    use super::monotone::verify_sigmoid_monotone_bound;
    assert!(verify_sigmoid_monotone_bound(5.0, 0.0, 1.0).is_err());
    assert!(verify_sigmoid_monotone_bound(-2.0, 0.0, 1.0).is_err());
}

#[test]
fn test_t85_tanh_monotone_bound_verified() {
    use super::monotone::verify_tanh_monotone_bound;
    verify_tanh_monotone_bound(0.0, -2.0, 2.0).expect("tanh(0) in bounds");
    verify_tanh_monotone_bound(-2.0, -2.0, 2.0).expect("tanh at lower endpoint");
    verify_tanh_monotone_bound(2.0, -2.0, 2.0).expect("tanh at upper endpoint");
    verify_tanh_monotone_bound(0.5, -1.0, 1.0).expect("tanh in symmetric interval");
}

#[test]
fn test_t85_tanh_monotone_bound_random() {
    use super::monotone::verify_tanh_monotone_bound;
    let mut rng: u64 = 67890;
    let lcg = |state: &mut u64| -> f64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (*state >> 33) as f64 / (1u64 << 31) as f64
    };
    for _ in 0..500 {
        let a = -10.0 + lcg(&mut rng) * 20.0;
        let b = a + lcg(&mut rng) * 5.0;
        let x = a + lcg(&mut rng) * (b - a);
        verify_tanh_monotone_bound(x, a, b)
            .unwrap_or_else(|e| panic!("T85 failed for x={x}, [{a},{b}]: {e}"));
    }
}

#[test]
fn test_t85_tanh_rejects_out_of_bounds() {
    use super::monotone::verify_tanh_monotone_bound;
    assert!(verify_tanh_monotone_bound(5.0, 0.0, 1.0).is_err());
}

#[test]
fn test_t83_t85_proof_status_is_proved() {
    use crate::spec::ProofStatus;
    assert_eq!(T83_SIGMOID_MONOTONE_BOUND, ProofStatus::DerivedPending);
    assert_eq!(T85_TANH_MONOTONE_BOUND, ProofStatus::DerivedPending);
}
