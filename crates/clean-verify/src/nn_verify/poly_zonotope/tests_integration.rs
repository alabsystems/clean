// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for polynomial zonotope attention verification (C015).
//!
//! These tests exercise the full pipeline from polynomial zonotope construction
//! through attention bound computation and tightness verification.

use super::attention::{
    attention_bound_poly, compare_attention_bounds, verify_attention_soundness,
};
use super::c015_spec::c015_theorem_entries;
use super::tightness::{analyze_tightness, verify_o_eps_tightness};
use super::types::PolyZonotope;

/// Helper: create a scalar polynomial zonotope from center and perturbation.
fn make_pz(center: f64, eps: f64) -> PolyZonotope {
    PolyZonotope::try_new(vec![center], vec![vec![eps]], vec![vec![0.0]], 1)
        .expect("should create scalar PZ")
}

// -- C015a: Product soundness --

#[test]
fn test_c015a_product_soundness_grid() {
    // Verify that the Hadamard product of two poly zonotopes contains
    // the true product for all sampled noise symbol values.
    let x = make_pz(2.0, 0.5);
    let y = make_pz(3.0, 0.5);

    let product = x
        .hadamard_product_scalar(&y)
        .expect("should compute product");
    let (lo, hi) = product.to_interval();

    // Sample eps values and check containment
    for eps_val in [-1.0, -0.75, -0.5, -0.25, 0.0, 0.25, 0.5, 0.75, 1.0] {
        let x_val = x.evaluate(&[eps_val]).expect("should evaluate")[0];
        let y_val = y.evaluate(&[eps_val]).expect("should evaluate")[0];
        let true_product = x_val * y_val;

        assert!(
            true_product >= lo[0] - 1e-6 && true_product <= hi[0] + 1e-6,
            "product {true_product} outside bounds [{}, {}] at eps={eps_val}",
            lo[0],
            hi[0]
        );
    }
}

#[test]
fn test_c015a_product_soundness_large_perturbation() {
    let x = make_pz(1.0, 1.0);
    let y = make_pz(1.0, 1.0);

    let product = x
        .hadamard_product_scalar(&y)
        .expect("should compute product");
    let (lo, hi) = product.to_interval();

    // At eps=1: x=2, y=2, product=4
    // At eps=-1: x=0, y=0, product=0
    // At eps=0: x=1, y=1, product=1
    for &eps_val in &[-1.0, 0.0, 1.0] {
        let x_val = x.evaluate(&[eps_val]).expect("eval")[0];
        let y_val = y.evaluate(&[eps_val]).expect("eval")[0];
        let true_product = x_val * y_val;

        assert!(
            true_product >= lo[0] - 1e-6,
            "product {true_product} below lower bound {} at eps={eps_val}",
            lo[0]
        );
        assert!(
            true_product <= hi[0] + 1e-6,
            "product {true_product} above upper bound {} at eps={eps_val}",
            hi[0]
        );
    }
}

// -- C015b: Attention bound soundness --

#[test]
fn test_c015b_attention_soundness_grid() {
    let q = make_pz(1.0, 0.2);
    let k = make_pz(1.5, 0.2);
    let v = make_pz(0.5, 0.1);

    let bound = attention_bound_poly(&q, &k, &v).expect("should compute bound");

    let samples: Vec<Vec<f64>> = vec![
        vec![0.0],
        vec![1.0],
        vec![-1.0],
        vec![0.5],
        vec![-0.5],
        vec![0.25],
        vec![-0.25],
        vec![0.75],
        vec![-0.75],
    ];

    let violation = verify_attention_soundness(&q, &k, &v, &bound, &samples);
    assert!(
        violation < 1e-6,
        "attention bounds should be sound, max violation: {violation}"
    );
}

#[test]
fn test_c015b_attention_soundness_multiple_configs() {
    let configs = vec![
        (1.0, 1.0, 1.0, 0.1),
        (2.0, 0.5, 1.5, 0.2),
        (0.5, 3.0, 0.2, 0.3),
        (1.0, 1.0, 1.0, 0.5),
    ];

    let samples: Vec<Vec<f64>> = vec![vec![0.0], vec![1.0], vec![-1.0], vec![0.5], vec![-0.5]];

    for (q0, k0, v0, eps) in configs {
        let q = make_pz(q0, eps);
        let k = make_pz(k0, eps);
        let v = make_pz(v0, eps);

        let bound = attention_bound_poly(&q, &k, &v).expect("should compute bound");
        let violation = verify_attention_soundness(&q, &k, &v, &bound, &samples);

        assert!(
            violation < 1e-6,
            "attention soundness failed for q0={q0}, k0={k0}, v0={v0}, eps={eps}: \
             violation={violation}"
        );
    }
}

// -- C015c: O(eps) tightness --

#[test]
fn test_c015c_poly_o_eps_tightness() {
    let (is_tight, analysis) = verify_o_eps_tightness(1.0, 1.0, 1.0).expect("should verify");

    assert!(
        is_tight,
        "C015c: polynomial zonotope should be O(eps), order = {:.3}",
        analysis.poly_order
    );
}

#[test]
fn test_c015c_poly_o_eps_different_centers() {
    for &(q0, k0, v0) in &[(2.0, 1.0, 0.5), (0.5, 2.0, 1.0), (1.5, 1.5, 1.5)] {
        let (is_tight, analysis) = verify_o_eps_tightness(q0, k0, v0).expect("should verify");

        assert!(
            is_tight,
            "C015c: O(eps) should hold for ({q0}, {k0}, {v0}), order = {:.3}",
            analysis.poly_order
        );
    }
}

// -- C015d: Linear zonotope is O(eps^2) --

#[test]
fn test_c015d_linear_o_eps_squared() {
    // Use zero-centered q and k so interval arithmetic overestimates.
    // With q0=k0=0, the product q*k = eps^2 * eps_1^2 has range [0, eps^2],
    // but interval arithmetic gives [-eps^2, eps^2], so linear gap ~ O(eps^2).
    let eps_values = vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.2, 0.5];
    let analysis = analyze_tightness(0.0, 0.0, 1.0, &eps_values).expect("should analyze tightness");

    assert!(
        analysis.linear_is_o_eps_squared,
        "C015d: linear zonotope gap should be O(eps^2), order = {:.3}",
        analysis.linear_order
    );
}

// -- C015e: Poly zonotope dominates linear --

#[test]
fn test_c015e_poly_dominates_linear() {
    // Zero-centered q and k: interval arithmetic overestimates q*k,
    // while poly zonotope tracks eps^2 correlation via diagonal quad gen.
    let q = make_pz(0.0, 0.1);
    let k = make_pz(0.0, 0.1);
    let v = make_pz(1.0, 0.1);

    let (poly_bound, linear_bound, improvement) =
        compare_attention_bounds(&q, &k, &v).expect("should compare");

    assert!(
        improvement >= 1.0 - 1e-10,
        "C015e: poly should dominate linear, improvement ratio: {improvement}"
    );
    assert!(
        poly_bound.max_gap <= linear_bound.max_gap + 1e-10,
        "C015e: poly gap ({}) should be <= linear gap ({})",
        poly_bound.max_gap,
        linear_bound.max_gap
    );
}

#[test]
fn test_c015e_poly_dominates_different_configs() {
    // Configs with zero or near-zero centers where the poly advantage
    // materializes (interval arithmetic overestimates mixed-sign products).
    let configs = vec![
        (0.0, 0.0, 1.0, 0.1),
        (0.0, 0.0, 2.0, 0.2),
        (0.0, 0.0, 0.5, 0.15),
    ];

    for (q0, k0, v0, eps) in configs {
        let q = make_pz(q0, eps);
        let k = make_pz(k0, eps);
        let v = make_pz(v0, eps);

        let (poly_bound, linear_bound, improvement) =
            compare_attention_bounds(&q, &k, &v).expect("should compare");

        assert!(
            improvement >= 1.0 - 1e-10,
            "C015e: poly should dominate linear for q0={q0}, k0={k0}, v0={v0}, eps={eps}: \
             ratio={improvement}, poly_gap={}, linear_gap={}",
            poly_bound.max_gap,
            linear_bound.max_gap
        );
    }
}

// -- Theorem registry --

#[test]
fn test_c015_theorem_registry() {
    let entries = c015_theorem_entries();
    assert_eq!(entries.len(), 5, "C015 should have 5 sub-theorems");

    for entry in &entries {
        assert!(
            entry.id.starts_with("C015"),
            "entry ID must start with C015"
        );
    }
}

// -- Multi-symbol tests --

#[test]
fn test_poly_zonotope_multi_symbol_attention() {
    // Test with 2 noise symbols (more realistic for multi-token attention)
    let q = PolyZonotope::try_new(
        vec![1.0],
        vec![vec![0.1], vec![0.05]],
        vec![vec![0.0], vec![0.0], vec![0.0]],
        2,
    )
    .expect("should create 2-symbol q");

    let k = PolyZonotope::try_new(
        vec![1.5],
        vec![vec![0.1], vec![0.05]],
        vec![vec![0.0], vec![0.0], vec![0.0]],
        2,
    )
    .expect("should create 2-symbol k");

    let v = PolyZonotope::try_new(
        vec![0.5],
        vec![vec![0.05], vec![0.02]],
        vec![vec![0.0], vec![0.0], vec![0.0]],
        2,
    )
    .expect("should create 2-symbol v");

    let bound = attention_bound_poly(&q, &k, &v).expect("should compute multi-symbol bound");

    assert!(
        bound.max_gap > 0.0,
        "multi-symbol bound should have nonzero gap"
    );
    assert!(bound.max_gap.is_finite(), "gap should be finite");

    // Verify soundness at corners and center
    let samples = vec![
        vec![0.0, 0.0],
        vec![1.0, 1.0],
        vec![-1.0, -1.0],
        vec![1.0, -1.0],
        vec![-1.0, 1.0],
        vec![0.5, 0.5],
    ];

    let violation = verify_attention_soundness(&q, &k, &v, &bound, &samples);
    assert!(
        violation < 1e-6,
        "multi-symbol attention bounds should be sound, violation: {violation}"
    );
}

// -- Linear transform integration --

#[test]
fn test_poly_zonotope_linear_transform_preserves_containment() {
    let pz = PolyZonotope::from_linear(vec![1.0, 2.0], vec![vec![0.1, 0.0], vec![0.0, 0.1]])
        .expect("should create PZ");

    let weight = vec![vec![2.0, 1.0], vec![0.0, 3.0]];
    let bias = vec![0.5, -0.5];

    let transformed = pz
        .linear_transform(&weight, &bias)
        .expect("should transform");

    // Evaluate at corners and check containment
    let (lo, hi) = transformed.to_interval();
    for &e1 in &[-1.0, 0.0, 1.0] {
        for &e2 in &[-1.0, 0.0, 1.0] {
            let point = pz.evaluate(&[e1, e2]).expect("should evaluate");
            // Manual transform: W * point + bias
            let expected = [
                2.0 * point[0] + 1.0 * point[1] + 0.5,
                0.0 * point[0] + 3.0 * point[1] - 0.5,
            ];

            let result = transformed.evaluate(&[e1, e2]).expect("should evaluate");
            for k in 0..2 {
                assert!(
                    (result[k] - expected[k]).abs() < 1e-10,
                    "transform mismatch at dim {k}: {} vs {}, eps=({e1},{e2})",
                    result[k],
                    expected[k]
                );
                assert!(
                    result[k] >= lo[k] - 1e-10 && result[k] <= hi[k] + 1e-10,
                    "result {} outside hull [{}, {}] at dim {k}",
                    result[k],
                    lo[k],
                    hi[k]
                );
            }
        }
    }
}
