// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C010 zonotope-CROWN equivalence on purely linear networks.
//!
//! Exercises exact agreement between interval bounds obtained from zonotope
//! forward propagation and CROWN backward propagation on linear (ReLU-free)
//! networks.

use super::c010_equiv::{
    crown_linear_bounds, product_matrix, verify_c010_equivalence, verify_c010_inductive,
    zonotope_linear_bounds, C010EquivSpec, LinearLayer,
};
use crate::spec::ProofStatus;

const TOL: f64 = 1e-10;

/// Helper to build a layer from const arrays.
fn layer<const ROWS: usize, const COLS: usize>(
    weights: [[f64; COLS]; ROWS],
    bias: [f64; ROWS],
) -> LinearLayer {
    (
        weights.into_iter().map(|row| row.to_vec()).collect(),
        bias.to_vec(),
    )
}

/// Assert two f64 slices are elementwise close.
fn assert_vec_close(actual: &[f64], expected: &[f64]) {
    assert_eq!(actual.len(), expected.len(), "length mismatch");
    for (i, (&a, &e)) in actual.iter().zip(expected.iter()).enumerate() {
        assert!(
            (a - e).abs() <= TOL,
            "mismatch at index {i}: expected {e:.12}, got {a:.12}"
        );
    }
}

/// Assert two matrices are elementwise close.
fn assert_matrix_close(actual: &[Vec<f64>], expected: &[Vec<f64>]) {
    assert_eq!(actual.len(), expected.len(), "row count mismatch");
    for (r, (a_row, e_row)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(a_row.len(), e_row.len(), "column count mismatch at row {r}");
        for (c, (&a, &e)) in a_row.iter().zip(e_row.iter()).enumerate() {
            assert!(
                (a - e).abs() <= TOL,
                "mismatch at ({r},{c}): expected {e:.12}, got {a:.12}"
            );
        }
    }
}

/// Reference: compute interval image of affine map W*x + b on [lo, hi].
fn affine_interval_bounds_reference(
    weight: &[Vec<f64>],
    bias: &[f64],
    input_lower: &[f64],
    input_upper: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    let mut lower = Vec::with_capacity(weight.len());
    let mut upper = Vec::with_capacity(weight.len());
    for (row, &b) in weight.iter().zip(bias.iter()) {
        let mut rl = b;
        let mut ru = b;
        for ((&w, &lo), &hi) in row.iter().zip(input_lower.iter()).zip(input_upper.iter()) {
            if w >= 0.0 {
                rl += w * lo;
                ru += w * hi;
            } else {
                rl += w * hi;
                ru += w * lo;
            }
        }
        lower.push(rl);
        upper.push(ru);
    }
    (lower, upper)
}

/// Reference: compose layers into a single affine map.
fn compose_layers_reference(layers: &[LinearLayer]) -> (Vec<Vec<f64>>, Vec<f64>) {
    let (mut weight, mut bias) = layers[0].clone();
    for (next_w, next_b) in layers.iter().skip(1) {
        let pushed: Vec<f64> = next_w
            .iter()
            .zip(next_b.iter())
            .map(|(row, &nb)| {
                row.iter()
                    .zip(bias.iter())
                    .map(|(&w, &b)| w * b)
                    .sum::<f64>()
                    + nb
            })
            .collect();
        let new_weight: Vec<Vec<f64>> = next_w
            .iter()
            .map(|row| {
                let cols = weight[0].len();
                (0..cols)
                    .map(|j| {
                        row.iter()
                            .zip(weight.iter())
                            .map(|(&w, wr)| w * wr[j])
                            .sum()
                    })
                    .collect()
            })
            .collect();
        weight = new_weight;
        bias = pushed;
    }
    (weight, bias)
}

/// Assert zonotope and CROWN bounds match, return the bounds.
fn assert_methods_match(
    layers: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    let (zl, zu) = zonotope_linear_bounds(layers, input_lower, input_upper)
        .expect("zonotope_linear_bounds should succeed");
    let (cl, cu) = crown_linear_bounds(layers, input_lower, input_upper)
        .expect("crown_linear_bounds should succeed");
    assert_vec_close(&zl, &cl);
    assert_vec_close(&zu, &cu);
    (zl, zu)
}

// ---- Tests ----

#[test]
fn test_c010_spec_status_is_derived_proved() {
    // Part of #3310: C010 zonotope-CROWN equivalence promoted to DerivedPending.
    let spec = C010EquivSpec::new();
    assert_eq!(spec.status(), ProofStatus::DerivedPending);
}

#[test]
fn test_bounds_single_layer_identity_returns_input_bounds() {
    let layers = vec![layer([[1.0, 0.0], [0.0, 1.0]], [0.0, 0.0])];
    let lo = [-1.5, 0.5];
    let hi = [2.0, 3.5];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    assert_vec_close(&lower, &lo);
    assert_vec_close(&upper, &hi);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_single_layer_scaling_scales_each_dimension() {
    let layers = vec![layer([[2.0, 0.0], [0.0, 3.0]], [0.0, 0.0])];
    let lo = [-1.0, 2.0];
    let hi = [4.0, 5.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    assert_vec_close(&lower, &[-2.0, 6.0]);
    assert_vec_close(&upper, &[8.0, 15.0]);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_single_layer_rotation_like_matches_expected() {
    let layers = vec![layer([[0.0, -1.0], [1.0, 0.0]], [0.0, 0.0])];
    let lo = [-1.0, 2.0];
    let hi = [3.0, 5.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    assert_vec_close(&lower, &[-5.0, -1.0]);
    assert_vec_close(&upper, &[-2.0, 3.0]);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_two_layer_composition_matches_reference() {
    let layers = vec![
        layer([[1.0, 2.0], [0.0, -1.0]], [0.0, 0.0]),
        layer([[2.0, 1.0], [-1.0, 3.0]], [0.0, 0.0]),
    ];
    let lo = [-1.0, 0.0];
    let hi = [2.0, 4.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    let (w, b) = compose_layers_reference(&layers);
    let (el, eu) = affine_interval_bounds_reference(&w, &b, &lo, &hi);
    assert_vec_close(&lower, &el);
    assert_vec_close(&upper, &eu);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_three_layer_dim_change_matches_reference() {
    let layers = vec![
        layer([[1.0, -1.0, 2.0], [0.5, 3.0, -2.0]], [0.0, 0.0]),
        layer(
            [[1.0, 2.0], [-1.0, 0.0], [0.0, -3.0], [2.5, 1.5]],
            [0.0, 0.0, 0.0, 0.0],
        ),
        layer([[1.0, -2.0, 0.5, 1.0], [-1.5, 0.0, 2.0, -0.5]], [0.0, 0.0]),
    ];
    let lo = [-1.0, 0.0, 2.0];
    let hi = [1.0, 3.0, 5.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    let (w, b) = compose_layers_reference(&layers);
    let (el, eu) = affine_interval_bounds_reference(&w, &b, &lo, &hi);
    assert_vec_close(&lower, &el);
    assert_vec_close(&upper, &eu);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_network_with_biases_includes_bias_offsets() {
    let layers = vec![
        layer([[2.0, -1.0], [1.5, 0.5]], [0.25, -0.5]),
        layer([[1.0, 3.0], [-2.0, 4.0]], [1.25, -2.0]),
    ];
    let lo = [-2.0, 1.0];
    let hi = [3.0, 2.5];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    let (w, b) = compose_layers_reference(&layers);
    let (el, eu) = affine_interval_bounds_reference(&w, &b, &lo, &hi);
    assert_vec_close(&lower, &el);
    assert_vec_close(&upper, &eu);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_product_matrix_identity_left_preserves_matrix() {
    let layers: Vec<LinearLayer> = vec![
        (vec![vec![1.0, 0.0], vec![0.0, 1.0]], vec![0.0, 0.0]),
        (vec![vec![2.0, -1.0], vec![0.5, 3.0]], vec![0.0, 0.0]),
    ];
    let prod = product_matrix(&layers).expect("product_matrix should succeed");
    assert_matrix_close(&prod, &[vec![2.0, -1.0], vec![0.5, 3.0]]);
}

#[test]
fn test_product_matrix_associativity() {
    let a: LinearLayer = (vec![vec![1.0, 2.0], vec![-1.0, 0.5]], vec![0.0, 0.0]);
    let b: LinearLayer = (vec![vec![0.0, 1.0], vec![3.0, -2.0]], vec![0.0, 0.0]);
    let c: LinearLayer = (vec![vec![2.0, -1.0], vec![1.5, 4.0]], vec![0.0, 0.0]);

    let ab_layers = vec![a.clone(), b.clone()];
    let ab = product_matrix(&ab_layers).expect("ab should succeed");
    let abc_left_layers = vec![(ab, vec![0.0, 0.0]), c.clone()];
    let left = product_matrix(&abc_left_layers).expect("abc_left should succeed");

    let bc_layers = vec![b, c];
    let bc = product_matrix(&bc_layers).expect("bc should succeed");
    let abc_right_layers = vec![a, (bc, vec![0.0, 0.0])];
    let right = product_matrix(&abc_right_layers).expect("abc_right should succeed");

    assert_matrix_close(&left, &right);
}

#[test]
fn test_verify_inductive_single_layer_returns_success() {
    let weight = vec![vec![2.0, 0.0], vec![0.0, -3.0]];
    let bias = vec![0.0, 1.0];
    let lo = [-2.0, -1.0];
    let hi = [1.5, 4.0];
    assert!(verify_c010_inductive(&weight, &bias, &lo, &hi).expect("inductive step should succeed"));
}

#[test]
fn test_verify_inductive_nondiagonal_returns_success() {
    let weight = vec![vec![1.0, -2.0], vec![3.5, 0.5]];
    let bias = vec![0.25, -1.5];
    let lo = [-1.0, 2.0];
    let hi = [4.0, 5.0];
    let (lower, upper) = zonotope_linear_bounds(&[(weight.clone(), bias.clone())], &lo, &hi)
        .expect("zonotope should succeed");
    let (el, eu) = affine_interval_bounds_reference(&weight, &bias, &lo, &hi);
    assert_vec_close(&lower, &el);
    assert_vec_close(&upper, &eu);
    assert!(verify_c010_inductive(&weight, &bias, &lo, &hi).expect("inductive step should succeed"));
}

#[test]
fn test_bounds_scalar_1x1_network() {
    let layers = vec![layer([[-2.0]], [0.5])];
    let lo = [-3.0];
    let hi = [4.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    // y = -2x + 0.5, x in [-3, 4] => y in [-2*4+0.5, -2*(-3)+0.5] = [-7.5, 6.5]
    assert!((lower[0] - (-7.5)).abs() <= TOL);
    assert!((upper[0] - 6.5).abs() <= TOL);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_wide_ten_dim_network_matches_reference() {
    let mut weight = vec![vec![0.0; 10]; 10];
    for (i, row) in weight.iter_mut().enumerate() {
        row[i] = 1.0 + (i as f64) * 0.1;
        if i + 1 < 10 {
            row[i + 1] = -0.25;
        }
        if i > 0 {
            row[i - 1] = 0.15;
        }
    }
    let bias: Vec<f64> = (0..10).map(|i| (i as f64) * 0.2 - 0.5).collect();
    let layers = vec![(weight.clone(), bias.clone())];
    let lo: Vec<f64> = (0..10).map(|i| -(i as f64) - 1.0).collect();
    let hi: Vec<f64> = (0..10).map(|i| (i as f64) + 1.5).collect();

    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    let (el, eu) = affine_interval_bounds_reference(&weight, &bias, &lo, &hi);
    assert_vec_close(&lower, &el);
    assert_vec_close(&upper, &eu);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_negative_weight_flips_intervals() {
    let layers = vec![layer([[-1.0, 0.0], [0.0, -1.0]], [0.0, 0.0])];
    let lo = [1.0, 2.0];
    let hi = [3.0, 5.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    assert_vec_close(&lower, &[-3.0, -5.0]);
    assert_vec_close(&upper, &[-1.0, -2.0]);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}

#[test]
fn test_bounds_point_input_collapses_to_exact_value() {
    let layers = vec![layer([[2.0, -1.0], [0.5, 3.0]], [1.0, -0.5])];
    let lo = [1.0, 2.0];
    let hi = [1.0, 2.0];
    let (lower, upper) = assert_methods_match(&layers, &lo, &hi);
    // y0 = 2*1 - 1*2 + 1 = 1; y1 = 0.5*1 + 3*2 - 0.5 = 6
    assert_vec_close(&lower, &[1.0, 6.0]);
    assert_vec_close(&upper, &[1.0, 6.0]);
    assert!(verify_c010_equivalence(&layers, &lo, &hi).expect("verify should succeed"));
}
