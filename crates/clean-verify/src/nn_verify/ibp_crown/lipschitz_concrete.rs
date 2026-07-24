// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete Lipschitz Verification via Power Iteration
//!
//! Executable implementations of the Lipschitz theorems specified in
//! [`lipschitz`](super::lipschitz). Connects the proof specs (T30, T32, T33)
//! to concrete numerical computation.
//!
//! ## Key Functions
//!
//! - [`power_iteration`]: Approximate max singular value of a matrix via
//!   power iteration on W^T W. Convergence: O(|lambda_1/lambda_2|^k).
//! - [`compute_layer_lipschitz`]: Spectral norm (T32) for a linear layer.
//! - [`compute_relu_lipschitz`]: ReLU is 1-Lipschitz (non-expansive).
//! - [`compute_network_lipschitz`]: Product of per-layer constants (T30/T32).
//! - [`compute_residual_lipschitz`]: Residual block bound (T33).
//! - [`verify_lipschitz_compose`]: Concrete check of submultiplicativity (T30).
//!
//! ## Connection to `neural_surgery::bound_propagation`
//!
//! The [`LipschitzBound`](crate::neural_surgery::LipschitzBound) in
//! `neural_surgery` is the consumer of these computed constants. After
//! calling [`compute_network_lipschitz`], wrap the result via
//! `LipschitzBound::new(constant)` and feed it into
//! `BoundPropagationSpec::propagate_bound` for delta verification.

use super::lipschitz::{LayerLipschitz, LipschitzComposeSpec, LipschitzSource};

// ---------------------------------------------------------------------------
// Layer specification
// ---------------------------------------------------------------------------

/// Specification of a single neural network layer for Lipschitz analysis.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum LayerSpec {
    /// Linear (fully-connected) layer: y = Wx + b.
    /// Stores the weight matrix as row-major `Vec<Vec<f64>>`.
    Linear(Vec<Vec<f64>>),
    /// ReLU activation (element-wise). Lipschitz constant = 1.
    Relu,
}

// ---------------------------------------------------------------------------
// Power iteration (core numerical routine)
// ---------------------------------------------------------------------------

/// Approximate the largest singular value of a matrix via power iteration.
///
/// Computes the dominant eigenvalue of W^T W by repeated matrix-vector
/// multiplication. The singular value is `sqrt(eigenvalue)`.
///
/// # Algorithm
///
/// 1. Initialize v as the all-ones vector, normalized.
/// 2. Repeat `iterations` times: v <- W^T W v, then normalize.
/// 3. Return sqrt(v^T W^T W v) as the approximate max singular value.
///
/// Convergence rate: geometric in |lambda_1 / lambda_2|.
///
/// # Parameters
///
/// - `matrix`: Row-major m x n matrix (slice of row slices).
/// - `iterations`: Number of power iteration steps (typically 20-100).
///
/// # Returns
///
/// The approximate spectral norm (max singular value). Returns 0.0 for
/// an empty matrix.
#[must_use]
pub fn power_iteration(matrix: &[&[f64]], iterations: usize) -> f64 {
    if matrix.is_empty() {
        return 0.0;
    }
    let m = matrix.len();
    let n = matrix[0].len();
    if n == 0 {
        return 0.0;
    }

    // Initialize v (n-dimensional) to uniform unit vector.
    let inv_sqrt_n = 1.0 / (n as f64).sqrt();
    let mut v: Vec<f64> = vec![inv_sqrt_n; n];

    for _ in 0..iterations {
        // u = W * v  (m-dimensional)
        let u: Vec<f64> = (0..m)
            .map(|i| {
                matrix[i]
                    .iter()
                    .zip(v.iter())
                    .map(|(w, vi)| w * vi)
                    .sum::<f64>()
            })
            .collect();

        // v_new = W^T * u  (n-dimensional)
        let mut v_new = vec![0.0; n];
        for i in 0..m {
            for j in 0..n {
                v_new[j] += matrix[i][j] * u[i];
            }
        }

        // Normalize v_new.
        let norm: f64 = v_new.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm < f64::EPSILON {
            return 0.0;
        }
        for x in &mut v_new {
            *x /= norm;
        }
        v = v_new;
    }

    // Compute the Rayleigh quotient: sigma = sqrt(v^T W^T W v).
    // First: u = W * v
    let u: Vec<f64> = (0..m)
        .map(|i| {
            matrix[i]
                .iter()
                .zip(v.iter())
                .map(|(w, vi)| w * vi)
                .sum::<f64>()
        })
        .collect();
    // sigma = ||u|| = ||Wv||
    u.iter().map(|x| x * x).sum::<f64>().sqrt()
}

// ---------------------------------------------------------------------------
// Per-layer Lipschitz computation
// ---------------------------------------------------------------------------

/// Compute the Lipschitz constant of a linear layer y = Wx.
///
/// The Lipschitz constant equals the spectral norm (largest singular value)
/// of W (T32). Uses [`power_iteration`] with the given iteration count.
///
/// # Parameters
///
/// - `weight`: Row-major weight matrix (slice of row slices).
/// - `iterations`: Number of power iteration steps.
#[must_use]
pub fn compute_layer_lipschitz(weight: &[&[f64]], iterations: usize) -> f64 {
    power_iteration(weight, iterations)
}

/// Compute the Lipschitz constant of a ReLU activation.
///
/// ReLU(x) = max(0, x) is 1-Lipschitz because:
///   |ReLU(a) - ReLU(b)| <= |a - b| for all a, b.
#[must_use]
pub fn compute_relu_lipschitz() -> f64 {
    1.0
}

// ---------------------------------------------------------------------------
// Network-level Lipschitz (T30 + T32)
// ---------------------------------------------------------------------------

/// Compute the Lipschitz constant of a feedforward network.
///
/// Applies T30 (submultiplicativity): the Lipschitz constant of a
/// sequential composition is the product of per-layer constants.
/// Each linear layer's constant is computed via spectral norm (T32);
/// ReLU layers contribute 1.0.
///
/// # Parameters
///
/// - `layers`: Ordered sequence of layer specifications.
/// - `power_iterations`: Number of power iteration steps for spectral norm.
#[must_use]
pub fn compute_network_lipschitz(layers: &[LayerSpec], power_iterations: usize) -> f64 {
    let per_layer: Vec<LayerLipschitz> = layers
        .iter()
        .map(|layer| match layer {
            LayerSpec::Linear(weight) => {
                let refs: Vec<&[f64]> = weight.iter().map(|r| r.as_slice()).collect();
                let sigma = power_iteration(&refs, power_iterations);
                LayerLipschitz::new(sigma, LipschitzSource::SpectralNorm)
            }
            LayerSpec::Relu => LayerLipschitz::relu(),
        })
        .collect();

    let compose_spec = LipschitzComposeSpec::new();
    compose_spec.compose_chain(&per_layer).constant()
}

// ---------------------------------------------------------------------------
// Residual Lipschitz (T33)
// ---------------------------------------------------------------------------

/// Compute the Lipschitz constant of a residual block y = x + f(x).
///
/// By the triangle inequality on operator norms (T33):
///   ||y(a) - y(b)|| = ||(a - b) + (f(a) - f(b))|| <= (1 + L_f) * ||a - b||
///
/// For a transformer block with parallel attention and FFN residuals:
///   L_block = (1 + L_attn) * (1 + L_ffn)   (T31 = T33 composed via T30)
///
/// This function computes the single-branch version: 1 + L_attn + L_ffn,
/// appropriate when attention and FFN share a single residual connection
/// (y = x + attn(x) + ffn(x)) rather than sequential residuals.
#[must_use]
pub fn compute_residual_lipschitz(attention_lip: f64, ffn_lip: f64) -> f64 {
    1.0 + attention_lip + ffn_lip
}

// ---------------------------------------------------------------------------
// T30 concrete verification
// ---------------------------------------------------------------------------

/// Verify submultiplicativity of composed Lipschitz constants (T30).
///
/// For f with constant l1 and g with constant l2, the composition
/// g . f must have constant <= l1 * l2. Returns true iff the
/// `composed` value satisfies this upper bound (within floating-point
/// tolerance).
///
/// # Parameters
///
/// - `l1`: Lipschitz constant of the first function.
/// - `l2`: Lipschitz constant of the second function.
/// - `composed`: Claimed Lipschitz constant of the composition.
#[must_use]
pub fn verify_lipschitz_compose(l1: f64, l2: f64, composed: f64) -> bool {
    composed <= l1 * l2 + f64::EPSILON
}

// ---------------------------------------------------------------------------
// Matrix multiplication helper (for testing submultiplicativity)
// ---------------------------------------------------------------------------

/// Multiply two row-major matrices: C = A * B.
///
/// A is (m x k), B is (k x n), result C is (m x n).
///
/// # Panics
///
/// Panics if inner dimensions do not match.
#[cfg(test)]
#[must_use]
pub(crate) fn mat_mul(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let m = a.len();
    assert!(!a.is_empty(), "matrix A must be non-empty");
    let k = a[0].len();
    assert!(!b.is_empty(), "matrix B must be non-empty");
    assert_eq!(
        k,
        b.len(),
        "inner dimensions must match: A cols={k}, B rows={}",
        b.len()
    );
    let n = b[0].len();

    let mut c = vec![vec![0.0; n]; m];
    for i in 0..m {
        for j in 0..n {
            let mut sum = 0.0;
            for p in 0..k {
                sum += a[i][p] * b[p][j];
            }
            c[i][j] = sum;
        }
    }
    c
}
