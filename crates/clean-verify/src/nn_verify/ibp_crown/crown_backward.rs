// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CROWN backward pass: per-layer propagation and end-to-end verification.
//!
//! Contains the core backward propagation functions that compose per-layer
//! relaxations into global symbolic bounds. See [`super::crown`] for types.

use super::crown::{crown_concretize, CrownBound, CrownResult};

/// Propagate a `CrownBound` backward through a linear layer y = W * x + b.
///
/// Given the current symbolic bound relating outputs to the post-linear
/// activations, produce a new bound relating outputs to the pre-linear inputs.
///
/// The matrix product computes: new_coeffs[i][j] = sum_k coeffs[i][k] * weight[k][j],
/// and the bias absorbs: new_bias[i] = old_bias[i] + sum_k coeffs[i][k] * layer_bias[k].
///
/// `weight` is row-major (out_features x in_features), `bias` has length out_features.
#[must_use]
pub fn crown_linear_backward(weight: &[Vec<f64>], bias: &[f64], bound: &CrownBound) -> CrownBound {
    let num_outputs = bound.num_outputs();
    let in_features = if weight.is_empty() {
        0
    } else {
        weight[0].len()
    };

    let mut new_lower_coeffs = vec![vec![0.0; in_features]; num_outputs];
    let mut new_upper_coeffs = vec![vec![0.0; in_features]; num_outputs];
    let mut new_lower_bias = vec![0.0; num_outputs];
    let mut new_upper_bias = vec![0.0; num_outputs];

    for i in 0..num_outputs {
        let lower_row = &bound.lower_coeffs[i];
        let upper_row = &bound.upper_coeffs[i];

        let mut lb = bound.lower_bias[i];
        let mut ub = bound.upper_bias[i];

        for (k, (lk, uk)) in lower_row.iter().zip(upper_row.iter()).enumerate() {
            // Bias contribution
            lb += lk * bias[k];
            ub += uk * bias[k];

            // Matrix product: new_coeffs[i][j] = sum_k coeffs[i][k] * weight[k][j]
            let w_row = &weight[k];
            for (j, w_kj) in w_row.iter().enumerate() {
                new_lower_coeffs[i][j] += lk * w_kj;
                new_upper_coeffs[i][j] += uk * w_kj;
            }
        }

        new_lower_bias[i] = lb;
        new_upper_bias[i] = ub;
    }

    CrownBound {
        lower_coeffs: new_lower_coeffs,
        upper_coeffs: new_upper_coeffs,
        lower_bias: new_lower_bias,
        upper_bias: new_upper_bias,
    }
}

/// Propagate a `CrownBound` backward through a ReLU layer.
///
/// For each neuron k with pre-activation bounds [l_k, u_k]:
///
/// - **Always active** (l_k >= 0): ReLU is identity. Keep coefficients unchanged.
/// - **Always inactive** (u_k <= 0): ReLU is zero. Zero out coefficients.
/// - **Crossing** (l_k < 0 < u_k): Apply alpha relaxation.
///   - Upper relaxation slope: lambda = u_k / (u_k - l_k)
///   - Upper relaxation intercept: mu = -l_k * u_k / (u_k - l_k)
///   - Lower relaxation: alpha = 0 (sound, conservative)
///
/// Sign-dependent dispatch for crossing neurons:
/// - Positive lower coeff + crossing => alpha=0 (want ReLU small for lower bound)
/// - Negative lower coeff + crossing => use upper relaxation (want ReLU large)
/// - Positive upper coeff + crossing => use upper relaxation (want ReLU large)
/// - Negative upper coeff + crossing => alpha=0 (want ReLU small for upper bound)
#[must_use]
pub fn crown_relu_backward(lower: &[f64], upper: &[f64], bound: &CrownBound) -> CrownBound {
    let num_outputs = bound.num_outputs();
    let num_neurons = lower.len();

    let mut new_lower_coeffs = vec![vec![0.0; num_neurons]; num_outputs];
    let mut new_upper_coeffs = vec![vec![0.0; num_neurons]; num_outputs];
    let mut new_lower_bias = bound.lower_bias.clone();
    let mut new_upper_bias = bound.upper_bias.clone();

    for i in 0..num_outputs {
        for k in 0..num_neurons {
            let l_k = lower[k];
            let u_k = upper[k];
            let lc = bound.lower_coeffs[i][k];
            let uc = bound.upper_coeffs[i][k];

            if l_k >= 0.0 {
                // Always active: identity pass-through
                new_lower_coeffs[i][k] = lc;
                new_upper_coeffs[i][k] = uc;
            } else if u_k <= 0.0 {
                // Always inactive: zero out
                new_lower_coeffs[i][k] = 0.0;
                new_upper_coeffs[i][k] = 0.0;
            } else {
                // Crossing case: l_k < 0 < u_k
                let lambda = u_k / (u_k - l_k);
                let mu = -l_k * u_k / (u_k - l_k);

                // Lower bound on f(x): need lower bound on ReLU(z_k)
                if lc >= 0.0 {
                    // Positive coeff wants ReLU small => alpha=0
                    new_lower_coeffs[i][k] = 0.0;
                } else {
                    // Negative coeff wants ReLU large => upper relaxation
                    new_lower_coeffs[i][k] = lc * lambda;
                    new_lower_bias[i] += lc * mu;
                }

                // Upper bound on f(x): need upper bound on ReLU(z_k)
                if uc >= 0.0 {
                    // Positive coeff wants ReLU large => upper relaxation
                    new_upper_coeffs[i][k] = uc * lambda;
                    new_upper_bias[i] += uc * mu;
                } else {
                    // Negative coeff wants ReLU small => alpha=0
                    new_upper_coeffs[i][k] = 0.0;
                }
            }
        }
    }

    CrownBound {
        lower_coeffs: new_lower_coeffs,
        upper_coeffs: new_upper_coeffs,
        lower_bias: new_lower_bias,
        upper_bias: new_upper_bias,
    }
}

/// Full CROWN backward pass: propagate from output to input, then concretize.
///
/// `network` is a list of (weight, bias) pairs from input to output.
/// `input_lower` and `input_upper` define the input interval.
///
/// The algorithm:
/// 1. Run IBP forward to get pre-activation bounds at each layer.
/// 2. Initialize identity bound at the output.
/// 3. Walk backward through layers, applying `crown_relu_backward` then
///    `crown_linear_backward` for each layer.
/// 4. Concretize at the input layer.
#[must_use]
pub fn verify_crown_bounds(
    network: &[(Vec<Vec<f64>>, Vec<f64>)],
    input_lower: &[f64],
    input_upper: &[f64],
) -> CrownResult {
    if network.is_empty() {
        return CrownResult {
            lower: input_lower.to_vec(),
            upper: input_upper.to_vec(),
        };
    }

    // Phase 1: IBP forward pass to collect pre-activation bounds.
    let num_layers = network.len();
    let mut pre_act_lower: Vec<Vec<f64>> = Vec::with_capacity(num_layers);
    let mut pre_act_upper: Vec<Vec<f64>> = Vec::with_capacity(num_layers);

    let mut current_lower = input_lower.to_vec();
    let mut current_upper = input_upper.to_vec();

    for (layer_idx, (weight, bias)) in network.iter().enumerate() {
        let m = weight.len();
        let mut out_lower = Vec::with_capacity(m);
        let mut out_upper = Vec::with_capacity(m);

        for r in 0..m {
            let row = &weight[r];
            let mut yl = bias[r];
            let mut yu = bias[r];
            for (j, w) in row.iter().enumerate() {
                if *w >= 0.0 {
                    yl += w * current_lower[j];
                    yu += w * current_upper[j];
                } else {
                    yl += w * current_upper[j];
                    yu += w * current_lower[j];
                }
            }
            out_lower.push(yl);
            out_upper.push(yu);
        }

        pre_act_lower.push(out_lower.clone());
        pre_act_upper.push(out_upper.clone());

        // Apply ReLU for all layers except the last (output has no activation)
        if layer_idx < num_layers - 1 {
            current_lower = out_lower.iter().map(|v| v.max(0.0)).collect();
            current_upper = out_upper.iter().map(|v| v.max(0.0)).collect();
        } else {
            current_lower = out_lower;
            current_upper = out_upper;
        }
    }

    // Phase 2: CROWN backward pass.
    let output_dim = network.last().map_or(0, |(w, _)| w.len());
    let mut bound = CrownBound::identity(output_dim);

    for layer_idx in (0..num_layers).rev() {
        let (weight, bias) = &network[layer_idx];

        // Apply ReLU backward for all layers except the last
        if layer_idx < num_layers - 1 {
            bound =
                crown_relu_backward(&pre_act_lower[layer_idx], &pre_act_upper[layer_idx], &bound);
        }

        bound = crown_linear_backward(weight, bias, &bound);
    }

    // Phase 3: Concretize
    let (concrete_lower, concrete_upper) = crown_concretize(&bound, input_lower, input_upper);

    CrownResult {
        lower: concrete_lower,
        upper: concrete_upper,
    }
}
