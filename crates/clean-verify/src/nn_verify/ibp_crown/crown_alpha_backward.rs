// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alpha-CROWN backward pass and gradient computation.
//!
//! Internal computation functions for the alpha-CROWN optimization loop.
//! Separated from `crown_alpha` to stay within file-size limits.

use super::crown::{crown_concretize, CrownBound};
use super::crown_alpha::AlphaCrownParams;
use super::ibp::Interval;

/// Initialize alpha parameters using the default CROWN heuristic.
///
/// For crossing neurons (l < 0 < u): alpha = u / (u - l), which minimizes
/// the area of the relaxation triangle.
/// For non-crossing neurons: alpha = 1.0 (arbitrary, ignored during backward pass).
pub(super) fn initialize_alphas(layer_bounds: &[Interval]) -> AlphaCrownParams {
    let mut alphas = Vec::with_capacity(layer_bounds.len());

    for bound in layer_bounds {
        let alpha = if bound.lower < 0.0 && bound.upper > 0.0 {
            bound.upper / (bound.upper - bound.lower)
        } else {
            1.0
        };
        alphas.push(vec![alpha]);
    }

    AlphaCrownParams { alphas }
}

/// Single backward pass with given alphas, returning output bounds as an Interval.
///
/// Propagates symbolic linear bounds backward through the network, using the
/// provided alpha values for crossing neurons in the lower-bound relaxation.
pub(super) fn backward_pass(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input_bounds: &Interval,
    layer_bounds: &[Interval],
    alphas: &AlphaCrownParams,
) -> Interval {
    let num_layers = weights.len();
    if num_layers == 0 {
        return *input_bounds;
    }

    let input_dim = if weights[0].is_empty() {
        0
    } else {
        weights[0][0].len()
    };

    // Collect per-layer pre-activation bounds from the flattened layer_bounds.
    let mut layer_pre_acts: Vec<(Vec<f64>, Vec<f64>)> = Vec::with_capacity(num_layers);
    let mut offset = 0;
    for layer_weights in weights {
        let num_neurons = layer_weights.len();
        let mut lower = Vec::with_capacity(num_neurons);
        let mut upper = Vec::with_capacity(num_neurons);
        for k in 0..num_neurons {
            if offset + k < layer_bounds.len() {
                lower.push(layer_bounds[offset + k].lower);
                upper.push(layer_bounds[offset + k].upper);
            } else {
                lower.push(f64::NEG_INFINITY);
                upper.push(f64::INFINITY);
            }
        }
        layer_pre_acts.push((lower, upper));
        offset += num_neurons;
    }

    // Start with identity bound on the output dimension.
    let output_dim = weights[num_layers - 1].len();
    let mut bound = CrownBound::identity(output_dim);

    // Walk backward through layers.
    let mut alpha_offset = 0;
    for layer_idx_rev in 0..num_layers {
        let layer_idx = num_layers - 1 - layer_idx_rev;
        let weight = &weights[layer_idx];
        let bias = &biases[layer_idx];

        // Apply ReLU backward for hidden layers (all except last).
        if layer_idx < num_layers - 1 {
            let (ref pre_lower, ref pre_upper) = layer_pre_acts[layer_idx];
            bound = alpha_relu_backward(
                pre_lower,
                pre_upper,
                &bound,
                alphas,
                layer_idx,
                &mut alpha_offset,
            );
        }

        // Apply linear backward.
        bound = alpha_linear_backward(weight, bias, &bound);
    }

    // Concretize.
    let input_lower: Vec<f64> = vec![input_bounds.lower; input_dim];
    let input_upper: Vec<f64> = vec![input_bounds.upper; input_dim];
    let (concrete_lower, concrete_upper) = crown_concretize(&bound, &input_lower, &input_upper);

    if concrete_lower.is_empty() {
        return Interval::new(0.0, 0.0);
    }

    let lo = concrete_lower[0];
    let hi = concrete_upper[0];
    if lo <= hi {
        Interval::new(lo, hi)
    } else {
        Interval::new(hi, hi)
    }
}

/// Propagate a `CrownBound` backward through a ReLU layer with per-neuron alphas.
fn alpha_relu_backward(
    lower: &[f64],
    upper: &[f64],
    bound: &CrownBound,
    alphas: &AlphaCrownParams,
    layer_idx: usize,
    _alpha_offset: &mut usize,
) -> CrownBound {
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
                new_lower_coeffs[i][k] = lc;
                new_upper_coeffs[i][k] = uc;
            } else if u_k <= 0.0 {
                new_lower_coeffs[i][k] = 0.0;
                new_upper_coeffs[i][k] = 0.0;
            } else {
                let lambda = u_k / (u_k - l_k);
                let mu = -l_k * u_k / (u_k - l_k);
                let alpha = get_alpha(alphas, layer_idx, k);

                if lc >= 0.0 {
                    new_lower_coeffs[i][k] = lc * alpha;
                } else {
                    new_lower_coeffs[i][k] = lc * lambda;
                    new_lower_bias[i] += lc * mu;
                }

                if uc >= 0.0 {
                    new_upper_coeffs[i][k] = uc * lambda;
                    new_upper_bias[i] += uc * mu;
                } else {
                    new_upper_coeffs[i][k] = uc * alpha;
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

/// Propagate a `CrownBound` backward through a linear layer.
fn alpha_linear_backward(weight: &[Vec<f64>], bias: &[f64], bound: &CrownBound) -> CrownBound {
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
            lb += lk * bias[k];
            ub += uk * bias[k];

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

/// Get alpha for a specific layer and neuron, with bounds checking.
fn get_alpha(alphas: &AlphaCrownParams, layer_idx: usize, neuron_idx: usize) -> f64 {
    if layer_idx < alphas.alphas.len() {
        let layer_alphas = &alphas.alphas[layer_idx];
        if neuron_idx < layer_alphas.len() {
            return layer_alphas[neuron_idx];
        }
    }
    0.0
}

/// Compute IBP forward bounds for each layer's pre-activation output.
///
/// Returns a flat vector of `Interval` values: for each layer, one interval
/// per output neuron, concatenated across layers.
pub(super) fn ibp_forward(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input_bounds: &Interval,
) -> Vec<Interval> {
    let mut result = Vec::new();
    if weights.is_empty() {
        return result;
    }

    let input_dim = if weights[0].is_empty() {
        0
    } else {
        weights[0][0].len()
    };
    let mut current_lower = vec![input_bounds.lower; input_dim];
    let mut current_upper = vec![input_bounds.upper; input_dim];

    for (layer_idx, (weight, bias)) in weights.iter().zip(biases.iter()).enumerate() {
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

        for (&lo, &hi) in out_lower.iter().zip(out_upper.iter()) {
            result.push(Interval::new(lo, hi));
        }

        if layer_idx < weights.len() - 1 {
            current_lower = out_lower.iter().map(|v| v.max(0.0)).collect();
            current_upper = out_upper.iter().map(|v| v.max(0.0)).collect();
        } else {
            current_lower = out_lower;
            current_upper = out_upper;
        }
    }

    result
}

/// Compute gradient of output bound width w.r.t. alpha parameters.
///
/// Uses central finite differences: (f(alpha + eps) - f(alpha - eps)) / (2 * eps).
pub(super) fn compute_alpha_gradient(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input_bounds: &Interval,
    layer_bounds: &[Interval],
    alphas: &AlphaCrownParams,
    epsilon: f64,
) -> Vec<Vec<f64>> {
    let mut grad = Vec::with_capacity(alphas.alphas.len());

    for layer_idx in 0..alphas.alphas.len() {
        let num_neurons = alphas.alphas[layer_idx].len();
        let mut layer_grad = vec![0.0; num_neurons];

        // `neuron_idx` indexes into both `alphas.alphas[layer_idx]` (read)
        // and `layer_grad` (write), so a single-iterator rewrite is not
        // applicable.
        #[allow(clippy::needless_range_loop)]
        for neuron_idx in 0..num_neurons {
            let mut alphas_plus = alphas.clone();
            alphas_plus.alphas[layer_idx][neuron_idx] =
                (alphas.alphas[layer_idx][neuron_idx] + epsilon).min(1.0);

            let plus = backward_pass(weights, biases, input_bounds, layer_bounds, &alphas_plus);
            let plus_width = plus.upper - plus.lower;

            let mut alphas_minus = alphas.clone();
            alphas_minus.alphas[layer_idx][neuron_idx] =
                (alphas.alphas[layer_idx][neuron_idx] - epsilon).max(0.0);

            let minus = backward_pass(weights, biases, input_bounds, layer_bounds, &alphas_minus);
            let minus_width = minus.upper - minus.lower;

            let actual_delta = alphas_plus.alphas[layer_idx][neuron_idx]
                - alphas_minus.alphas[layer_idx][neuron_idx];

            if actual_delta.abs() > 1e-15 {
                layer_grad[neuron_idx] = (plus_width - minus_width) / actual_delta;
            }
        }

        grad.push(layer_grad);
    }

    grad
}

/// Project alpha values to valid range [0, 1].
pub(super) fn project_alphas(alphas: &mut AlphaCrownParams) {
    for layer in &mut alphas.alphas {
        for alpha in layer.iter_mut() {
            *alpha = alpha.clamp(0.0, 1.0);
        }
    }
}
