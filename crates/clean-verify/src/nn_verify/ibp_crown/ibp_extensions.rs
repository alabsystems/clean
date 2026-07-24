// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IBP Extensions: Sigmoid (T83) and Convolutional Layer (T84) Soundness
//!
//! These extend the core IBP specs (T80-T82 in `ibp.rs`) to additional
//! layer types: monotone activations and convolutional operators.

use crate::spec::ProofStatus;

use super::ibp::{IbpLinearSpec, IbpReluSpec, Interval};

// ---------------------------------------------------------------------------
// T83: IBP Sigmoid (Monotone Activation)
// ---------------------------------------------------------------------------

/// Proof specification for T83: IBP sigmoid soundness.
///
/// **Statement:** For any monotonically increasing activation function
/// sigma (sigmoid, tanh, etc.) with sigma' > 0 everywhere,
/// if x in [l, u] then sigma(x) in [sigma(l), sigma(u)].
///
/// **Proof:** Immediate from monotonicity: l <= x <= u implies
/// sigma(l) <= sigma(x) <= sigma(u).
///
/// **Status:** `DerivedPending` -- kernel theorem
/// `NNVerify.ibp_sigmoid_sound` registered as `Declaration::Theorem`
/// with proof term via monotonicity of sigmoid. The proof uses
/// `monotone_preserve_bounds` which derives the interval bound from
/// the monotonicity hypothesis `l <= x <= u => sigma(l) <= sigma(x) <= sigma(u)`.
/// See `nn_verify_ibp_sigmoid.rs` in clean-kernel.
#[derive(Debug)]
pub struct IbpSigmoidSpec {
    status: ProofStatus,
}

impl IbpSigmoidSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }

    /// Propagate an interval through the standard sigmoid: sigma(x) = 1/(1+e^{-x}).
    #[must_use]
    pub fn propagate_sigmoid(&self, input: &Interval) -> Interval {
        let lower = sigmoid(input.lower);
        let upper = sigmoid(input.upper);
        Interval::new(lower, upper)
    }

    /// Propagate an interval through tanh.
    #[must_use]
    pub fn propagate_tanh(&self, input: &Interval) -> Interval {
        let lower = input.lower.tanh();
        let upper = input.upper.tanh();
        Interval::new(lower, upper)
    }

    /// Verify soundness for a concrete value through sigmoid.
    pub fn verify_concrete_sigmoid(&self, input: &Interval, x: f64) -> Result<(), String> {
        if x < input.lower - f64::EPSILON || x > input.upper + f64::EPSILON {
            return Err(format!("x={x} not in input interval"));
        }
        let sigma_x = sigmoid(x);
        let bound = self.propagate_sigmoid(input);
        if sigma_x < bound.lower - f64::EPSILON || sigma_x > bound.upper + f64::EPSILON {
            return Err(format!(
                "sigmoid({x})={sigma_x} not in [{}, {}]",
                bound.lower, bound.upper
            ));
        }
        Ok(())
    }
}

impl Default for IbpSigmoidSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Standard sigmoid function: 1 / (1 + e^{-x}).
fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

// ---------------------------------------------------------------------------
// T84: IBP Conv
// ---------------------------------------------------------------------------

/// Proof specification for T84: IBP convolutional layer soundness.
///
/// **Statement:** A 1D/2D convolutional layer is a structured linear
/// operator. The convolution y = conv(W, x) + b can be represented as
/// y = T(W) * vec(x) + b where T(W) is the Toeplitz (1D) or
/// doubly-block-circulant (2D) matrix. Since T(W) is a real matrix,
/// T80 (IBP linear) applies directly.
///
/// **Proof strategy:** Reduce to T80 by constructing the equivalent
/// Toeplitz matrix and applying IBP linear soundness.
///
/// **Status:** `DerivedPending` -- kernel theorem
/// `NNVerify.ibp_conv_sound` registered as `Declaration::Theorem`.
/// The proof reduces convolution to T80 (IBP linear) by constructing
/// the Toeplitz matrix T(W) such that conv(W, x) = T(W) * x, then
/// directly applying `ibp_linear_sound`.
/// See `nn_verify_ibp_conv.rs` in clean-kernel.
#[derive(Debug)]
pub struct IbpConvSpec {
    status: ProofStatus,
}

impl IbpConvSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }

    /// Construct the Toeplitz matrix for a 1D convolution kernel.
    ///
    /// `kernel` is the convolution filter of length k.
    /// `input_len` is the length of the input signal.
    /// Returns the (input_len - k + 1) x input_len Toeplitz matrix (valid padding).
    #[must_use]
    pub fn toeplitz_1d(&self, kernel: &[f64], input_len: usize) -> Vec<Vec<f64>> {
        let k = kernel.len();
        if k > input_len {
            return Vec::new();
        }
        let output_len = input_len - k + 1;
        let mut matrix = vec![vec![0.0; input_len]; output_len];
        for i in 0..output_len {
            for (j, &w) in kernel.iter().enumerate() {
                matrix[i][i + j] = w;
            }
        }
        matrix
    }

    /// Propagate bounds through a 1D conv layer by reducing to IBP linear.
    #[must_use]
    pub fn propagate_1d(
        &self,
        kernel: &[f64],
        bias: f64,
        input_bounds: &[Interval],
    ) -> Vec<Interval> {
        let toeplitz = self.toeplitz_1d(kernel, input_bounds.len());
        if toeplitz.is_empty() {
            return Vec::new();
        }
        let output_len = toeplitz.len();
        let bias_vec = vec![bias; output_len];
        let linear = IbpLinearSpec::new();
        linear.propagate(&toeplitz, &bias_vec, input_bounds)
    }
}

impl Default for IbpConvSpec {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Batch IBP and Multi-Input Interval Analysis
// ---------------------------------------------------------------------------

/// Result of verifying that all sample outputs fall within IBP bounds.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct BatchSoundnessResult {
    /// Whether all samples are within bounds.
    pub sound: bool,
    /// Number of samples checked.
    pub num_samples: usize,
    /// Indices of samples that violated bounds.
    pub violations: Vec<usize>,
}

/// Result of measuring how output bounds change when input is perturbed.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct SensitivityResult {
    /// Width of the input interval.
    pub input_width: f64,
    /// Width of the output interval.
    pub output_width: f64,
    /// Amplification factor: output_width / input_width.
    pub amplification: f64,
}

/// Run IBP forward pass for multiple input intervals simultaneously.
///
/// Each element of `inputs` is propagated through the network defined by
/// `weights` (layer weight matrices) and `biases` (per-layer bias vectors).
/// Returns one output interval vector per input.
#[must_use]
pub fn batch_ibp_forward(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    inputs: &[Interval],
) -> Vec<Vec<Interval>> {
    inputs
        .iter()
        .map(|input| ibp_forward_single(weights, biases, input))
        .collect()
}

/// Single-input IBP forward pass returning per-layer output intervals.
///
/// Propagates the input interval through each layer (linear + ReLU)
/// and returns the output intervals of each layer.
#[must_use]
pub fn ibp_forward_single(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input: &Interval,
) -> Vec<Interval> {
    let linear = IbpLinearSpec::new();
    let relu = IbpReluSpec::new();
    let num_layers = weights.len().min(biases.len());
    if num_layers == 0 {
        return Vec::new();
    }

    // Start with input broadcast to match first layer's input dimension
    let input_dim = if weights[0].is_empty() {
        0
    } else {
        weights[0][0].len()
    };
    let mut current = vec![*input; input_dim];

    for layer_idx in 0..num_layers {
        let linear_out = linear.propagate(&weights[layer_idx], &biases[layer_idx], &current);
        // Apply ReLU to all layers except the last
        current = if layer_idx < num_layers - 1 {
            relu.propagate_vector(&linear_out)
        } else {
            linear_out
        };
    }
    current
}

/// Compute the convex hull (widest bounds) across multiple input intervals.
///
/// Returns a single interval whose lower bound is the minimum of all lowers
/// and whose upper bound is the maximum of all uppers.
#[must_use]
pub fn multi_input_hull(input_intervals: &[Interval]) -> Interval {
    if input_intervals.is_empty() {
        return Interval::new(0.0, 0.0);
    }
    let lower = input_intervals
        .iter()
        .map(|iv| iv.lower)
        .fold(f64::INFINITY, f64::min);
    let upper = input_intervals
        .iter()
        .map(|iv| iv.upper)
        .fold(f64::NEG_INFINITY, f64::max);
    Interval::new(lower, upper)
}

/// Verify that all sample outputs fall within IBP bounds.
///
/// For each sample (a concrete input vector), computes the network output
/// and checks that it lies within the IBP output interval derived from `input`.
#[must_use]
pub fn verify_batch_soundness(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input: &Interval,
    samples: &[Vec<f64>],
) -> BatchSoundnessResult {
    let output_bounds = ibp_forward_single(weights, biases, input);
    let mut violations = Vec::new();

    for (idx, sample) in samples.iter().enumerate() {
        let concrete_out = evaluate_network(weights, biases, sample);
        if !is_within_bounds(&concrete_out, &output_bounds) {
            violations.push(idx);
        }
    }

    BatchSoundnessResult {
        sound: violations.is_empty(),
        num_samples: samples.len(),
        violations,
    }
}

/// Measure how much output bounds change when input is perturbed by epsilon.
///
/// Compares the output interval width for the original input against
/// the output interval width for the input expanded by epsilon on each side.
#[must_use]
pub fn ibp_sensitivity(
    weights: &[Vec<Vec<f64>>],
    biases: &[Vec<f64>],
    input: &Interval,
    epsilon: f64,
) -> SensitivityResult {
    let original_out = ibp_forward_single(weights, biases, input);
    let perturbed = Interval::new(input.lower - epsilon, input.upper + epsilon);
    let perturbed_out = ibp_forward_single(weights, biases, &perturbed);

    let original_width: f64 = original_out.iter().map(|iv| iv.width()).sum();
    let perturbed_width: f64 = perturbed_out.iter().map(|iv| iv.width()).sum();

    let input_width = input.width();
    let output_width_delta = perturbed_width - original_width;
    let amplification = if input_width.abs() < f64::EPSILON {
        if output_width_delta.abs() < f64::EPSILON {
            0.0
        } else {
            f64::INFINITY
        }
    } else {
        output_width_delta / (2.0 * epsilon)
    };

    SensitivityResult {
        input_width,
        output_width: perturbed_width,
        amplification,
    }
}

/// Evaluate a neural network on a concrete input vector.
fn evaluate_network(weights: &[Vec<Vec<f64>>], biases: &[Vec<f64>], input: &[f64]) -> Vec<f64> {
    let num_layers = weights.len().min(biases.len());
    if num_layers == 0 {
        return Vec::new();
    }
    let mut current = input.to_vec();
    for layer_idx in 0..num_layers {
        let w = &weights[layer_idx];
        let b = &biases[layer_idx];
        let mut next = Vec::with_capacity(w.len());
        for (i, row) in w.iter().enumerate() {
            let mut val = b.get(i).copied().unwrap_or(0.0);
            for (j, &wij) in row.iter().enumerate() {
                val += wij * current.get(j).copied().unwrap_or(0.0);
            }
            // ReLU for all but last layer
            if layer_idx < num_layers - 1 {
                val = val.max(0.0);
            }
            next.push(val);
        }
        current = next;
    }
    current
}

/// Check if concrete outputs fall within interval bounds.
fn is_within_bounds(concrete: &[f64], bounds: &[Interval]) -> bool {
    if concrete.len() != bounds.len() {
        return false;
    }
    concrete
        .iter()
        .zip(bounds.iter())
        .all(|(&val, bound)| val >= bound.lower - f64::EPSILON && val <= bound.upper + f64::EPSILON)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- T83: IBP Sigmoid ----

    #[test]
    fn test_ibp_sigmoid_unit_interval() {
        let spec = IbpSigmoidSpec::new();
        let input = Interval::new(-2.0, 2.0);
        let output = spec.propagate_sigmoid(&input);
        // sigmoid(-2) ~ 0.1192, sigmoid(2) ~ 0.8808
        assert!(output.lower > 0.11);
        assert!(output.lower < 0.13);
        assert!(output.upper > 0.87);
        assert!(output.upper < 0.89);
    }

    #[test]
    fn test_ibp_sigmoid_monotonicity_preserved() {
        let spec = IbpSigmoidSpec::new();
        let narrow = Interval::new(0.0, 1.0);
        let wide = Interval::new(-1.0, 2.0);
        let out_narrow = spec.propagate_sigmoid(&narrow);
        let out_wide = spec.propagate_sigmoid(&wide);
        assert!(out_wide.lower <= out_narrow.lower + f64::EPSILON);
        assert!(out_wide.upper >= out_narrow.upper - f64::EPSILON);
    }

    #[test]
    fn test_ibp_sigmoid_verify_concrete() {
        let spec = IbpSigmoidSpec::new();
        let input = Interval::new(-3.0, 3.0);
        spec.verify_concrete_sigmoid(&input, 0.0)
            .expect("sigmoid(0) = 0.5 should be in bounds");
        spec.verify_concrete_sigmoid(&input, -2.0)
            .expect("sigmoid(-2) should be in bounds");
        spec.verify_concrete_sigmoid(&input, 2.5)
            .expect("sigmoid(2.5) should be in bounds");
    }

    #[test]
    fn test_ibp_tanh_propagation() {
        let spec = IbpSigmoidSpec::new();
        let input = Interval::new(-1.0, 1.0);
        let output = spec.propagate_tanh(&input);
        assert!(output.lower > -0.77);
        assert!(output.lower < -0.75);
        assert!(output.upper > 0.75);
        assert!(output.upper < 0.77);
    }

    #[test]
    fn test_ibp_sigmoid_status() {
        let spec = IbpSigmoidSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
    }

    // ---- T84: IBP Conv ----

    #[test]
    fn test_ibp_conv_toeplitz_construction() {
        let spec = IbpConvSpec::new();
        let kernel = vec![1.0, 2.0, 3.0];
        let matrix = spec.toeplitz_1d(&kernel, 5);
        assert_eq!(matrix.len(), 3);
        assert_eq!(matrix[0].len(), 5);
        assert!((matrix[0][0] - 1.0).abs() < 1e-10);
        assert!((matrix[0][1] - 2.0).abs() < 1e-10);
        assert!((matrix[0][2] - 3.0).abs() < 1e-10);
        assert!((matrix[0][3]).abs() < 1e-10);
        assert!((matrix[1][0]).abs() < 1e-10);
        assert!((matrix[1][1] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_ibp_conv_propagate_1d() {
        let spec = IbpConvSpec::new();
        let kernel = vec![1.0, -1.0];
        let bias = 0.0;
        let input = vec![
            Interval::new(0.0, 1.0),
            Interval::new(0.0, 1.0),
            Interval::new(0.0, 1.0),
        ];
        let output = spec.propagate_1d(&kernel, bias, &input);
        assert_eq!(output.len(), 2);
        assert!((output[0].lower - (-1.0)).abs() < 1e-10);
        assert!((output[0].upper - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_ibp_conv_kernel_larger_than_input() {
        let spec = IbpConvSpec::new();
        let kernel = vec![1.0, 2.0, 3.0, 4.0];
        let input = vec![Interval::new(0.0, 1.0), Interval::new(0.0, 1.0)];
        let output = spec.propagate_1d(&kernel, 0.0, &input);
        assert!(output.is_empty(), "kernel > input should give empty output");
    }

    #[test]
    fn test_ibp_conv_status() {
        let spec = IbpConvSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
    }
}
