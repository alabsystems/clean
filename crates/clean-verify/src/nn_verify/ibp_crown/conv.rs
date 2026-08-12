// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Convolutional Layer IBP Soundness (T84a-T84c)
//!
//! Dedicated module for 2D convolutional layer interval bound propagation.
//! A convolution is a structured linear operator; im2col reduces it to a
//! matrix multiply so that T80 (IBP linear) applies directly.
//!
//! ## Theorems
//!
//! - **T84a (Conv IBP sound):** IBP forward through conv produces sound bounds.
//! - **T84b (Conv-linear equiv):** For small inputs, conv IBP matches
//!   the expanded Toeplitz-like linear matrix applied via T80.
//! - **T84c (Conv Lipschitz):** Upper bound on the Lipschitz constant of a
//!   conv layer via the spectral norm of the expanded matrix.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use crate::spec::ProofStatus;

use super::ibp::{IbpLinearSpec, Interval};

/// T84a: Conv IBP forward soundness.
///
/// **Status:** `DerivedPending` -- kernel theorem `NNVerify.conv_ibp_sound`
/// registered as `Declaration::Theorem`. The proof constructs the im2col
/// column extraction, reduces to the W+/W- decomposition of T80 applied
/// per-column, and uses `ibp_linear_sound` on the unrolled operator.
/// Each output position is proved sound independently via the same
/// interval arithmetic argument as T80. See `nn_verify_ibp_conv.rs`
/// in clean-kernel.
pub const T84A_CONV_IBP_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T84b: Conv-linear equivalence.
///
/// **Status:** `DerivedPending` -- kernel theorem `NNVerify.conv_linear_equiv`
/// registered as `Declaration::Theorem`. The proof shows that
/// `conv_forward_interval(x)` produces identical bounds to
/// `ibp_linear(T(W), vec(x))` where T(W) is the Toeplitz expansion.
/// By structural induction on spatial positions: im2col extracts the
/// same patches as the Toeplitz matrix rows, so the dot products are
/// identical. See `nn_verify_ibp_conv.rs` in clean-kernel.
pub const T84B_CONV_LINEAR_EQUIV: ProofStatus = ProofStatus::DerivedPending;

/// T84c: Conv Lipschitz bound.
///
/// **Status:** `DerivedPending` -- kernel theorem `NNVerify.conv_lipschitz`
/// registered as `Declaration::Theorem`. The proof uses the Frobenius norm
/// inequality: ||A||_2 <= ||A||_F for any matrix A. Applied to the
/// Toeplitz expansion T(W), the Frobenius norm is computable from
/// the kernel weights. Combined with `lipschitz_compose` (T30), this
/// bounds the Lipschitz constant of the conv layer.
/// See `nn_verify_ibp_conv.rs` in clean-kernel.
pub const T84C_CONV_LIPSCHITZ: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Data structures
// ---------------------------------------------------------------------------

/// Parameters describing a 2D convolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvParams {
    pub kernel_height: usize,
    pub kernel_width: usize,
    pub in_channels: usize,
    pub out_channels: usize,
    pub stride_h: usize,
    pub stride_w: usize,
    pub pad_h: usize,
    pub pad_w: usize,
}

/// Convolution kernel weights and bias.
///
/// `kernel` is indexed `[out_ch][in_ch][kh][kw]`. `bias` has length
/// `out_channels` (one per output channel).
#[derive(Debug, Clone)]
pub struct ConvWeight {
    pub kernel: Vec<Vec<Vec<Vec<f64>>>>,
    pub bias: Vec<f64>,
}

/// Multi-dimensional interval tensor stored as a flat `Vec<Interval>` with
/// shape metadata.  Layout is row-major: `[H][W][C]` maps to index
/// `(h * width + w) * channels + c`.
#[derive(Debug, Clone)]
pub struct IntervalTensor {
    pub data: Vec<Interval>,
    pub height: usize,
    pub width: usize,
    pub channels: usize,
}

impl IntervalTensor {
    /// Create a new interval tensor.  Panics in debug mode if sizes disagree.
    #[must_use]
    pub fn new(data: Vec<Interval>, height: usize, width: usize, channels: usize) -> Self {
        debug_assert_eq!(
            data.len(),
            height * width * channels,
            "data length must equal H*W*C"
        );
        Self {
            data,
            height,
            width,
            channels,
        }
    }

    /// Index into the tensor: `(h, w, c)`.
    #[must_use]
    pub fn get(&self, h: usize, w: usize, c: usize) -> &Interval {
        &self.data[(h * self.width + w) * self.channels + c]
    }

    /// Total number of elements.
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Whether the tensor is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Output shape
// ---------------------------------------------------------------------------

/// Compute the output spatial dimensions for a 2D convolution.
///
/// Returns `(out_h, out_w)`.
#[must_use]
pub fn compute_output_shape(in_h: usize, in_w: usize, params: &ConvParams) -> (usize, usize) {
    let out_h = (in_h + 2 * params.pad_h - params.kernel_height) / params.stride_h + 1;
    let out_w = (in_w + 2 * params.pad_w - params.kernel_width) / params.stride_w + 1;
    (out_h, out_w)
}

// ---------------------------------------------------------------------------
// im2col for intervals
// ---------------------------------------------------------------------------

/// Extract im2col columns from an interval tensor.
///
/// Each output column corresponds to one spatial output position and contains
/// `in_channels * kernel_height * kernel_width` interval entries.  Padded
/// positions use the zero point interval `[0, 0]`.
///
/// Returns a vector of columns (each column is a `Vec<Interval>`), with
/// `out_h * out_w` columns total.
#[must_use]
pub fn im2col_intervals(input: &IntervalTensor, params: &ConvParams) -> Vec<Vec<Interval>> {
    let (out_h, out_w) = compute_output_shape(input.height, input.width, params);
    let col_len = params.in_channels * params.kernel_height * params.kernel_width;
    let zero = Interval::point(0.0);

    let mut columns = Vec::with_capacity(out_h * out_w);
    for oh in 0..out_h {
        for ow in 0..out_w {
            let mut col = Vec::with_capacity(col_len);
            for ic in 0..params.in_channels {
                for kh in 0..params.kernel_height {
                    for kw in 0..params.kernel_width {
                        let ih = oh * params.stride_h + kh;
                        let iw = ow * params.stride_w + kw;
                        // Account for padding: subtract pad offset.
                        let ih = ih as isize - params.pad_h as isize;
                        let iw = iw as isize - params.pad_w as isize;
                        if ih >= 0
                            && (ih as usize) < input.height
                            && iw >= 0
                            && (iw as usize) < input.width
                        {
                            col.push(*input.get(ih as usize, iw as usize, ic));
                        } else {
                            col.push(zero);
                        }
                    }
                }
            }
            columns.push(col);
        }
    }
    columns
}

// ---------------------------------------------------------------------------
// IBP forward pass through conv
// ---------------------------------------------------------------------------

/// IBP forward pass through a 2D convolutional layer.
///
/// Uses the W+/W- decomposition from T80 applied via im2col.  For each
/// output channel and each spatial position, we compute interval bounds
/// using the positive/negative weight decomposition.
#[must_use]
pub fn conv_forward_interval(
    input: &IntervalTensor,
    weight: &ConvWeight,
    params: &ConvParams,
) -> IntervalTensor {
    let (out_h, out_w) = compute_output_shape(input.height, input.width, params);
    let columns = im2col_intervals(input, params);
    let col_len = params.in_channels * params.kernel_height * params.kernel_width;

    let mut out_data = Vec::with_capacity(out_h * out_w * params.out_channels);
    for (col_idx, col) in columns.iter().enumerate() {
        let _ = col_idx; // used implicitly via iteration order
        for oc in 0..params.out_channels {
            // Flatten the kernel for this output channel to match the column.
            let mut lower = weight.bias[oc];
            let mut upper = weight.bias[oc];
            let mut k = 0;
            for ic in 0..params.in_channels {
                for kh in 0..params.kernel_height {
                    for kw in 0..params.kernel_width {
                        let w = weight.kernel[oc][ic][kh][kw];
                        let iv = &col[k];
                        if w >= 0.0 {
                            lower += w * iv.lower;
                            upper += w * iv.upper;
                        } else {
                            lower += w * iv.upper;
                            upper += w * iv.lower;
                        }
                        k += 1;
                    }
                }
            }
            debug_assert_eq!(k, col_len);
            out_data.push(Interval::new(lower, upper));
        }
    }
    IntervalTensor::new(out_data, out_h, out_w, params.out_channels)
}

// ---------------------------------------------------------------------------
// Soundness verification
// ---------------------------------------------------------------------------

/// Verify that for a concrete input within `input_bounds`, the concrete
/// convolution output falls within the IBP output bounds.
///
/// `concrete` is a flat `[H][W][C]` vector of concrete values.
pub fn verify_conv_ibp_sound(
    input_bounds: &IntervalTensor,
    concrete: &[f64],
    weight: &ConvWeight,
    params: &ConvParams,
) -> Result<(), String> {
    // Check concrete input is within bounds.
    if concrete.len() != input_bounds.len() {
        return Err(format!(
            "concrete length {} != bounds length {}",
            concrete.len(),
            input_bounds.len()
        ));
    }
    for (i, (val, iv)) in concrete.iter().zip(input_bounds.data.iter()).enumerate() {
        if *val < iv.lower - f64::EPSILON || *val > iv.upper + f64::EPSILON {
            return Err(format!(
                "concrete[{i}]={val} not in [{}, {}]",
                iv.lower, iv.upper
            ));
        }
    }

    let ibp_out = conv_forward_interval(input_bounds, weight, params);

    // Compute concrete convolution.
    let (out_h, out_w) = compute_output_shape(input_bounds.height, input_bounds.width, params);
    let in_h = input_bounds.height;
    let in_w = input_bounds.width;
    let ic_count = params.in_channels;

    for oh in 0..out_h {
        for ow in 0..out_w {
            for oc in 0..params.out_channels {
                let mut val = weight.bias[oc];
                for ic in 0..ic_count {
                    for kh in 0..params.kernel_height {
                        for kw in 0..params.kernel_width {
                            let ih = (oh * params.stride_h + kh) as isize - params.pad_h as isize;
                            let iw = (ow * params.stride_w + kw) as isize - params.pad_w as isize;
                            if ih >= 0 && (ih as usize) < in_h && iw >= 0 && (iw as usize) < in_w {
                                let idx = (ih as usize * in_w + iw as usize) * ic_count + ic;
                                val += weight.kernel[oc][ic][kh][kw] * concrete[idx];
                            }
                        }
                    }
                }
                let bound = ibp_out.get(oh, ow, oc);
                if val < bound.lower - f64::EPSILON || val > bound.upper + f64::EPSILON {
                    return Err(format!(
                        "output[{oh},{ow},{oc}]={val} not in [{}, {}]",
                        bound.lower, bound.upper
                    ));
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Conv-to-linear expansion
// ---------------------------------------------------------------------------

/// Expand a 2D convolution to its equivalent dense matrix for small inputs.
///
/// The returned matrix has shape `(out_h*out_w*out_ch, in_h*in_w*in_ch)`.
/// Bias vector has length `out_h*out_w*out_ch`.
#[must_use]
pub fn conv_to_linear_matrix(
    in_h: usize,
    in_w: usize,
    weight: &ConvWeight,
    params: &ConvParams,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let (out_h, out_w) = compute_output_shape(in_h, in_w, params);
    let in_size = in_h * in_w * params.in_channels;
    let out_size = out_h * out_w * params.out_channels;

    let mut matrix = vec![vec![0.0; in_size]; out_size];
    let mut bias = Vec::with_capacity(out_size);

    for oh in 0..out_h {
        for ow in 0..out_w {
            for oc in 0..params.out_channels {
                let out_idx = (oh * out_w + ow) * params.out_channels + oc;
                bias.push(weight.bias[oc]);
                for ic in 0..params.in_channels {
                    for kh in 0..params.kernel_height {
                        for kw in 0..params.kernel_width {
                            let ih = (oh * params.stride_h + kh) as isize - params.pad_h as isize;
                            let iw = (ow * params.stride_w + kw) as isize - params.pad_w as isize;
                            if ih >= 0 && (ih as usize) < in_h && iw >= 0 && (iw as usize) < in_w {
                                let in_idx =
                                    (ih as usize * in_w + iw as usize) * params.in_channels + ic;
                                matrix[out_idx][in_idx] = weight.kernel[oc][ic][kh][kw];
                            }
                        }
                    }
                }
            }
        }
    }
    (matrix, bias)
}

/// Verify that `conv_forward_interval` matches IBP linear applied to the
/// expanded matrix, for small inputs.
pub fn verify_conv_linear_equivalence(
    input: &IntervalTensor,
    weight: &ConvWeight,
    params: &ConvParams,
) -> Result<(), String> {
    let conv_out = conv_forward_interval(input, weight, params);
    let (matrix, bias) = conv_to_linear_matrix(input.height, input.width, weight, params);
    let linear = IbpLinearSpec::new();
    let linear_out = linear.propagate(&matrix, &bias, &input.data);

    if conv_out.data.len() != linear_out.len() {
        return Err(format!(
            "output size mismatch: conv={} vs linear={}",
            conv_out.data.len(),
            linear_out.len()
        ));
    }
    for (i, (c, l)) in conv_out.data.iter().zip(linear_out.iter()).enumerate() {
        if (c.lower - l.lower).abs() > 1e-9 || (c.upper - l.upper).abs() > 1e-9 {
            return Err(format!(
                "mismatch at {i}: conv=[{}, {}] vs linear=[{}, {}]",
                c.lower, c.upper, l.lower, l.upper
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Depthwise convolution
// ---------------------------------------------------------------------------

/// Depthwise separable convolution: each input channel is convolved with its
/// own kernel independently.
///
/// `weight.kernel` must have shape `[channels][1][kh][kw]` and
/// `params.in_channels == params.out_channels`.  `weight.bias` has length
/// `channels`.
#[must_use]
pub fn depthwise_conv_interval(
    input: &IntervalTensor,
    weight: &ConvWeight,
    params: &ConvParams,
) -> IntervalTensor {
    debug_assert_eq!(params.in_channels, params.out_channels);
    let (out_h, out_w) = compute_output_shape(input.height, input.width, params);
    let channels = params.in_channels;

    let mut out_data = Vec::with_capacity(out_h * out_w * channels);
    for oh in 0..out_h {
        for ow in 0..out_w {
            for ch in 0..channels {
                let mut lower = weight.bias[ch];
                let mut upper = weight.bias[ch];
                for kh in 0..params.kernel_height {
                    for kw in 0..params.kernel_width {
                        let ih = (oh * params.stride_h + kh) as isize - params.pad_h as isize;
                        let iw = (ow * params.stride_w + kw) as isize - params.pad_w as isize;
                        let iv = if ih >= 0
                            && (ih as usize) < input.height
                            && iw >= 0
                            && (iw as usize) < input.width
                        {
                            *input.get(ih as usize, iw as usize, ch)
                        } else {
                            Interval::point(0.0)
                        };
                        let w = weight.kernel[ch][0][kh][kw];
                        if w >= 0.0 {
                            lower += w * iv.lower;
                            upper += w * iv.upper;
                        } else {
                            lower += w * iv.upper;
                            upper += w * iv.lower;
                        }
                    }
                }
                out_data.push(Interval::new(lower, upper));
            }
        }
    }
    IntervalTensor::new(out_data, out_h, out_w, channels)
}

// ---------------------------------------------------------------------------
// Lipschitz bound
// ---------------------------------------------------------------------------

/// Upper bound on the Lipschitz constant of a conv layer.
///
/// Uses the Frobenius norm of the expanded linear matrix as a simple
/// (but loose) upper bound on the spectral norm.
#[must_use]
pub fn conv_lipschitz_bound(
    in_h: usize,
    in_w: usize,
    weight: &ConvWeight,
    params: &ConvParams,
) -> f64 {
    let (matrix, _bias) = conv_to_linear_matrix(in_h, in_w, weight, params);
    // Frobenius norm: sqrt(sum of squares of all entries).
    let frob_sq: f64 = matrix
        .iter()
        .flat_map(|row| row.iter())
        .map(|v| v * v)
        .sum();
    frob_sq.sqrt()
}
