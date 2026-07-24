// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Combined affine + ReLU operations on zonotopes (T07).
//!
//! Chains the exact affine transformation (T02) with the ReLU
//! overapproximation (T03) to propagate zonotopes through neural network
//! layers. Also provides multi-layer forward pass and comparison against
//! interval bound propagation (IBP) for tightness analysis.

use super::concrete::ConcreteZonotope;
use super::relu::zonotope_relu;

/// Apply an affine transformation y = W * x + b to a zonotope, then ReLU.
///
/// The affine step uses `ConcreteZonotope::linear_transform` (T02, exact).
/// The ReLU step uses lambda-relaxation overapproximation (T03).
///
/// `weight` is row-major: `weight[i]` is row i (length = `z.dim()`).
/// `bias` has length equal to the number of rows in `weight`.
/// Returns a zonotope of dimension `weight.len()`.
#[must_use]
pub fn zonotope_affine_relu(
    z: &ConcreteZonotope,
    weight: &[Vec<f64>],
    bias: &[f64],
) -> ConcreteZonotope {
    let w_refs: Vec<&[f64]> = weight.iter().map(|row| row.as_slice()).collect();
    let affine_z = z.linear_transform(&w_refs, bias);
    zonotope_relu(&affine_z)
}

/// Forward pass through multiple affine+ReLU layers.
///
/// Each layer is a (weight, bias) pair. The zonotope is propagated through
/// each layer sequentially, applying affine transformation then ReLU
/// overapproximation at each step.
#[must_use]
pub fn zonotope_forward_pass(
    z: &ConcreteZonotope,
    layers: &[(Vec<Vec<f64>>, Vec<f64>)],
) -> ConcreteZonotope {
    let mut current = z.clone();
    for (weight, bias) in layers {
        current = zonotope_affine_relu(&current, weight, bias);
    }
    current
}

/// Compare zonotope hull width vs IBP hull width after a forward pass.
///
/// Returns `(zonotope_width, ibp_width)` where each is the sum of
/// per-dimension interval widths at the output. The zonotope width should
/// be less than or equal to the IBP width, since zonotopes track
/// correlations between dimensions that IBP loses.
///
/// IBP is computed by propagating axis-aligned bounding boxes through
/// each layer using W+/W- decomposition.
#[must_use]
pub fn compare_zonotope_ibp(
    z: &ConcreteZonotope,
    layers: &[(Vec<Vec<f64>>, Vec<f64>)],
) -> (f64, f64) {
    // Zonotope forward pass
    let zono_output = zonotope_forward_pass(z, layers);
    let (zono_lo, zono_hi) = zono_output.to_interval();
    let zono_width: f64 = zono_lo
        .iter()
        .zip(zono_hi.iter())
        .map(|(&l, &h)| h - l)
        .sum();

    // IBP forward pass: propagate interval bounds
    let (mut ibp_lo, mut ibp_hi) = z.to_interval();
    for (weight, bias) in layers {
        let (new_lo, new_hi) = ibp_affine_relu(&ibp_lo, &ibp_hi, weight, bias);
        ibp_lo = new_lo;
        ibp_hi = new_hi;
    }
    let ibp_width: f64 = ibp_lo.iter().zip(ibp_hi.iter()).map(|(&l, &h)| h - l).sum();

    (zono_width, ibp_width)
}

/// IBP propagation through one affine + ReLU layer.
///
/// Uses W+/W- decomposition for the affine step, then element-wise
/// interval ReLU. Returns (lower, upper) vectors for the output.
fn ibp_affine_relu(
    lo: &[f64],
    hi: &[f64],
    weight: &[Vec<f64>],
    bias: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    let m = weight.len();
    let mut out_lo = Vec::with_capacity(m);
    let mut out_hi = Vec::with_capacity(m);

    for i in 0..m {
        let mut y_lo = bias[i];
        let mut y_hi = bias[i];
        for (j, &w) in weight[i].iter().enumerate() {
            if w >= 0.0 {
                y_lo += w * lo[j];
                y_hi += w * hi[j];
            } else {
                y_lo += w * hi[j];
                y_hi += w * lo[j];
            }
        }
        // ReLU on interval
        out_lo.push(y_lo.max(0.0));
        out_hi.push(y_hi.max(0.0));
    }

    (out_lo, out_hi)
}
