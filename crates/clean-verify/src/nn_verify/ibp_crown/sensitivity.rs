// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IBP Batch Sensitivity Analysis
//!
//! Analyzes how input perturbations affect output bounds through interval
//! bound propagation. Provides tools for identifying critical neurons,
//! measuring bound tightness, and estimating worst-case amplification
//! through network layers.
//!
//! ## Key Concepts
//!
//! - **Input sensitivity:** Jacobian norm estimate per output neuron,
//!   measuring how much each output bound can change per unit of input
//!   perturbation.
//! - **Layer amplification:** Worst-case factor by which a linear layer
//!   amplifies interval widths (spectral norm proxy via row L1 norms).
//! - **ReLU tightness:** Fraction of neurons with determined sign, where
//!   tighter bounds (fewer crossing neurons) yield more precise analysis.
//! - **Critical neurons:** Crossing neurons with large interval widths,
//!   which dominate bound looseness and are prime targets for refinement.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use super::ibp::Interval;

/// Statistics on interval bound widths across a layer.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct BoundWidthStats {
    /// Minimum width across all intervals.
    pub min: f64,
    /// Maximum width across all intervals.
    pub max: f64,
    /// Mean width across all intervals.
    pub mean: f64,
    /// Median width across all intervals.
    pub median: f64,
    /// Number of intervals.
    pub count: usize,
}

/// Per-output sensitivity to input perturbations.
///
/// For each output neuron i, computes the sum of absolute weights
/// multiplied by input interval widths: `sum_j |W[i][j]| * width(input_j)`.
/// This is a Jacobian-norm estimate bounding how much the output interval
/// can widen per unit of input perturbation.
///
/// # Panics
///
/// Debug-asserts that each weight row has the same length as `input_bounds`.
#[must_use]
pub(crate) fn input_sensitivity(weights: &[Vec<f64>], input_bounds: &[Interval]) -> Vec<f64> {
    weights
        .iter()
        .map(|row| {
            debug_assert_eq!(
                row.len(),
                input_bounds.len(),
                "weight row length must match input_bounds length"
            );
            row.iter()
                .zip(input_bounds.iter())
                .map(|(w, bound)| w.abs() * bound.width())
                .sum()
        })
        .collect()
}

/// Worst-case bound amplification factor through a linear layer.
///
/// Returns the maximum L1-norm of the weight matrix rows, which bounds
/// how much a unit-width input interval can be amplified in any single
/// output dimension. For an identity matrix this is 1.0.
///
/// Returns 0.0 for an empty weight matrix.
#[must_use]
pub(crate) fn layer_amplification_factor(weights: &[Vec<f64>]) -> f64 {
    weights
        .iter()
        .map(|row| row.iter().map(|w| w.abs()).sum::<f64>())
        .fold(0.0_f64, f64::max)
}

/// Fraction of neurons with determined sign (not crossing zero).
///
/// A neuron with bounds `[l, u]` is "tight" if `l >= 0` (always active)
/// or `u <= 0` (always inactive). Crossing neurons (`l < 0 < u`) introduce
/// bound looseness. Returns 1.0 when all neurons have determined sign,
/// 0.0 when all are crossing.
///
/// Returns 1.0 for empty bounds (vacuously all tight).
#[must_use]
pub(crate) fn relu_tightness_ratio(bounds: &[Interval]) -> f64 {
    if bounds.is_empty() {
        return 1.0;
    }
    let tight_count = bounds
        .iter()
        .filter(|b| b.lower >= 0.0 || b.upper <= 0.0)
        .count();
    tight_count as f64 / bounds.len() as f64
}

/// Product of per-layer sensitivity factors.
///
/// Composition of layers amplifies bounds multiplicatively: if layer i
/// amplifies by factor s_i, the composed network amplifies by the product
/// of all s_i. Returns 1.0 for an empty slice (identity composition).
#[must_use]
pub(crate) fn composition_sensitivity(layer_sensitivities: &[f64]) -> f64 {
    layer_sensitivities.iter().product()
}

/// Indices of crossing neurons with interval width above `threshold`.
///
/// A crossing neuron has `lower < 0 < upper`. Among these, neurons with
/// large widths dominate the looseness of ReLU relaxation and are prime
/// targets for branch-and-bound refinement or CROWN alpha optimization.
#[must_use]
pub(crate) fn identify_critical_neurons(bounds: &[Interval], threshold: f64) -> Vec<usize> {
    bounds
        .iter()
        .enumerate()
        .filter(|(_, b)| b.lower < 0.0 && b.upper > 0.0 && b.width() > threshold)
        .map(|(i, _)| i)
        .collect()
}

/// Compute min, max, mean, and median width statistics over interval bounds.
///
/// Returns `None` if `bounds` is empty (statistics are undefined).
#[must_use]
pub(crate) fn bound_width_statistics(bounds: &[Interval]) -> Option<BoundWidthStats> {
    if bounds.is_empty() {
        return None;
    }

    let mut widths: Vec<f64> = bounds.iter().map(Interval::width).collect();

    let min = widths.iter().copied().fold(f64::INFINITY, f64::min);
    let max = widths.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    let mean = widths.iter().sum::<f64>() / widths.len() as f64;

    widths.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let median = if widths.len() % 2 == 1 {
        widths[widths.len() / 2]
    } else {
        (widths[widths.len() / 2 - 1] + widths[widths.len() / 2]) / 2.0
    };

    Some(BoundWidthStats {
        min,
        max,
        mean,
        median,
        count: bounds.len(),
    })
}
