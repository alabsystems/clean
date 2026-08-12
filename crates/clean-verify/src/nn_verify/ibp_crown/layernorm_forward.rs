// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete LayerNorm bound computation using tuple-based interval representation.
//!
//! This module provides functions for propagating interval bounds through
//! LayerNorm using `(f64, f64)` tuples for per-component intervals.
//! Each tuple `(lo, hi)` represents the interval `[lo, hi]`.
//!
//! The full LayerNorm pipeline is:
//!   1. Compute mean interval
//!   2. Center each component by subtracting mean
//!   3. Compute variance interval from centered bounds
//!   4. Compute inverse-sqrt interval for normalization
//!   5. Scale and shift: gamma * normalized + beta
//!
//! All functions use conservative (sound) interval arithmetic:
//! computed bounds always contain the true output for any input
//! within the given bounds.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

/// Default epsilon for LayerNorm numerical stability.
#[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
const DEFAULT_EPS: f64 = 1e-5;

// ---------------------------------------------------------------------------
// Step 1: Mean interval
// ---------------------------------------------------------------------------

/// Compute interval bounds on the mean of a vector with per-component bounds.
///
/// Since `mean(x) = (1/n) * sum(x_i)` is linear, interval arithmetic is exact:
/// - `mean_lower = sum(lowers) / n`
/// - `mean_upper = sum(uppers) / n`
///
/// # Panics
///
/// Debug-asserts that `bounds` is non-empty.
#[must_use]
pub fn compute_mean_interval(bounds: &[(f64, f64)]) -> (f64, f64) {
    let n = bounds.len();
    debug_assert!(n > 0, "bounds must be non-empty");

    let inv_n = 1.0 / n as f64;
    let sum_lo: f64 = bounds.iter().map(|&(lo, _)| lo).sum();
    let sum_hi: f64 = bounds.iter().map(|&(_, hi)| hi).sum();
    (sum_lo * inv_n, sum_hi * inv_n)
}

// ---------------------------------------------------------------------------
// Step 2: Centered bounds
// ---------------------------------------------------------------------------

/// Subtract the mean interval from each component interval to get centered bounds.
///
/// For component `i`:
/// - `centered_lo[i] = bounds[i].lo - mean_hi` (smallest value minus largest mean)
/// - `centered_hi[i] = bounds[i].hi - mean_lo` (largest value minus smallest mean)
///
/// This is exact interval arithmetic for subtraction.
#[must_use]
pub fn compute_centered_bounds(bounds: &[(f64, f64)], mean_bounds: (f64, f64)) -> Vec<(f64, f64)> {
    bounds
        .iter()
        .map(|&(lo, hi)| (lo - mean_bounds.1, hi - mean_bounds.0))
        .collect()
}

// ---------------------------------------------------------------------------
// Step 3: Variance interval
// ---------------------------------------------------------------------------

/// Compute interval bounds on variance = `(1/n) * sum(x_i^2)` where each `x_i`
/// has centered interval bounds.
///
/// For squaring an interval `[a, b]`:
/// - If `a >= 0`: `[a, b]^2 = [a^2, b^2]`
/// - If `b <= 0`: `[a, b]^2 = [b^2, a^2]`
/// - If `a < 0 < b`: `[a, b]^2 = [0, max(a^2, b^2)]`
///
/// The variance lower bound is `(1/n) * sum(sq_lo_i)` and the upper bound
/// is `(1/n) * sum(sq_hi_i)`.
#[must_use]
pub fn compute_variance_interval(centered: &[(f64, f64)]) -> (f64, f64) {
    let n = centered.len();
    debug_assert!(n > 0, "centered bounds must be non-empty");

    let inv_n = 1.0 / n as f64;
    let mut sum_sq_lo = 0.0;
    let mut sum_sq_hi = 0.0;

    for &(lo, hi) in centered {
        let (sq_lo, sq_hi) = square_interval(lo, hi);
        sum_sq_lo += sq_lo;
        sum_sq_hi += sq_hi;
    }

    (sum_sq_lo * inv_n, sum_sq_hi * inv_n)
}

/// Compute the interval of `x^2` given `x` in `[lo, hi]`.
#[must_use]
fn square_interval(lo: f64, hi: f64) -> (f64, f64) {
    if lo >= 0.0 {
        // Both non-negative: squaring preserves order
        (lo * lo, hi * hi)
    } else if hi <= 0.0 {
        // Both non-positive: squaring reverses order
        (hi * hi, lo * lo)
    } else {
        // Interval straddles zero: minimum square is 0
        (0.0, lo.abs().max(hi.abs()).powi(2))
    }
}

// ---------------------------------------------------------------------------
// Step 4: Inverse sqrt interval
// ---------------------------------------------------------------------------

/// Compute interval bounds on `1 / sqrt(var + epsilon)`.
///
/// Since `1/sqrt(x)` is monotonically decreasing for `x > 0`:
/// - `inv_sqrt_lo = 1 / sqrt(var_hi + epsilon)` (larger variance -> smaller scale)
/// - `inv_sqrt_hi = 1 / sqrt(var_lo + epsilon)` (smaller variance -> larger scale)
///
/// # Panics
///
/// Debug-asserts that `var_bounds.0 + epsilon > 0` (required for sqrt domain).
#[must_use]
pub fn compute_inv_sqrt_interval(var_bounds: (f64, f64), epsilon: f64) -> (f64, f64) {
    let lo_arg = var_bounds.0 + epsilon;
    let hi_arg = var_bounds.1 + epsilon;
    debug_assert!(lo_arg > 0.0, "var_lo + epsilon must be positive");
    debug_assert!(hi_arg > 0.0, "var_hi + epsilon must be positive");

    // 1/sqrt is monotonically decreasing on (0, inf)
    let inv_sqrt_lo = 1.0 / hi_arg.sqrt();
    let inv_sqrt_hi = 1.0 / lo_arg.sqrt();
    (inv_sqrt_lo, inv_sqrt_hi)
}

// ---------------------------------------------------------------------------
// Step 5: Full LayerNorm forward pass
// ---------------------------------------------------------------------------

/// Full LayerNorm forward pass with IBP bounds.
///
/// Computes conservative output bounds for:
///   `LayerNorm(x)_i = gamma_i * (x_i - mean(x)) / sqrt(var(x) + eps) + beta_i`
///
/// Pipeline:
///   1. Mean interval (linear, exact)
///   2. Center each component
///   3. Variance interval from centered bounds
///   4. Inverse-sqrt interval for normalization factor
///   5. For each component: multiply centered by inv_sqrt, then scale by gamma + beta
///
/// # Panics
///
/// Debug-asserts that `input_bounds`, `gamma`, and `beta` have equal, nonzero length.
#[must_use]
pub fn layernorm_forward_bounds(
    input_bounds: &[(f64, f64)],
    gamma: &[f64],
    beta: &[f64],
    epsilon: f64,
) -> Vec<(f64, f64)> {
    let n = input_bounds.len();
    debug_assert!(n > 0, "input dimension must be nonzero");
    debug_assert_eq!(n, gamma.len(), "gamma length must match input");
    debug_assert_eq!(n, beta.len(), "beta length must match input");

    // Step 1: Mean interval
    let mean_bounds = compute_mean_interval(input_bounds);

    // Step 2: Center
    let centered = compute_centered_bounds(input_bounds, mean_bounds);

    // Step 3: Variance interval
    let var_bounds = compute_variance_interval(&centered);

    // Step 4: Inverse sqrt interval
    let inv_sqrt = compute_inv_sqrt_interval(var_bounds, epsilon);

    // Step 5: For each component, compute normalized * gamma + beta
    let mut output = Vec::with_capacity(n);
    for i in 0..n {
        let (c_lo, c_hi) = centered[i];

        // Multiply centered interval by inv_sqrt interval
        let products = [
            c_lo * inv_sqrt.0,
            c_lo * inv_sqrt.1,
            c_hi * inv_sqrt.0,
            c_hi * inv_sqrt.1,
        ];
        let norm_lo = products.iter().copied().fold(f64::INFINITY, f64::min);
        let norm_hi = products.iter().copied().fold(f64::NEG_INFINITY, f64::max);

        // Affine: gamma_i * normalized_i + beta_i
        let g = gamma[i];
        let (out_lo, out_hi) = if g >= 0.0 {
            (g * norm_lo + beta[i], g * norm_hi + beta[i])
        } else {
            (g * norm_hi + beta[i], g * norm_lo + beta[i])
        };

        output.push((out_lo, out_hi));
    }

    output
}

// ---------------------------------------------------------------------------
// Step 6: Containment verification
// ---------------------------------------------------------------------------

/// Verify that a concrete input produces a LayerNorm output within given bounds.
///
/// Computes the exact LayerNorm output for `input` using the given `gamma`,
/// `beta`, and `epsilon`, then checks that each output component falls within
/// the corresponding interval in `output_bounds`.
///
/// Returns `true` if every output component is contained in its bound interval.
///
/// # Panics
///
/// Debug-asserts that all slices have equal, nonzero length.
#[must_use]
pub fn verify_layernorm_containment(
    input: &[f64],
    output_bounds: &[(f64, f64)],
    gamma: &[f64],
    beta: &[f64],
    epsilon: f64,
) -> bool {
    let n = input.len();
    debug_assert!(n > 0, "input must be non-empty");
    debug_assert_eq!(n, output_bounds.len());
    debug_assert_eq!(n, gamma.len());
    debug_assert_eq!(n, beta.len());

    // Compute exact LayerNorm
    let inv_n = 1.0 / n as f64;
    let mean: f64 = input.iter().sum::<f64>() * inv_n;
    let var: f64 = input.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() * inv_n;
    let inv_sigma = 1.0 / (var + epsilon).sqrt();

    for i in 0..n {
        let normalized = (input[i] - mean) * inv_sigma;
        let output = gamma[i] * normalized + beta[i];
        let (lo, hi) = output_bounds[i];
        // Use small tolerance for floating-point comparison
        if output < lo - 1e-10 || output > hi + 1e-10 {
            return false;
        }
    }

    true
}
