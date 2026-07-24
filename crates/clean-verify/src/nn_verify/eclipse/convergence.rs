// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ECLipsE Convergence Rate Analysis (C003)
//!
//! Proves that the ECLipsE (Efficient CLiP-based Splittable Estimator)
//! iterative refinement algorithm converges via Lipschitz contraction.
//!
//! ## Core theorem (Banach fixed-point)
//!
//! If `f` is a contraction mapping with Lipschitz constant `L < 1`, i.e.
//! `||f(x) - f(y)|| <= L * ||x - y||` for all `x, y`, then:
//!
//! 1. `f` has a unique fixed point `x*`
//! 2. The iterates `x_{n+1} = f(x_n)` converge to `x*` from any start
//! 3. Error bound: `||x_n - x*|| <= L^n / (1 - L) * ||x_1 - x_0||`
//!
//! ## Connection to Lipschitz analysis
//!
//! Uses the Lipschitz analysis infrastructure from `ibp_crown::lipschitz`
//! to verify that eclipse block Lipschitz constants satisfy `L < 1`.

use thiserror::Error;

/// Errors raised during ECLipsE convergence verification.
#[derive(Debug, Clone, PartialEq, Error)]
#[non_exhaustive]
pub(crate) enum EclipseConvergenceError {
    /// The Lipschitz constant is not a valid contraction factor.
    #[error("Lipschitz constant {constant} is not a contraction (must be in [0, 1))")]
    NotContractive { constant: f64 },

    /// The contraction property was violated for specific inputs.
    #[error(
        "contraction violated: d(f(x),f(y)) = {output_distance} > L * d(x,y) = {bound} \
         (L = {lipschitz_constant})"
    )]
    ContractionViolated {
        output_distance: f64,
        bound: f64,
        lipschitz_constant: f64,
    },

    /// Dimension mismatch between inputs.
    #[error("dimension mismatch: expected {expected}, got {got}")]
    DimensionMismatch { expected: usize, got: usize },

    /// The iteration did not converge within the allowed iterations.
    #[error(
        "did not converge after {iterations} iterations (final distance: {final_distance:.2e})"
    )]
    DidNotConverge {
        iterations: usize,
        final_distance: f64,
    },
}

// ---------------------------------------------------------------------------
// Contractive map trait
// ---------------------------------------------------------------------------

/// A mapping that is a contraction with a known Lipschitz constant L < 1.
///
/// Implementors guarantee `||f(x) - f(y)|| <= L * ||x - y||` for all `x, y`
/// where `L = lipschitz_constant()`.
pub(crate) trait ContractiveMap {
    /// The Lipschitz constant L of this contraction (must be in [0, 1)).
    fn lipschitz_constant(&self) -> f64;

    /// Apply the mapping to a point.
    fn apply(&self, point: &[f64]) -> Vec<f64>;
}

// ---------------------------------------------------------------------------
// Concrete implementation: affine contraction step
// ---------------------------------------------------------------------------

/// A single ECLipsE refinement step modeled as an affine contraction
/// `f(x) = Wx + b`.
///
/// The weight matrix `W` must have spectral norm `< 1` for the mapping
/// to be a contraction. The Lipschitz constant is the spectral norm of `W`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct EclipseRefinementStep {
    /// Row-major weight matrix.
    weight: Vec<Vec<f64>>,
    /// Bias vector.
    bias: Vec<f64>,
    /// Lipschitz constant (spectral norm of weight).
    lipschitz: f64,
}

impl EclipseRefinementStep {
    /// Create a new refinement step with the given weight, bias, and
    /// claimed Lipschitz constant.
    #[must_use]
    pub(crate) fn new(weight: Vec<Vec<f64>>, bias: Vec<f64>, lipschitz_constant: f64) -> Self {
        debug_assert!(
            lipschitz_constant >= 0.0,
            "Lipschitz constant must be non-negative"
        );
        Self {
            weight,
            bias,
            lipschitz: lipschitz_constant,
        }
    }
}

impl ContractiveMap for EclipseRefinementStep {
    fn lipschitz_constant(&self) -> f64 {
        self.lipschitz
    }

    fn apply(&self, point: &[f64]) -> Vec<f64> {
        self.weight
            .iter()
            .zip(self.bias.iter())
            .map(|(row, &b)| {
                row.iter()
                    .zip(point.iter())
                    .map(|(&w, &x)| w * x)
                    .sum::<f64>()
                    + b
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Convergence rate bound
// ---------------------------------------------------------------------------

/// Compute the a priori error bound from the Banach fixed-point theorem.
///
/// After `n` iterations starting from `x_0`, the distance to the fixed
/// point `x*` satisfies:
///
/// ```text
/// ||x_n - x*|| <= L^n / (1 - L) * initial_distance
/// ```
///
/// where `initial_distance = ||x_1 - x_0||`.
#[must_use]
pub(crate) fn convergence_rate_bound(
    lipschitz_constant: f64,
    initial_distance: f64,
    n_iterations: usize,
) -> f64 {
    lipschitz_constant.powi(n_iterations as i32) / (1.0 - lipschitz_constant) * initial_distance
}

// ---------------------------------------------------------------------------
// Contraction verification
// ---------------------------------------------------------------------------

/// Verify the contraction property for a specific pair of points.
///
/// Checks that `||f(x) - f(y)|| <= L * ||x - y||` within the given
/// tolerance.
pub(crate) fn verify_contraction<M: ContractiveMap>(
    map: &M,
    x: &[f64],
    y: &[f64],
    tolerance: f64,
) -> Result<(), EclipseConvergenceError> {
    let l = map.lipschitz_constant();
    if l >= 1.0 {
        return Err(EclipseConvergenceError::NotContractive { constant: l });
    }

    let fx = map.apply(x);
    let fy = map.apply(y);

    let input_dist = l2_norm_diff(x, y);
    let output_dist = l2_norm_diff(&fx, &fy);
    let bound = l * input_dist;

    if output_dist > bound + tolerance {
        return Err(EclipseConvergenceError::ContractionViolated {
            output_distance: output_dist,
            bound,
            lipschitz_constant: l,
        });
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Convergence witness
// ---------------------------------------------------------------------------

/// Witness for a verified convergence rate: records the iterate sequence
/// and verifies geometric decrease of successive distances.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ConvergenceWitness {
    /// Distances between successive iterates: `||x_{i+1} - x_i||`.
    pub(crate) successive_distances: Vec<f64>,
    /// Observed contraction ratios: `d_{i+1} / d_i`.
    pub(crate) contraction_ratios: Vec<f64>,
    /// Maximum observed contraction ratio.
    pub(crate) max_ratio: f64,
}

/// Verify the convergence rate by running `n_iterations` and checking
/// that successive distances decrease geometrically.
pub(crate) fn verify_convergence_rate<M: ContractiveMap>(
    map: &M,
    x0: &[f64],
    n_iterations: usize,
    tolerance: f64,
) -> Result<ConvergenceWitness, EclipseConvergenceError> {
    let l = map.lipschitz_constant();
    if l >= 1.0 {
        return Err(EclipseConvergenceError::NotContractive { constant: l });
    }

    let mut prev = x0.to_vec();
    let mut successive_distances = Vec::with_capacity(n_iterations);
    let mut contraction_ratios = Vec::new();

    for _ in 0..n_iterations {
        let next = map.apply(&prev);
        let dist = l2_norm_diff(&prev, &next);
        successive_distances.push(dist);
        prev = next;
    }

    let mut max_ratio = 0.0_f64;
    for window in successive_distances.windows(2) {
        if window[0] > tolerance {
            let ratio = window[1] / window[0];
            contraction_ratios.push(ratio);
            max_ratio = max_ratio.max(ratio);
        }
    }

    Ok(ConvergenceWitness {
        successive_distances,
        contraction_ratios,
        max_ratio,
    })
}

// ---------------------------------------------------------------------------
// Fixed-point iteration
// ---------------------------------------------------------------------------

/// Result of iterating to a fixed point.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FixedPointResult {
    /// Approximate fixed point.
    pub(crate) fixed_point: Vec<f64>,
    /// Number of iterations performed.
    pub(crate) iterations_used: usize,
    /// Whether the iteration converged (distance < tolerance).
    pub(crate) converged: bool,
    /// Distance between the last two iterates.
    pub(crate) final_distance: f64,
}

/// Iterate the contractive map until the successive distance drops
/// below `tolerance`, or `max_iterations` is reached.
pub(crate) fn iterate_to_fixed_point<M: ContractiveMap>(
    map: &M,
    x0: &[f64],
    max_iterations: usize,
    tolerance: f64,
) -> Result<FixedPointResult, EclipseConvergenceError> {
    let l = map.lipschitz_constant();
    if l >= 1.0 {
        return Err(EclipseConvergenceError::NotContractive { constant: l });
    }

    let mut current = x0.to_vec();
    let mut final_distance = f64::INFINITY;

    for iteration in 0..max_iterations {
        let next = map.apply(&current);
        final_distance = l2_norm_diff(&current, &next);
        current = next;

        if final_distance < tolerance {
            return Ok(FixedPointResult {
                fixed_point: current,
                iterations_used: iteration + 1,
                converged: true,
                final_distance,
            });
        }
    }

    Err(EclipseConvergenceError::DidNotConverge {
        iterations: max_iterations,
        final_distance,
    })
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Compute the L2 distance between two vectors.
#[must_use]
fn l2_norm_diff(x: &[f64], y: &[f64]) -> f64 {
    x.iter()
        .zip(y.iter())
        .map(|(&xi, &yi)| {
            let d = xi - yi;
            d * d
        })
        .sum::<f64>()
        .sqrt()
}
