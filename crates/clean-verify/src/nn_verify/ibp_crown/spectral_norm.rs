// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Spectral Norm Verification Properties (T32 deepening)
//!
//! Extends the brief T32 entry in the Lipschitz theorem registry with formal
//! verification infrastructure for spectral norm properties. Provides:
//!
//! - **Power iteration with convergence tracking**: Returns iteration count
//!   and relative change so callers can assess numerical confidence.
//! - **Bound verification**: Check that sigma_max(W) <= a claimed bound.
//! - **Interval spectral norm**: Sound outer bounds on sigma_max when weight
//!   entries are interval-valued (for robustness verification).
//! - **Frobenius-to-spectral bound**: Quick upper bound via ||W||_F >= sigma_max.
//! - **Rank-one update bound**: Weyl's inequality for W' = W + u*v^T.
//! - **Lipschitz-via-spectral**: T32 core statement that Lip(linear) = sigma_max.
//! - **Spectral gap**: sigma_1/sigma_2 ratio controlling convergence rate.
//! - **Submultiplicativity**: sigma_max(AB) <= sigma_max(A) * sigma_max(B).
//!
//! All proof status constants are `DerivedPending` pending formal derivation.

use super::ibp::Interval;
use crate::spec::ProofStatus;

// -- Proof status constants --------------------------------------------------

/// T32a: spectral norm equals operator norm (sigma_max(W) = sup ||Wx||/||x||).
pub const T32A_SPECTRAL_NORM_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// T32b: Frobenius norm dominates spectral norm (sigma_max <= ||W||_F).
pub const T32B_FROBENIUS_SPECTRAL_RELATION: ProofStatus = ProofStatus::DerivedPending;

/// T32c: spectral norm is submultiplicative (sigma_max(AB) <= sigma_max(A)*sigma_max(B)).
pub const T32C_SPECTRAL_SUBMULTIPLICATIVITY: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Core result type
// ---------------------------------------------------------------------------

/// Result of a spectral norm computation via power iteration.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SpectralNormResult {
    /// Computed spectral norm (largest singular value).
    pub spectral_norm: f64,
    /// Whether the iteration converged (relative change < tolerance).
    pub converged: bool,
    /// Number of iterations actually performed.
    pub iterations_used: usize,
    /// Final relative change between last two iterates.
    pub final_relative_change: f64,
}

// ---------------------------------------------------------------------------
// Power iteration with convergence tracking
// ---------------------------------------------------------------------------

/// Power iteration with convergence checking.
///
/// Computes the dominant singular value of `matrix` by iterating
/// v <- W^T W v with early termination when the relative change in the
/// Rayleigh quotient drops below `tolerance`.
///
/// # Parameters
///
/// - `matrix`: Row-major m x n weight matrix.
/// - `max_iterations`: Upper bound on iteration count.
/// - `tolerance`: Convergence threshold on relative change of estimated sigma.
///
/// # Returns
///
/// A [`SpectralNormResult`] with the computed norm, convergence flag,
/// iteration count, and final relative change.
#[must_use]
pub fn spectral_norm_power_iteration(
    matrix: &[Vec<f64>],
    max_iterations: usize,
    tolerance: f64,
) -> SpectralNormResult {
    if matrix.is_empty() {
        return SpectralNormResult {
            spectral_norm: 0.0,
            converged: true,
            iterations_used: 0,
            final_relative_change: 0.0,
        };
    }
    let m = matrix.len();
    let n = matrix[0].len();
    if n == 0 {
        return SpectralNormResult {
            spectral_norm: 0.0,
            converged: true,
            iterations_used: 0,
            final_relative_change: 0.0,
        };
    }

    // Initialize v to uniform unit vector.
    let inv_sqrt_n = 1.0 / (n as f64).sqrt();
    let mut v: Vec<f64> = vec![inv_sqrt_n; n];

    let mut prev_sigma = 0.0_f64;
    let mut final_change = f64::INFINITY;
    let mut converged = false;
    let mut iters_used = 0;

    for iter in 0..max_iterations {
        iters_used = iter + 1;

        // u = W * v
        let u: Vec<f64> = (0..m)
            .map(|i| {
                matrix[i]
                    .iter()
                    .zip(v.iter())
                    .map(|(w, vi)| w * vi)
                    .sum::<f64>()
            })
            .collect();

        // v_new = W^T * u
        let mut v_new = vec![0.0; n];
        for i in 0..m {
            for j in 0..n {
                v_new[j] += matrix[i][j] * u[i];
            }
        }

        // Normalize
        let norm: f64 = v_new.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm < f64::EPSILON {
            return SpectralNormResult {
                spectral_norm: 0.0,
                converged: true,
                iterations_used: iters_used,
                final_relative_change: 0.0,
            };
        }
        for x in &mut v_new {
            *x /= norm;
        }
        v = v_new;

        // Estimate sigma via Rayleigh quotient: ||Wv||
        let u_final: Vec<f64> = (0..m)
            .map(|i| {
                matrix[i]
                    .iter()
                    .zip(v.iter())
                    .map(|(w, vi)| w * vi)
                    .sum::<f64>()
            })
            .collect();
        let sigma = u_final.iter().map(|x| x * x).sum::<f64>().sqrt();

        // Check convergence
        final_change = if prev_sigma.abs() > f64::EPSILON {
            ((sigma - prev_sigma) / prev_sigma).abs()
        } else {
            f64::INFINITY
        };

        if final_change < tolerance {
            converged = true;
            return SpectralNormResult {
                spectral_norm: sigma,
                converged,
                iterations_used: iters_used,
                final_relative_change: final_change,
            };
        }
        prev_sigma = sigma;
    }

    // Did not converge within max_iterations
    SpectralNormResult {
        spectral_norm: prev_sigma,
        converged,
        iterations_used: iters_used,
        final_relative_change: final_change,
    }
}

// ---------------------------------------------------------------------------
// Bound verification
// ---------------------------------------------------------------------------

/// Verify that sigma_max(W) <= `claimed_bound`.
///
/// Runs power iteration internally and checks whether the computed spectral
/// norm is at or below the claimed value (within floating-point tolerance).
///
/// Returns `Ok(result)` if the bound holds, `Err(message)` otherwise.
pub fn verify_spectral_norm_bound(
    matrix: &[Vec<f64>],
    claimed_bound: f64,
    max_iterations: usize,
    tolerance: f64,
) -> Result<SpectralNormResult, String> {
    let result = spectral_norm_power_iteration(matrix, max_iterations, tolerance);
    if result.spectral_norm <= claimed_bound + f64::EPSILON {
        Ok(result)
    } else {
        Err(format!(
            "spectral norm {:.6} exceeds claimed bound {:.6}",
            result.spectral_norm, claimed_bound
        ))
    }
}

// ---------------------------------------------------------------------------
// Interval spectral norm
// ---------------------------------------------------------------------------

/// Compute a sound outer bound on the spectral norm of an interval-valued
/// weight matrix.
///
/// Given a matrix whose entries are intervals, this computes an upper bound
/// on sigma_max for *any* point matrix within those intervals. The strategy
/// is conservative: construct the matrix of absolute-value upper bounds
/// (max(|lower|, |upper|) per entry) and compute its spectral norm. By the
/// monotonicity of singular values under entry-wise absolute value dominance,
/// this yields a valid upper bound.
///
/// Returns an [`Interval`] where `lower` is the spectral norm of the midpoint
/// matrix and `upper` is the spectral norm of the absolute-bound matrix.
#[must_use]
pub fn spectral_norm_interval(
    interval_matrix: &[Vec<Interval>],
    max_iterations: usize,
    tolerance: f64,
) -> Interval {
    if interval_matrix.is_empty() {
        return Interval::new(0.0, 0.0);
    }
    let m = interval_matrix.len();
    let n = interval_matrix[0].len();
    if n == 0 {
        return Interval::new(0.0, 0.0);
    }

    // Midpoint matrix for lower bound estimate.
    let mid_matrix: Vec<Vec<f64>> = interval_matrix
        .iter()
        .map(|row| row.iter().map(|iv| (iv.lower + iv.upper) / 2.0).collect())
        .collect();

    // Absolute-bound matrix for upper bound.
    let abs_matrix: Vec<Vec<f64>> = interval_matrix
        .iter()
        .map(|row| {
            row.iter()
                .map(|iv| iv.lower.abs().max(iv.upper.abs()))
                .collect()
        })
        .collect();

    let mid_result = spectral_norm_power_iteration(&mid_matrix, max_iterations, tolerance);
    let abs_result = spectral_norm_power_iteration(&abs_matrix, max_iterations, tolerance);

    // The midpoint spectral norm is a lower bound (some specific matrix has
    // at least this sigma_max). The absolute-bound matrix spectral norm is
    // an upper bound (no matrix in the interval can exceed this).
    let lower = mid_result.spectral_norm;
    let upper = abs_result.spectral_norm;

    // Ensure interval validity (upper >= lower is guaranteed by construction
    // but guard against numerical noise).
    if upper < lower {
        Interval::new(lower, lower)
    } else {
        Interval::new(lower, upper)
    }
}

// ---------------------------------------------------------------------------
// Frobenius-to-spectral bound
// ---------------------------------------------------------------------------

/// Quick upper bound on sigma_max via the Frobenius norm.
///
/// Since sigma_max(W) <= ||W||_F = sqrt(sum w_ij^2), this provides a
/// cheap (O(mn)) upper bound without iterative computation. The bound
/// is tight only for rank-1 matrices.
///
/// T32b: Frobenius-spectral relation.
#[must_use]
pub fn frobenius_to_spectral_bound(matrix: &[Vec<f64>]) -> f64 {
    let sum_sq: f64 = matrix
        .iter()
        .flat_map(|row| row.iter())
        .map(|w| w * w)
        .sum();
    sum_sq.sqrt()
}

// ---------------------------------------------------------------------------
// Rank-one update bound (Weyl's inequality)
// ---------------------------------------------------------------------------

/// Bound sigma_max(W + u*v^T) using Weyl's inequality.
///
/// For W' = W + u*v^T:
///   |sigma_max(W') - sigma_max(W)| <= sigma_max(u*v^T) = ||u|| * ||v||
///
/// Therefore:
///   sigma_max(W') <= sigma_max(W) + ||u|| * ||v||
///
/// # Parameters
///
/// - `sigma_w`: spectral norm of the original matrix W.
/// - `u`: column vector of the rank-one perturbation.
/// - `v`: row vector of the rank-one perturbation.
///
/// # Returns
///
/// Upper bound on sigma_max(W + u*v^T).
#[must_use]
pub fn spectral_norm_rank_one_update(sigma_w: f64, u: &[f64], v: &[f64]) -> f64 {
    let u_norm = u.iter().map(|x| x * x).sum::<f64>().sqrt();
    let v_norm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
    sigma_w + u_norm * v_norm
}

// ---------------------------------------------------------------------------
// T32 core: Lipschitz via spectral norm
// ---------------------------------------------------------------------------

/// Verify that a linear layer's Lipschitz constant equals its spectral norm.
///
/// This is the core statement of T32: for y = Wx, the Lipschitz constant
/// (sup ||Wx||/||x|| over x != 0) equals sigma_max(W). We verify this by
/// computing sigma_max via power iteration and checking it matches the
/// claimed Lipschitz constant within tolerance.
///
/// Returns `Ok(sigma)` if |claimed - sigma_max| < tolerance, `Err` otherwise.
pub fn verify_lipschitz_via_spectral(
    matrix: &[Vec<f64>],
    claimed_lipschitz: f64,
    max_iterations: usize,
    tolerance: f64,
) -> Result<f64, String> {
    let result = spectral_norm_power_iteration(matrix, max_iterations, tolerance);
    let sigma = result.spectral_norm;
    if (sigma - claimed_lipschitz).abs() < tolerance {
        Ok(sigma)
    } else {
        Err(format!(
            "claimed Lipschitz {claimed_lipschitz:.6} differs from sigma_max {sigma:.6} \
             (difference {:.2e}, tolerance {tolerance:.2e})",
            (sigma - claimed_lipschitz).abs()
        ))
    }
}

// ---------------------------------------------------------------------------
// Spectral gap
// ---------------------------------------------------------------------------

/// Compute the spectral gap ratio sigma_1 / sigma_2.
///
/// The spectral gap controls the convergence rate of power iteration:
/// a larger gap means faster convergence. We estimate sigma_2 by deflating
/// the dominant singular direction and re-running power iteration.
///
/// Returns `None` if the matrix has rank <= 1 (sigma_2 ~ 0).
#[must_use]
pub fn spectral_gap(matrix: &[Vec<f64>], max_iterations: usize, tolerance: f64) -> Option<f64> {
    if matrix.is_empty() {
        return None;
    }
    let m = matrix.len();
    let n = matrix[0].len();
    if n == 0 || m.min(n) < 2 {
        return None;
    }

    // Step 1: compute sigma_1 and its right singular vector v1.
    let inv_sqrt_n = 1.0 / (n as f64).sqrt();
    let mut v: Vec<f64> = vec![inv_sqrt_n; n];

    for _ in 0..max_iterations {
        let u: Vec<f64> = (0..m)
            .map(|i| {
                matrix[i]
                    .iter()
                    .zip(v.iter())
                    .map(|(w, vi)| w * vi)
                    .sum::<f64>()
            })
            .collect();
        let mut v_new = vec![0.0; n];
        for i in 0..m {
            for j in 0..n {
                v_new[j] += matrix[i][j] * u[i];
            }
        }
        let norm: f64 = v_new.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm < f64::EPSILON {
            return None;
        }
        for x in &mut v_new {
            *x /= norm;
        }
        v = v_new;
    }
    let v1 = v;

    // sigma_1 = ||W * v1||
    let wv1: Vec<f64> = (0..m)
        .map(|i| {
            matrix[i]
                .iter()
                .zip(v1.iter())
                .map(|(w, vi)| w * vi)
                .sum::<f64>()
        })
        .collect();
    let sigma1 = wv1.iter().map(|x| x * x).sum::<f64>().sqrt();
    if sigma1 < f64::EPSILON {
        return None;
    }
    let u1: Vec<f64> = wv1.iter().map(|x| x / sigma1).collect();

    // Step 2: deflate — W2 = W - sigma1 * u1 * v1^T
    let deflated: Vec<Vec<f64>> = (0..m)
        .map(|i| {
            (0..n)
                .map(|j| matrix[i][j] - sigma1 * u1[i] * v1[j])
                .collect()
        })
        .collect();

    // Step 3: sigma_2 via power iteration on deflated matrix.
    let result2 = spectral_norm_power_iteration(&deflated, max_iterations, tolerance);
    let sigma2 = result2.spectral_norm;

    if sigma2 < f64::EPSILON {
        return None; // Rank-1 matrix
    }

    Some(sigma1 / sigma2)
}

// ---------------------------------------------------------------------------
// Submultiplicativity verification
// ---------------------------------------------------------------------------

/// Verify sigma_max(AB) <= sigma_max(A) * sigma_max(B) for composed layers.
///
/// T32c: spectral norm submultiplicativity. Computes spectral norms of A, B,
/// and their product AB, then checks the inequality.
///
/// Returns `Ok((sigma_a, sigma_b, sigma_ab))` if the inequality holds,
/// `Err` otherwise.
pub fn verify_submultiplicativity(
    a: &[Vec<f64>],
    b: &[Vec<f64>],
    max_iterations: usize,
    tolerance: f64,
) -> Result<(f64, f64, f64), String> {
    if a.is_empty() || b.is_empty() {
        return Ok((0.0, 0.0, 0.0));
    }
    let k = a[0].len();
    if k != b.len() {
        return Err(format!(
            "inner dimension mismatch: A cols={k}, B rows={}",
            b.len()
        ));
    }
    let m = a.len();
    let n = b[0].len();

    // Compute AB
    let ab: Vec<Vec<f64>> = (0..m)
        .map(|i| {
            (0..n)
                .map(|j| (0..k).map(|p| a[i][p] * b[p][j]).sum::<f64>())
                .collect()
        })
        .collect();

    let res_a = spectral_norm_power_iteration(a, max_iterations, tolerance);
    let res_b = spectral_norm_power_iteration(b, max_iterations, tolerance);
    let res_ab = spectral_norm_power_iteration(&ab, max_iterations, tolerance);

    let sigma_a = res_a.spectral_norm;
    let sigma_b = res_b.spectral_norm;
    let sigma_ab = res_ab.spectral_norm;

    // Relative tolerance scaled to product magnitude for numerical stability.
    let product = sigma_a * sigma_b;
    let tol = 1e-9_f64.max(product * 1e-12);
    if sigma_ab <= product + tol {
        Ok((sigma_a, sigma_b, sigma_ab))
    } else {
        Err(format!(
            "submultiplicativity violated: sigma(AB)={sigma_ab:.6} > \
             sigma(A)*sigma(B)={:.6}",
            sigma_a * sigma_b
        ))
    }
}
