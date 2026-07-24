// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner Hypercontractivity for Boolean Function Analysis
//!
//! The Bonami-Beckner theorem (1970/1975) is a cornerstone of Boolean
//! function analysis. It bounds the q-norm of the noise operator T_rho
//! applied to a Boolean function:
//!
//!   `||T_rho f||_q <= ||f||_2`   when `rho <= 1/sqrt(q-1)`
//!
//! The noise operator T_rho acts in the Fourier domain by multiplying
//! each level-k coefficient by `rho^k`:
//!
//!   `(T_rho f)^(S) = rho^{|S|} * f^(S)`
//!
//! This module provides executable verification of:
//! - Noise operator application in the Fourier domain
//! - Level-k Fourier weight computation
//! - Hypercontractive norm bounds
//! - Bonami-Beckner inequality verification
//!
//! ## Proof Status Constants
//!
//! | ID  | Name                       | Status         |
//! |-----|----------------------------|----------------|
//! | S50 | Bonami-Beckner inequality  | DerivedPending |
//! | S51 | Hypercontractive norm      | DerivedPending |
//!
//! ## References
//!
//! - A. Bonami, "Etude des coefficients de Fourier des fonctions de L^p(G)",
//!   *Annales de l'Institut Fourier* 20(2), 1970, pp. 335-402
//! - W. Beckner, "Inequalities in Fourier Analysis", *Annals of Mathematics*
//!   102(1), 1975, pp. 159-182
//! - R. O'Donnell, *Analysis of Boolean Functions*, Cambridge, 2014, Ch. 9

use crate::spec::ProofStatus;

/// Floating-point tolerance for identity checks.
const EPSILON: f64 = 1e-10;

// ---------------------------------------------------------------------------
// Noise operator in Fourier domain
// ---------------------------------------------------------------------------

/// Apply the noise operator T_rho in the Fourier domain.
///
/// Each Fourier coefficient at level k is multiplied by `rho^k`.
/// The level of a coefficient indexed by subset bitmask `s` is
/// the popcount of `s`.
///
/// `coefficients` is indexed by subset bitmask (output of
/// `fourier::compute_all_fourier`). `rho` is the noise parameter
/// in `[0, 1]`.
///
/// Returns a new vector of dampened coefficients.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 2.46.
#[must_use]
pub fn noise_operator_fourier(coefficients: &[f64], rho: f64) -> Vec<f64> {
    coefficients
        .iter()
        .enumerate()
        .map(|(s, &c)| {
            let level = (s as u32).count_ones();
            c * rho.powi(level as i32)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Level-k Fourier weight
// ---------------------------------------------------------------------------

/// Compute the level-k Fourier weight W^k(f) from Fourier coefficients.
///
/// `W^k(f) = sum_{|S|=k} f_hat(S)^2`
///
/// `coefficients` is indexed by subset bitmask. `n` is the number of
/// variables. `k` is the target level.
///
/// Returns 0.0 if `k > n`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 1.14.
#[must_use]
pub fn level_k_weight(coefficients: &[f64], n: usize, k: usize) -> f64 {
    if k > n {
        return 0.0;
    }
    let size = 1usize << n;
    coefficients
        .iter()
        .take(size)
        .enumerate()
        .filter(|(s, _)| (*s as u32).count_ones() as usize == k)
        .map(|(_, &c)| c * c)
        .sum()
}

// ---------------------------------------------------------------------------
// Hypercontractive norm
// ---------------------------------------------------------------------------

/// Compute `||T_rho f||_q` via Fourier coefficients.
///
/// This evaluates `T_rho f` at each input point using the dampened
/// Fourier expansion, then computes the q-norm over the uniform
/// distribution:
///
///   `||g||_q = (E[|g|^q])^{1/q}`
///
/// For q >= 1. Uses the inverse Fourier transform to reconstruct
/// function values from dampened coefficients.
///
/// Returns 0.0 for empty coefficient vectors or q < 1.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Section 9.1.
#[must_use]
pub fn hypercontractive_norm(coefficients: &[f64], n: usize, rho: f64, q: f64) -> f64 {
    if coefficients.is_empty() || q < 1.0 {
        return 0.0;
    }
    let dampened = noise_operator_fourier(coefficients, rho);
    let size = 1usize << n;
    // Reconstruct function values from dampened Fourier coefficients
    // g(x) = sum_S dampened[S] * chi_S(x)
    let q_norm_sum: f64 = (0..size)
        .map(|x| {
            let val: f64 = dampened
                .iter()
                .take(size)
                .enumerate()
                .map(|(s, &c)| {
                    let parity = ((s as u32) & (x as u32)).count_ones();
                    let chi = if parity.is_multiple_of(2) { 1.0 } else { -1.0 };
                    c * chi
                })
                .sum();
            val.abs().powf(q)
        })
        .sum();
    let mean = q_norm_sum / size as f64;
    mean.powf(1.0 / q)
}

/// Compute `||f||_p` (the p-norm) from Fourier coefficients.
///
/// Reconstructs function values via inverse Fourier transform and
/// computes `(E[|f|^p])^{1/p}`.
///
/// Returns 0.0 for empty coefficient vectors or p < 1.
#[must_use]
pub fn fourier_p_norm(coefficients: &[f64], n: usize, p: f64) -> f64 {
    if coefficients.is_empty() || p < 1.0 {
        return 0.0;
    }
    let size = 1usize << n;
    let p_norm_sum: f64 = (0..size)
        .map(|x| {
            let val: f64 = coefficients
                .iter()
                .take(size)
                .enumerate()
                .map(|(s, &c)| {
                    let parity = ((s as u32) & (x as u32)).count_ones();
                    let chi = if parity.is_multiple_of(2) { 1.0 } else { -1.0 };
                    c * chi
                })
                .sum();
            val.abs().powf(p)
        })
        .sum();
    let mean = p_norm_sum / size as f64;
    mean.powf(1.0 / p)
}

// ---------------------------------------------------------------------------
// Bonami-Beckner inequality verification
// ---------------------------------------------------------------------------

/// Compute the optimal noise parameter rho for a given q.
///
/// The Bonami-Beckner theorem states `||T_rho f||_q <= ||f||_2`
/// when `rho <= 1/sqrt(q-1)`. The optimal (largest) such rho is:
///
///   `rho* = 1/sqrt(q-1)`
///
/// For q = 2: rho = 1 (no damping needed, just Parseval).
/// For q = 4: rho = 1/sqrt(3).
///
/// Returns `f64::INFINITY` for `q <= 1` (degenerate case).
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Theorem 9.22.
#[must_use]
pub fn optimal_rho_for_q(q: f64) -> f64 {
    if q <= 1.0 {
        return f64::INFINITY;
    }
    1.0 / (q - 1.0).sqrt()
}

/// Verify the Bonami-Beckner hypercontractivity inequality:
///
///   `||T_rho f||_4 <= ||f||_2`
///
/// at the given `rho`. The inequality holds for `rho <= 1/sqrt(3)`.
/// This function checks it computationally for the given coefficients.
///
/// Returns `true` if `||T_rho f||_4 <= ||f||_2 + epsilon`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Theorem 9.22.
#[must_use]
pub fn verify_bonami_beckner(coefficients: &[f64], n: usize, rho: f64) -> bool {
    let lhs = hypercontractive_norm(coefficients, n, rho, 4.0);
    let rhs = fourier_p_norm(coefficients, n, 2.0);
    lhs <= rhs + EPSILON
}

/// Compute the Bonami-Beckner bound value.
///
/// Returns `(||T_rho f||_q, ||f||_2)` so callers can inspect both sides
/// of the inequality `||T_rho f||_q <= ||f||_2`.
///
/// The inequality holds when `rho <= 1/sqrt(q-1)`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Theorem 9.22.
#[must_use]
pub fn bonami_beckner_bound(f: &super::fourier::BooleanFunction, rho: f64, q: f64) -> f64 {
    let coeffs = match super::fourier::compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    let n = f.num_vars();
    let lhs = hypercontractive_norm(&coeffs, n, rho, q);
    let rhs = fourier_p_norm(&coeffs, n, 2.0);
    // Return the ratio ||T_rho f||_q / ||f||_2
    // Bonami-Beckner says this is <= 1 when rho <= 1/sqrt(q-1)
    if rhs < EPSILON {
        return 0.0;
    }
    lhs / rhs
}

// ---------------------------------------------------------------------------
// Proof status constants (S50-S51)
// ---------------------------------------------------------------------------

/// S50: Bonami-Beckner hypercontractivity inequality.
///
/// `||T_rho f||_q <= ||f||_2` when `rho <= 1/sqrt(q-1)`.
///
/// Status: `DerivedPending` -- verified computationally for small n
/// and standard function families (dictator, parity, majority).
/// Formal proof term requires tensor-power machinery.
pub const S50_BONAMI_BECKNER: ProofStatus = ProofStatus::DerivedPending;

/// S51: Hypercontractive norm computation via Fourier.
///
/// `||T_rho f||_q` computed from dampened Fourier coefficients and
/// inverse transform reconstruction.
///
/// Status: `DerivedPending` -- executable computation verified against
/// direct truth-table evaluation for n <= 10.
pub const S51_HYPERCONTRACTIVE_NORM: ProofStatus = ProofStatus::DerivedPending;
