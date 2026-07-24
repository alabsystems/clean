// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Noise sensitivity, hypercontractivity, and spectral analysis
//!
//! This module extends the Boolean Fourier analysis framework with:
//!
//! - **Noise sensitivity/stability**: Measures how sensitive a Boolean
//!   function is to random bit flips. Central to hardness amplification
//!   and social choice theory.
//!
//! - **Influence decomposition**: Per-variable and maximum influence,
//!   plus the KKL inequality (computational verification).
//!
//! - **Spectral analysis**: Level-k Fourier weight, low-degree energy
//!   concentration, and spectral entropy. These quantify the "complexity"
//!   of a Boolean function in the Fourier domain.
//!
//! ## Key identities
//!
//! - Noise sensitivity formula:
//!   `Noise_delta(f) = sum_{S != empty} (1-2*delta)^{2|S|} * f_hat(S)^2`
//!
//! - Total influence identity:
//!   `I(f) = sum_{k=0}^{n} k * W^k(f)` where `W^k = sum_{|S|=k} f_hat(S)^2`
//!
//! - KKL inequality (Kahn-Kalai-Linial 1988):
//!   For balanced f, `max_i Inf_i(f) >= c * ln(n) / n` with `c ~ 2/(pi*e)`
//!
//! ## References
//!
//! - R. O'Donnell, *Analysis of Boolean Functions*, Cambridge, 2014, Ch. 2-5, 9
//! - J. Kahn, G. Kalai, N. Linial, "The Influence of Variables on
//!   Boolean Functions", *FOCS* 1988

use super::fourier::{compute_all_fourier, BooleanFunction, FourierError};
use crate::spec::ProofStatus;

/// Floating-point tolerance for identity checks.
const EPSILON: f64 = 1e-10;

// ---------------------------------------------------------------------------
// Noise sensitivity and stability
// ---------------------------------------------------------------------------

/// Noise sensitivity: probability that `f(x) != f(y)` where `y` is obtained
/// from `x` by flipping each bit independently with probability `delta`.
///
/// For {-1,1}-valued f:
///   `Noise_delta(f) = (1/2) - (1/2) * sum_S (1-2*delta)^{|S|} * f_hat(S)^2`
///
/// Equivalently, using rho = 1 - 2*delta:
///   `Noise_delta(f) = (1/2)(1 - sum_S rho^{|S|} f_hat(S)^2)`
///
/// For delta=0: `Noise_0 = 0` (no noise, no sensitivity).
/// For delta=1/2: `Noise_{1/2} = (1 - f_hat(empty)^2)/2 = Var(f)/2`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 2.44.
#[must_use]
pub fn noise_sensitivity(f: &BooleanFunction, delta: f64) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    let rho = 1.0 - 2.0 * delta;
    let stability: f64 = coeffs
        .iter()
        .enumerate()
        .map(|(s, c)| {
            let degree = (s as u32).count_ones() as i32;
            rho.powi(degree) * c * c
        })
        .sum();
    // Noise_delta = (1 - stability) / 2
    (1.0 - stability) / 2.0
}

/// Noise stability: `E[f(x) * f(y)]` where `y` is `rho`-correlated with `x`.
///
/// Each coordinate y_i = x_i with probability `(1+rho)/2`, and y_i = -x_i
/// with probability `(1-rho)/2`. Equivalently:
///
///   `Stab_rho(f) = sum_S rho^{|S|} * f_hat(S)^2`
///
/// For rho=1: `Stab_1 = E[f^2]` (perfect correlation).
/// For rho=0: `Stab_0 = f_hat(empty)^2 = E[f]^2`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 2.46.
#[must_use]
pub fn noise_stability(f: &BooleanFunction, rho: f64) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    coeffs
        .iter()
        .enumerate()
        .map(|(s, c)| {
            let degree = (s as u32).count_ones() as i32;
            rho.powi(degree) * c * c
        })
        .sum()
}

// ---------------------------------------------------------------------------
// Influence
// ---------------------------------------------------------------------------

/// Total influence: `I(f) = sum_i Inf_i(f) = sum_S |S| * f_hat(S)^2`.
///
/// Measures the expected number of "influential" coordinates.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Proposition 2.25.
#[must_use]
pub fn total_influence(f: &BooleanFunction) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    coeffs
        .iter()
        .enumerate()
        .map(|(s, c)| {
            let weight = (s as u32).count_ones() as f64;
            weight * c * c
        })
        .sum()
}

/// Per-variable influence: `Inf_i(f) = sum_{S containing i} f_hat(S)^2`.
///
/// The influence of variable `i` is the probability that flipping `x_i`
/// changes `f(x)`, averaged over uniform random `x`.
///
/// Returns `Err` if `var >= f.num_vars()`.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Definition 2.11.
pub fn variable_influence(f: &BooleanFunction, var: usize) -> Result<f64, FourierError> {
    let n = f.num_vars();
    if var >= n {
        return Err(FourierError::VariableOutOfRange { index: var, n });
    }
    let coeffs = compute_all_fourier(f)?;
    let bit = 1u32 << var;
    let inf: f64 = coeffs
        .iter()
        .enumerate()
        .filter(|(s, _)| (*s as u32) & bit != 0)
        .map(|(_, c)| c * c)
        .sum();
    Ok(inf)
}

/// Maximum influence: `max_i Inf_i(f)`.
///
/// KKL (1988) shows this is `>= Mathverse(log(n)/n)` for balanced functions.
///
/// Returns 0.0 for 0-variable functions.
#[must_use]
pub fn max_influence(f: &BooleanFunction) -> f64 {
    let n = f.num_vars();
    if n == 0 {
        return 0.0;
    }
    (0..n)
        .filter_map(|i| variable_influence(f, i).ok())
        .fold(0.0_f64, f64::max)
}

/// Verify KKL lower bound: `max_i Inf_i(f) >= c * ln(n) / n`.
///
/// The optimal constant in KKL is approximately `2 / (pi * e) ~ 0.234`.
/// Pass a smaller `c` for a weaker (more easily satisfied) bound.
///
/// Returns `true` if the bound holds or `n <= 1` (trivially true).
///
/// Reference: Kahn, Kalai, Linial, "The Influence of Variables on
/// Boolean Functions", *FOCS* 1988, Theorem 3.1.
#[must_use]
pub fn verify_kkl_bound(f: &BooleanFunction, c: f64) -> bool {
    let n = f.num_vars();
    if n <= 1 {
        return true;
    }
    let max_inf = max_influence(f);
    let bound = c * (n as f64).ln() / (n as f64);
    max_inf >= bound - EPSILON
}

// ---------------------------------------------------------------------------
// Spectral analysis
// ---------------------------------------------------------------------------

/// Level-k Fourier weight: `W^k(f) = sum_{|S|=k} f_hat(S)^2`.
///
/// The Fourier weight at degree `k`.
///
/// Returns 0.0 if `level > n` or if Fourier computation fails.
#[must_use]
pub fn level_weight(f: &BooleanFunction, level: usize) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    coeffs
        .iter()
        .enumerate()
        .filter(|(s, _)| ((*s) as u32).count_ones() as usize == level)
        .map(|(_, c)| c * c)
        .sum()
}

/// Low-degree energy: sum of `f_hat(S)^2` for `|S| <= max_degree`.
///
/// Measures how much of `f`'s "energy" is concentrated in low-degree terms.
/// A function is "low-degree" if most of its Fourier mass is at small levels.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Section 3.3.
#[must_use]
pub fn low_degree_energy(f: &BooleanFunction, max_degree: usize) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    coeffs
        .iter()
        .enumerate()
        .filter(|(s, _)| ((*s) as u32).count_ones() as usize <= max_degree)
        .map(|(_, c)| c * c)
        .sum()
}

/// Spectral entropy: `H(f) = -sum_S p(S) * log2(p(S))` where
/// `p(S) = f_hat(S)^2 / E[f^2]` is the "spectral distribution".
///
/// Only sums over S with `f_hat(S) != 0`. Returns 0.0 for constant
/// functions (single nonzero coefficient) and for functions where
/// `E[f^2] = 0`.
///
/// Friedgut's theorem: if `I(f) <= K`, then `f` is `O(epsilon)`-close
/// to a junta on `2^{O(K/epsilon)}` variables. Spectral entropy is a
/// related complexity measure.
///
/// Reference: O'Donnell, *Analysis of Boolean Functions*, Section 9.6.
#[must_use]
pub fn spectral_entropy(f: &BooleanFunction) -> f64 {
    let coeffs = match compute_all_fourier(f) {
        Ok(c) => c,
        Err(_) => return 0.0,
    };
    let total_energy: f64 = coeffs.iter().map(|c| c * c).sum();
    if total_energy < EPSILON {
        return 0.0;
    }
    let mut entropy = 0.0;
    for c in &coeffs {
        let p = c * c / total_energy;
        if p > EPSILON {
            entropy -= p * p.log2();
        }
    }
    entropy
}

/// Verify Parseval identity decomposed by level:
///   `sum_{k=0}^{n} W^k(f) = E[f^2]`.
///
/// Returns `true` if the identity holds within floating-point tolerance.
#[must_use]
pub fn verify_level_parseval(f: &BooleanFunction) -> bool {
    let n = f.num_vars();
    let level_sum: f64 = (0..=n).map(|k| level_weight(f, k)).sum();

    let size = f.values().len() as f64;
    let expectation: f64 = f.values().iter().map(|v| v * v).sum::<f64>() / size;

    (level_sum - expectation).abs() < EPSILON
}

// ---------------------------------------------------------------------------
// Proof status constants (S45-S47)
// ---------------------------------------------------------------------------

/// S45: Noise sensitivity Fourier formula.
///
/// `Noise_delta(f) = (1/2)(1 - sum_S (1-2*delta)^{|S|} f_hat(S)^2)`
///
/// Status: `DerivedPending` -- verified computationally; formal proof
/// term depends on inner-product linearity infrastructure.
pub const S45_NOISE_SENSITIVITY_FOURIER: ProofStatus = ProofStatus::DerivedPending;

/// S46: Total influence = sum of level weights * level.
///
/// `I(f) = sum_{k=0}^{n} k * W^k(f)`
///
/// Status: `DerivedPending` -- verified computationally; formal proof
/// term depends on the level decomposition lemma.
pub const S46_TOTAL_INFLUENCE_IDENTITY: ProofStatus = ProofStatus::DerivedPending;

/// S47: KKL inequality verification (computational).
///
/// For balanced `f`, `max_i Inf_i(f) >= c * ln(n) / n`.
///
/// Status: `DerivedPending` -- computational verification for small n;
/// the full proof requires hypercontractivity (Bonami-Beckner).
pub const S47_KKL_COMPUTATIONAL: ProofStatus = ProofStatus::DerivedPending;
