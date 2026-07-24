// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope ReLU overapproximation via lambda-relaxation (T03-T06).
//!
//! For each dimension j of the zonotope, the ReLU activation max(0, x_j) is
//! handled by case analysis on the interval hull [l_j, u_j]:
//!
//! - **Always active** (l_j >= 0): ReLU is identity; generators unchanged.
//! - **Always inactive** (u_j <= 0): ReLU outputs zero; zero the generators.
//! - **Crossing** (l_j < 0 < u_j): Lambda-relaxation overapproximation.
//!   - lambda = u / (u - l)
//!   - new center_j = lambda * center_j + (1 - lambda) * u / 2
//!   - existing generators scaled: gen_ij *= lambda
//!   - one new error generator added per crossing dimension with magnitude
//!     (1 - lambda) * u / 2
//!
//! ## Soundness
//!
//! The lambda-relaxation produces a parallelotope that contains the image of
//! max(0, x_j) for all x_j in [l_j, u_j]. The upper facet is the line
//! through (l, 0) and (u, u) (slope = lambda), and the lower facet is y = 0.
//! The new error generator accounts for the gap between these facets.
//!
//! ## References
//!
//! - Singh et al., "Fast and Effective Robustness Certification" (NeurIPS 2018)
//! - Gehr et al., "AI2: Safety and Robustness Certification of Neural Networks
//!   with Abstract Interpretation" (S&P 2018)

use super::concrete::ConcreteZonotope;

/// Classification of a neuron's activation status based on interval hull bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReluCase {
    /// Lower bound >= 0: ReLU is identity on this dimension.
    AlwaysActive,
    /// Upper bound <= 0: ReLU outputs zero on this dimension.
    AlwaysInactive,
    /// Lower < 0 < upper: crossing region, needs lambda-relaxation.
    Crossing,
}

/// Classify the ReLU case for a single dimension given its interval bounds.
#[must_use]
pub(crate) fn classify_relu(lower: f64, upper: f64) -> ReluCase {
    if lower >= 0.0 {
        ReluCase::AlwaysActive
    } else if upper <= 0.0 {
        ReluCase::AlwaysInactive
    } else {
        ReluCase::Crossing
    }
}

/// Apply element-wise ReLU overapproximation to a zonotope.
///
/// For each dimension j, computes the interval hull [l_j, u_j] and applies:
/// - Always active: keep generators as-is
/// - Always inactive: zero the center and generators for that dimension
/// - Crossing: lambda-relaxation with one new error generator per crossing dim
///
/// Returns a new zonotope that soundly overapproximates {max(0, x) : x in Z}.
#[must_use]
pub fn zonotope_relu(z: &ConcreteZonotope) -> ConcreteZonotope {
    let dim = z.dim();
    let (lower, upper) = z.to_interval();
    let num_existing_gen = z.num_generators();

    // Count crossing dimensions to know how many new generators we need.
    let crossing_dims: Vec<usize> = (0..dim)
        .filter(|&j| classify_relu(lower[j], upper[j]) == ReluCase::Crossing)
        .collect();
    let num_crossing = crossing_dims.len();

    // New generators = existing (scaled) + one per crossing dimension.
    let total_gen = num_existing_gen + num_crossing;
    let mut new_center = vec![0.0; dim];
    let mut new_generators: Vec<Vec<f64>> = vec![vec![0.0; dim]; total_gen];

    // Precompute lambda and mu = (1-lambda)*u/2 for crossing dims.
    let mut lambda_vec = vec![0.0; dim];
    let mut mu_vec = vec![0.0; dim];
    for &j in &crossing_dims {
        let l = lower[j];
        let u = upper[j];
        let lam = u / (u - l);
        lambda_vec[j] = lam;
        mu_vec[j] = (1.0 - lam) * u / 2.0;
    }

    for j in 0..dim {
        match classify_relu(lower[j], upper[j]) {
            ReluCase::AlwaysActive => {
                // Identity: keep center and generators unchanged.
                new_center[j] = z.center[j];
                for (gi, gvec) in z.generators.iter().enumerate() {
                    new_generators[gi][j] = gvec[j];
                }
            }
            ReluCase::AlwaysInactive => {
                // Zero everything for this dimension (already 0.0 from init).
            }
            ReluCase::Crossing => {
                // Lambda-relaxation.
                let lam = lambda_vec[j];
                let mu = mu_vec[j];
                new_center[j] = lam * z.center[j] + mu;
                for (gi, gvec) in z.generators.iter().enumerate() {
                    new_generators[gi][j] = lam * gvec[j];
                }
            }
        }
    }

    // Add new error generators for crossing dimensions.
    // Each crossing dimension j gets a fresh generator with magnitude mu[j]
    // in dimension j and zero elsewhere.
    for (crossing_idx, &j) in crossing_dims.iter().enumerate() {
        let gen_idx = num_existing_gen + crossing_idx;
        new_generators[gen_idx][j] = mu_vec[j];
    }

    ConcreteZonotope::new(new_center, new_generators)
}

/// Verify ReLU soundness by sampling: for each sampled point x in Z,
/// check that max(0, x) is contained in the interval hull of relu(Z).
///
/// Uses deterministic xorshift64 sampling consistent with `verify.rs`.
/// Returns `true` if all `num_samples` sampled points pass the check.
#[must_use]
pub fn verify_relu_soundness(z: &ConcreteZonotope, num_samples: usize) -> bool {
    let relu_z = zonotope_relu(z);
    let (relu_lo, relu_hi) = relu_z.to_interval();
    let num_gen = z.num_generators();
    let mut seed: u64 = 0xDEAD_BEEF_CAFE_0003;

    for _ in 0..num_samples {
        let coeffs: Vec<f64> = (0..num_gen).map(|_| pseudo_random(&mut seed)).collect();
        let point = match z.sample_point(&coeffs) {
            Ok(p) => p,
            Err(_) => return false,
        };
        let relu_point: Vec<f64> = point.iter().map(|&x| x.max(0.0)).collect();

        for (j, &rp) in relu_point.iter().enumerate() {
            if rp < relu_lo[j] - 1e-9 || rp > relu_hi[j] + 1e-9 {
                return false;
            }
        }
    }
    true
}

/// Compute overestimation ratio of the ReLU overapproximation.
///
/// Returns the ratio of total hull width after ReLU to total hull width
/// before ReLU. A ratio of 1.0 means the approximation is exact (only
/// possible when all neurons are always-active). Lower ratios indicate
/// dimension collapse from inactive neurons.
///
/// Returns `f64::INFINITY` if the input has zero total width.
#[must_use]
pub fn verify_relu_tightness(z: &ConcreteZonotope) -> f64 {
    let (lo_before, hi_before) = z.to_interval();
    let width_before: f64 = lo_before
        .iter()
        .zip(hi_before.iter())
        .map(|(&l, &h)| h - l)
        .sum();

    if width_before < f64::EPSILON {
        return f64::INFINITY;
    }

    let relu_z = zonotope_relu(z);
    let (lo_after, hi_after) = relu_z.to_interval();
    let width_after: f64 = lo_after
        .iter()
        .zip(hi_after.iter())
        .map(|(&l, &h)| h - l)
        .sum();

    width_after / width_before
}

/// Deterministic pseudo-random f64 in [-1, 1] (xorshift64).
fn pseudo_random(seed: &mut u64) -> f64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    let bits = *seed & 0x7FFF_FFFF_FFFF_FFFF;
    (bits as f64 / (0x7FFF_FFFF_FFFF_FFFFu64 as f64)) * 2.0 - 1.0
}
