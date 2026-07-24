// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sampling-based runtime verification for zonotope properties.
//!
//! These functions use deterministic pseudo-random sampling to empirically
//! verify that zonotope algebra operations satisfy their soundness contracts.
//! They complement the formal proof infrastructure (T01, T02, T08, T12) with
//! high-confidence runtime checks.

use super::concrete::ConcreteZonotope;

/// Deterministic pseudo-random f64 in [-1, 1] from mutable seed.
///
/// Uses xorshift64 to avoid pulling `rand` as a production dependency.
fn pseudo_random(seed: &mut u64) -> f64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    let bits = *seed & 0x7FFF_FFFF_FFFF_FFFF;
    (bits as f64 / (0x7FFF_FFFF_FFFF_FFFFu64 as f64)) * 2.0 - 1.0
}

/// Generate `n` pseudo-random coefficients in [-1, 1].
fn random_coeffs(seed: &mut u64, n: usize) -> Vec<f64> {
    (0..n).map(|_| pseudo_random(seed)).collect()
}

/// Tolerance for floating-point comparisons in verification.
const VERIFY_TOL: f64 = 1e-9;

/// T01: Verify that sampled zonotope points lie within the interval hull.
///
/// Samples `samples` random points from `z` (using valid coefficients in
/// [-1, 1]) and checks that each falls within the interval hull. Returns
/// `true` if all sampled points are contained.
#[must_use]
pub fn verify_hull_soundness(z: &ConcreteZonotope, samples: usize) -> bool {
    let (lo, hi) = z.to_interval();
    let n = z.num_generators();
    let mut seed: u64 = 0xDEAD_BEEF_CAFE_1234;

    for _ in 0..samples {
        let coeffs = random_coeffs(&mut seed, n);
        let point = match z.sample_point(&coeffs) {
            Ok(p) => p,
            Err(_) => return false,
        };
        for (j, &xj) in point.iter().enumerate() {
            if xj < lo[j] - VERIFY_TOL || xj > hi[j] + VERIFY_TOL {
                return false;
            }
        }
    }
    true
}

/// T02: Verify linear transform soundness by sampling.
///
/// For each of `samples` random zonotope points x in Z, verifies that
/// W*x + b lies within the interval hull of W*Z + b.
///
/// `w` is row-major: `w[i]` is the i-th row (length = `z.dim()`).
#[must_use]
pub fn verify_linear_transform(
    z: &ConcreteZonotope,
    w: &[&[f64]],
    b: &[f64],
    samples: usize,
) -> bool {
    let transformed = z.linear_transform(w, b);
    let (lo, hi) = transformed.to_interval();
    let n = z.num_generators();
    let d_in = z.dim();
    let m = w.len();
    let mut seed: u64 = 0xCAFE_BABE_0000_5678;

    for _ in 0..samples {
        let coeffs = random_coeffs(&mut seed, n);
        let x = match z.sample_point(&coeffs) {
            Ok(p) => p,
            Err(_) => return false,
        };

        // Compute y = W*x + b
        let y: Vec<f64> = (0..m)
            .map(|i| {
                let mut val = b[i];
                for j in 0..d_in {
                    val += w[i][j] * x[j];
                }
                val
            })
            .collect();

        for (j, &yj) in y.iter().enumerate() {
            if yj < lo[j] - VERIFY_TOL || yj > hi[j] + VERIFY_TOL {
                return false;
            }
        }
    }
    true
}

/// T12: Verify that compression preserves the interval hull exactly.
///
/// The compressed zonotope must have the same interval hull as the
/// original, since merging generators via absolute-value summation
/// preserves per-coordinate reach.
#[must_use]
pub fn verify_compress_hull_exact(z: &ConcreteZonotope, kept: &[usize]) -> bool {
    z.verify_compress_hull_exact(kept)
}

/// T08: Verify Minkowski sum soundness by sampling.
///
/// For each of `samples` trials, picks random points x1 in Z1 and x2
/// in Z2 and checks that x1 + x2 lies within the interval hull of
/// Z1 + Z2.
#[must_use]
pub fn verify_minkowski_sum(z1: &ConcreteZonotope, z2: &ConcreteZonotope, samples: usize) -> bool {
    let sum = z1.minkowski_add(z2);
    let (lo, hi) = sum.to_interval();
    let mut seed: u64 = 0x1234_5678_9ABC_DEF0;

    for _ in 0..samples {
        let c1 = random_coeffs(&mut seed, z1.num_generators());
        let c2 = random_coeffs(&mut seed, z2.num_generators());
        let p1 = match z1.sample_point(&c1) {
            Ok(p) => p,
            Err(_) => return false,
        };
        let p2 = match z2.sample_point(&c2) {
            Ok(p) => p,
            Err(_) => return false,
        };

        for j in 0..z1.dim() {
            let s = p1[j] + p2[j];
            if s < lo[j] - VERIFY_TOL || s > hi[j] + VERIFY_TOL {
                return false;
            }
        }
    }
    true
}
