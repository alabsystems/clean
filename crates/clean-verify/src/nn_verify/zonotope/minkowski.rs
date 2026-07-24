// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minkowski sum for skip connections (T08).
//!
//! Required for residual streams in transformers: if x₁ ∈ Z₁ and x₂ ∈ Z₂,
//! then x₁ + x₂ ∈ Z₁ ⊕ Z₂ where ⊕ concatenates generators.
//!
//! This module provides the fundamental Minkowski sum, overapproximation,
//! generator reduction after summation, Hausdorff distance bounds, interval
//! hull computation, residual connection verification, and scalar scaling.

use super::concrete::{ConcreteZonotope, ZonotopeError};
use crate::spec::ProofStatus;

// ---------------------------------------------------------------------------
// Proof status constants
// ---------------------------------------------------------------------------

/// T08a: Minkowski sum is sound.
/// For any x₁ in Z₁ and x₂ in Z₂, x₁ + x₂ is in minkowski_sum(Z₁, Z₂).
/// Proof: concatenate the coefficient vectors from each zonotope.
/// See [`super::proofs::verify_t08_minkowski_sum_sound`] for constructive witness.
pub const T08A_MINKOWSKI_SUM_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T08b: Generator reduction after Minkowski sum is sound.
/// The reduced zonotope contains the original Minkowski sum.
/// Proof: compression merges generators via absolute-value summation,
/// preserving per-dimension reach.
pub const T08B_MINKOWSKI_REDUCTION_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T08c: Residual connection containment.
/// For y = x + f(x), if x in Z_in and f(x) in Z_f, then y in Z_in + Z_f.
/// Direct application of T08a.
pub const T08C_RESIDUAL_CONTAINMENT: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Core operations
// ---------------------------------------------------------------------------

/// Compute the Minkowski sum Z₁ ⊕ Z₂.
///
/// center = c₁ + c₂, generators = concat(G₁, G₂).
/// Both zonotopes must have the same dimension.
///
/// This is the fundamental operation for skip/residual connections: if
/// x₁ ∈ Z₁ and x₂ ∈ Z₂ then x₁ + x₂ ∈ Z₁ ⊕ Z₂.
pub fn minkowski_sum(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
) -> Result<ConcreteZonotope, ZonotopeError> {
    z1.minkowski_sum(z2)
}

/// Verify Minkowski sum containment by sampling.
///
/// For `samples` random coefficient vectors, samples x₁ from Z₁ and x₂
/// from Z₂, computes x₁ + x₂, and checks membership in the interval hull
/// of Z₁ ⊕ Z₂. Returns `true` when all samples pass.
///
/// This is a runtime witness for T08a, not a formal proof.
#[must_use]
pub fn verify_minkowski_containment(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
    samples: usize,
) -> bool {
    let sum = z1.minkowski_add(z2);
    let (lo, hi) = sum.to_interval();
    let mut seed: u64 = 0xA1B2_C3D4_E5F6_0718;

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
            if s < lo[j] - TOL || s > hi[j] + TOL {
                return false;
            }
        }
    }
    true
}

/// Compute a tight axis-aligned box (interval hull) overapproximation of
/// the Minkowski sum Z₁ ⊕ Z₂.
///
/// Returns `(lower, upper)` where each is a d-dimensional vector.
/// This is equivalent to summing the interval hulls of Z₁ and Z₂
/// component-wise.
pub fn minkowski_overapprox(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
) -> Result<(Vec<f64>, Vec<f64>), ZonotopeError> {
    if z1.dim() != z2.dim() {
        return Err(ZonotopeError::OperandDimensionMismatch {
            left_dim: z1.dim(),
            right_dim: z2.dim(),
        });
    }
    let sum = z1.minkowski_add(z2);
    Ok(sum.to_interval())
}

/// Minkowski sum followed by generator reduction.
///
/// Computes Z₁ ⊕ Z₂ then compresses generators: keeps the `keep_count`
/// largest generators (by L2 norm) and merges the rest into one generator
/// via absolute-value summation.
///
/// The reduced zonotope has at most `keep_count + 1` generators and is
/// guaranteed to contain the exact Minkowski sum (T08b).
pub fn minkowski_with_reduction(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
    keep_count: usize,
) -> Result<ConcreteZonotope, ZonotopeError> {
    let sum = minkowski_sum(z1, z2)?;
    let n = sum.num_generators();
    if keep_count >= n {
        return Ok(sum);
    }
    let keep_indices = top_generators_by_norm(&sum, keep_count);
    Ok(sum.compress(&keep_indices))
}

/// Verify that the reduced zonotope contains the original Minkowski sum.
///
/// Checks that the interval hull of `reduced` contains the interval hull
/// of `full_sum`. Since compression preserves per-dimension absolute-value
/// sums (T12), the hulls should be identical.
#[must_use]
pub fn verify_reduction_sound(full_sum: &ConcreteZonotope, reduced: &ConcreteZonotope) -> bool {
    if full_sum.dim() != reduced.dim() {
        return false;
    }
    let (lo_full, hi_full) = full_sum.to_interval();
    let (lo_red, hi_red) = reduced.to_interval();

    lo_full
        .iter()
        .zip(lo_red.iter())
        .all(|(f, r)| *r <= *f + TOL)
        && hi_full
            .iter()
            .zip(hi_red.iter())
            .all(|(f, r)| *r >= *f - TOL)
}

/// Upper bound on the Hausdorff distance between Z₁ ⊕ Z₂ and its
/// generator-reduced form.
///
/// The Hausdorff distance is bounded by the L2 norm of the difference
/// between the merged-generator bounding box and individual generator
/// bounding boxes. In the worst case, this is the sum of the L2 norms
/// of the removed generators.
///
/// Returns 0.0 when no generators are removed (keep_count >= total).
#[must_use]
pub fn minkowski_hausdorff_bound(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
    keep_count: usize,
) -> f64 {
    let sum = z1.minkowski_add(z2);
    let n = sum.num_generators();
    if keep_count >= n {
        return 0.0;
    }

    let mut norms: Vec<(usize, f64)> = sum
        .generators
        .iter()
        .enumerate()
        .map(|(i, g)| {
            let norm = g.iter().map(|x| x * x).sum::<f64>().sqrt();
            (i, norm)
        })
        .collect();

    // Sort descending by norm; the ones NOT kept are the small ones.
    norms.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    // Removed generators are those after keep_count.
    norms[keep_count..].iter().map(|(_, norm)| norm).sum()
}

/// Compute the interval hull (bounding box) of the Minkowski sum Z₁ ⊕ Z₂.
///
/// Returns `(lower, upper)`. Equivalent to `minkowski_overapprox` but
/// with a clearer name for the common use case of bounding-box queries.
pub fn minkowski_interval_hull(
    z1: &ConcreteZonotope,
    z2: &ConcreteZonotope,
) -> Result<(Vec<f64>, Vec<f64>), ZonotopeError> {
    minkowski_overapprox(z1, z2)
}

/// Verify residual connection soundness.
///
/// For a residual connection y = x + f(x), given:
/// - `z_input`: zonotope containing x
/// - `z_branch`: zonotope containing f(x)
///
/// Verifies via sampling that x + f(x) is contained in z_input ⊕ z_branch.
/// Returns `true` when all `samples` random trials pass (T08c).
#[must_use]
pub fn verify_residual_sound(
    z_input: &ConcreteZonotope,
    z_branch: &ConcreteZonotope,
    samples: usize,
) -> bool {
    // A residual connection is exactly Minkowski sum: y = x + f(x),
    // x in z_input, f(x) in z_branch => y in z_input + z_branch.
    verify_minkowski_containment(z_input, z_branch, samples)
}

/// Predict the generator count after Minkowski sum: |G₁| + |G₂|.
///
/// Useful for capacity planning and deciding when to apply reduction.
#[must_use]
pub fn generator_count_after_sum(z1: &ConcreteZonotope, z2: &ConcreteZonotope) -> usize {
    z1.num_generators() + z2.num_generators()
}

/// Scalar scaling of a zonotope: alpha * Z.
///
/// Scales center and all generators by `alpha`. The resulting zonotope is
/// { alpha * c + sum_i eps_i * (alpha * g_i) : eps_i in [-1,1] }
/// = { alpha * x : x in Z }.
///
/// For negative `alpha`, the set is reflected through the origin (still a
/// valid zonotope since eps_i ranges over the full symmetric interval).
#[must_use]
pub fn minkowski_scaling(z: &ConcreteZonotope, alpha: f64) -> ConcreteZonotope {
    let new_center: Vec<f64> = z.center.iter().map(|c| alpha * c).collect();
    let new_generators: Vec<Vec<f64>> = z
        .generators
        .iter()
        .map(|g| g.iter().map(|x| alpha * x).collect())
        .collect();
    ConcreteZonotope::new(new_center, new_generators)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Tolerance for floating-point comparisons.
const TOL: f64 = 1e-9;

/// Deterministic pseudo-random f64 in [-1, 1] from mutable seed.
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

/// Return indices of the top `count` generators by L2 norm (descending).
fn top_generators_by_norm(z: &ConcreteZonotope, count: usize) -> Vec<usize> {
    let mut norms: Vec<(usize, f64)> = z
        .generators
        .iter()
        .enumerate()
        .map(|(i, g)| {
            let norm = g.iter().map(|x| x * x).sum::<f64>().sqrt();
            (i, norm)
        })
        .collect();
    norms.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    norms.iter().take(count).map(|(i, _)| *i).collect()
}
