// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope compression soundness (C001: T10-T12) and concrete compression
//! algorithms.
//!
//! Compression merges generators to reduce error term count while preserving
//! soundness. The proof is abstract over the choice of kept indices — no
//! sorting logic in the proof (gamma-crown sorts by L1 norm in Rust).
//!
//! Concrete algorithms: magnitude-based merging, PCA compression, and
//! Johnson-Lindenstrauss random projection.

use crate::spec::ProofStatus;

/// T10: compress_hull_sound
/// Z.to_interval.contains x -> (Z.compress kept).to_interval.contains x
///
/// Note: This is HULL-LEVEL containment, not exact zonotope containment.
/// A single merged generator with scalar e' cannot simultaneously match all
/// dimensions (AI Model 5.4 review). Since compression preserves per-dimension
/// Σ|gᵢⱼ| totals (T12), the interval hull is identical, so hull containment
/// is trivially preserved.
pub const T10_COMPRESS_HULL_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// T11: compress_projection_tightness
/// width(W · compress(Z)) ≤ width(W · Z) + 2 · W · Σ_merged
///
/// Note: The IMMEDIATE interval hull of a compressed zonotope is identical
/// to the original (T12). Tightness loss only appears after a subsequent
/// linear projection, because compression destroys cross-dimensional
/// correlations that a linear map could exploit.
pub const T11_COMPRESS_PROJECTION_TIGHTNESS: ProofStatus = ProofStatus::DerivedPending;

/// T12: compress_hull_exact
/// to_interval(compress(Z)) = to_interval(Z)
///
/// The interval hull is computed as center ± Σ|gᵢⱼ| per dimension.
/// Compression preserves this sum: the merged generator's contribution
/// equals the sum of the merged generators' absolute values.
pub const T12_COMPRESS_HULL_EXACT: ProofStatus = ProofStatus::DerivedPending;

// ---------------------------------------------------------------------------
// Concrete compression algorithms
// ---------------------------------------------------------------------------

/// L2 norm (Euclidean magnitude) of a generator vector.
#[must_use]
pub fn generator_magnitude(gvec: &[f64]) -> f64 {
    gvec.iter().map(|x| x * x).sum::<f64>().sqrt()
}

/// Rank generators by L2 magnitude, sorted descending.
///
/// Returns `(original_index, magnitude)` pairs. Ties are broken by index
/// (lower index first among equal magnitudes via the stable sort).
#[must_use]
pub fn rank_generators(generators: &[Vec<f64>]) -> Vec<(usize, f64)> {
    let mut ranked: Vec<(usize, f64)> = generators
        .iter()
        .enumerate()
        .map(|(i, g)| (i, generator_magnitude(g)))
        .collect();
    // Sort descending by magnitude. Stable sort preserves index order for ties.
    ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    ranked
}

/// Reduce generator count while preserving soundness by merging small
/// generators into an interval hull overapproximation.
///
/// Keeps the `target_count` largest generators (by L2 norm) unchanged.
/// All remaining generators are merged into a single generator whose j-th
/// component equals `Σ |g_ij|` over the merged set. This preserves the
/// interval hull exactly (T12).
///
/// If `target_count >= generators.len()`, returns the inputs unchanged.
/// If `generators` is empty, returns center unchanged with no generators.
#[must_use]
pub fn compress_generators(
    center: &[f64],
    generators: &[Vec<f64>],
    target_count: usize,
) -> (Vec<f64>, Vec<Vec<f64>>) {
    let n = generators.len();
    let d = center.len();

    if target_count >= n {
        return (center.to_vec(), generators.to_vec());
    }

    let ranked = rank_generators(generators);

    // Keep the top `target_count` generators by magnitude.
    let mut new_generators: Vec<Vec<f64>> = Vec::with_capacity(target_count + 1);
    let mut keep_set = vec![false; n];
    for &(idx, _) in ranked.iter().take(target_count) {
        keep_set[idx] = true;
        new_generators.push(generators[idx].clone());
    }

    // Merge the rest into an interval hull overapproximation generator.
    let mut merged = vec![0.0; d];
    let mut has_merged = false;
    for (i, gvec) in generators.iter().enumerate() {
        if !keep_set[i] {
            has_merged = true;
            for (j, val) in gvec.iter().enumerate() {
                merged[j] += val.abs();
            }
        }
    }
    if has_merged {
        new_generators.push(merged);
    }

    (center.to_vec(), new_generators)
}

/// PCA-based compression: keep top-k principal components via power iteration.
///
/// Computes an approximate eigendecomposition of G^T G (generator covariance)
/// using repeated power iteration. Each principal component captures the
/// direction of maximum remaining variance, with generators projected onto
/// that subspace.
///
/// Returns `target_count` generator vectors (or fewer if the input has fewer
/// generators or dimensions).
#[must_use]
pub fn pca_compress(generators: &[Vec<f64>], target_count: usize) -> Vec<Vec<f64>> {
    if generators.is_empty() || target_count == 0 {
        return Vec::new();
    }
    let n = generators.len();
    let d = generators.first().map_or(0, Vec::len);
    if d == 0 {
        return Vec::new();
    }
    let k = target_count.min(n).min(d);

    // Build G^T G (d x d covariance of generator columns).
    let mut cov = vec![vec![0.0; d]; d];
    for g in generators {
        for i in 0..d {
            for j in i..d {
                let val = g[i] * g[j];
                cov[i][j] += val;
                if i != j {
                    cov[j][i] += val;
                }
            }
        }
    }

    let mut result = Vec::with_capacity(k);
    let mut deflated = cov;
    let max_iters = 200;

    for _ in 0..k {
        // Power iteration to find dominant eigenvector.
        // Initialize with all-ones vector (normalized) to ensure overlap
        // with any eigenvector direction after deflation.
        let init_norm = (d as f64).sqrt();
        let mut v: Vec<f64> = vec![1.0 / init_norm; d];
        for _ in 0..max_iters {
            let mut new_v = vec![0.0; d];
            for i in 0..d {
                for j in 0..d {
                    new_v[i] += deflated[i][j] * v[j];
                }
            }
            let norm = new_v.iter().map(|x| x * x).sum::<f64>().sqrt();
            if norm < 1e-15 {
                break;
            }
            for x in &mut new_v {
                *x /= norm;
            }
            v = new_v;
        }

        // Compute eigenvalue: v^T A v
        let mut eigenvalue = 0.0;
        for i in 0..d {
            let mut row_dot = 0.0;
            for j in 0..d {
                row_dot += deflated[i][j] * v[j];
            }
            eigenvalue += v[i] * row_dot;
        }

        // Scale eigenvector by sqrt(eigenvalue) to get generator magnitude.
        let scale = eigenvalue.max(0.0).sqrt();
        let component: Vec<f64> = v.iter().map(|x| x * scale).collect();
        result.push(component);

        // Deflate: remove this component from the covariance matrix.
        for i in 0..d {
            for j in 0..d {
                deflated[i][j] -= eigenvalue * v[i] * v[j];
            }
        }
    }

    result
}

/// Verify the compressed zonotope contains the original by checking
/// interval hulls.
///
/// Returns `true` if for every dimension, the compressed interval hull
/// is at least as wide as the original. This is a necessary condition for
/// sound overapproximation.
#[must_use]
pub fn verify_compression_sound(
    original_center: &[f64],
    original_gens: &[Vec<f64>],
    compressed_center: &[f64],
    compressed_gens: &[Vec<f64>],
) -> bool {
    let d = original_center.len();
    if compressed_center.len() != d {
        return false;
    }
    let tol = 1e-9;

    for j in 0..d {
        let orig_spread: f64 = original_gens.iter().map(|g| g[j].abs()).sum();
        let comp_spread: f64 = compressed_gens.iter().map(|g| g[j].abs()).sum();

        let orig_lo = original_center[j] - orig_spread;
        let orig_hi = original_center[j] + orig_spread;
        let comp_lo = compressed_center[j] - comp_spread;
        let comp_hi = compressed_center[j] + comp_spread;

        // Compressed hull must contain original hull.
        if comp_lo > orig_lo + tol || comp_hi < orig_hi - tol {
            return false;
        }
    }
    true
}

/// Hausdorff-like error bound between original and compressed zonotopes.
///
/// Computes the maximum over all dimensions of the difference in interval
/// hull half-widths: `max_j | Σ|orig_gij| - Σ|comp_gij| |`. This gives
/// an upper bound on the Hausdorff distance between the two interval hulls.
#[must_use]
pub fn compression_error_bound(original_gens: &[Vec<f64>], compressed_gens: &[Vec<f64>]) -> f64 {
    if original_gens.is_empty() && compressed_gens.is_empty() {
        return 0.0;
    }
    let d = original_gens
        .first()
        .or(compressed_gens.first())
        .map_or(0, Vec::len);
    if d == 0 {
        return 0.0;
    }

    let mut max_diff = 0.0f64;
    for j in 0..d {
        let orig_spread: f64 = original_gens.iter().map(|g| g[j].abs()).sum();
        let comp_spread: f64 = compressed_gens.iter().map(|g| g[j].abs()).sum();
        max_diff = max_diff.max((orig_spread - comp_spread).abs());
    }
    max_diff
}

/// Johnson-Lindenstrauss style random projection compression.
///
/// Projects the n generators (each d-dimensional) through a random
/// `target_count x n` matrix with entries drawn from a simple hash-based
/// pseudo-random distribution, then scales appropriately.
///
/// Each output generator is a linear combination of the input generators,
/// preserving approximate distances with high probability (JL lemma).
///
/// The `seed` parameter ensures reproducibility.
#[must_use]
pub fn random_projection_compress(
    generators: &[Vec<f64>],
    target_count: usize,
    seed: u64,
) -> Vec<Vec<f64>> {
    if generators.is_empty() || target_count == 0 {
        return Vec::new();
    }
    let n = generators.len();
    let d = generators.first().map_or(0, Vec::len);
    if d == 0 {
        return Vec::new();
    }
    let k = target_count.min(n);
    let scale = (n as f64 / k as f64).sqrt();

    let mut result = Vec::with_capacity(k);
    for row in 0..k {
        let mut new_gen = vec![0.0; d];
        for (col, gvec) in generators.iter().enumerate() {
            // Simple hash-based random sign: deterministic from seed, row, col.
            let hash = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(row as u64)
                .wrapping_mul(2_862_933_555_777_941_757)
                .wrapping_add(col as u64);
            let sign = if hash.is_multiple_of(2) { 1.0 } else { -1.0 };
            for (j, val) in gvec.iter().enumerate() {
                new_gen[j] += sign * val;
            }
        }
        // Scale by sqrt(n/k) to preserve expected norms.
        for val in &mut new_gen {
            *val *= scale / (n as f64).sqrt();
        }
        result.push(new_gen);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        assert!(matches!(
            T10_COMPRESS_HULL_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T11_COMPRESS_PROJECTION_TIGHTNESS,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(
            T12_COMPRESS_HULL_EXACT,
            ProofStatus::DerivedPending
        ));
    }
}
