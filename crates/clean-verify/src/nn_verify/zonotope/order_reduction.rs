// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Zonotope order reduction strategies for keeping generator count manageable.
//!
//! Order reduction is essential in neural network verification: each ReLU
//! layer can add generators, causing exponential growth. These strategies
//! reduce generator count while preserving soundness (the reduced zonotope
//! over-approximates the original).
//!
//! Three strategies are provided:
//! - **Magnitude**: drop smallest generators, merge into interval hull error
//! - **PCA**: eigendecomposition-based reduction to target dimension
//! - **Girard**: sort by column norm, merge small generators into axis-aligned box

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

/// Tolerance for floating-point comparisons.
const TOL: f64 = 1e-9;

/// Number of sampling trials for soundness verification.
const DEFAULT_SAMPLES: usize = 500;

/// Reduce generator count by dropping smallest (by L2 magnitude) and merging
/// their contribution into a single interval-hull error generator.
///
/// The merged generator's j-th component equals `sum |g_ij|` over all dropped
/// generators, preserving the interval hull exactly (T12). This is the
/// simplest and most common order reduction strategy.
///
/// If `max_generators >= z.num_generators()`, returns a clone unchanged.
#[must_use]
pub(crate) fn reduce_by_magnitude(z: &ConcreteZonotope, max_generators: usize) -> ConcreteZonotope {
    let n = z.num_generators();
    if max_generators >= n {
        return z.clone();
    }

    let mut ranked = rank_by_l2(&z.generators);
    ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    let d = z.dim();
    let mut keep_set = vec![false; n];
    let mut new_generators: Vec<Vec<f64>> = Vec::with_capacity(max_generators + 1);

    for &(idx, _) in ranked.iter().take(max_generators) {
        keep_set[idx] = true;
        new_generators.push(z.generators[idx].clone());
    }

    let mut merged = vec![0.0; d];
    let mut has_merged = false;
    for (i, gvec) in z.generators.iter().enumerate() {
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

    ConcreteZonotope::new(z.center.clone(), new_generators)
}

/// Reduce generator count via PCA-based eigendecomposition approximation.
///
/// Computes the generator covariance matrix G^T G and extracts the top
/// `target_dim` principal components via power iteration. Each component
/// captures the direction of maximum remaining variance.
///
/// Unlike magnitude reduction, PCA can capture correlated structure across
/// dimensions, potentially giving tighter over-approximations when generators
/// are not axis-aligned.
///
/// If `target_dim == 0` or there are no generators, returns a point zonotope.
/// The result always has at most `target_dim` generators.
#[must_use]
pub(crate) fn reduce_by_pca(z: &ConcreteZonotope, target_dim: usize) -> ConcreteZonotope {
    if z.generators.is_empty() || target_dim == 0 {
        return ConcreteZonotope::new(z.center.clone(), Vec::new());
    }

    let n = z.num_generators();
    let d = z.dim();
    if d == 0 {
        return ConcreteZonotope::new(z.center.clone(), Vec::new());
    }

    let k = target_dim.min(n).min(d);
    let new_generators = pca_extract(d, &z.generators, k);
    ConcreteZonotope::new(z.center.clone(), new_generators)
}

/// Extract top-k principal component generators via power iteration.
fn pca_extract(d: usize, generators: &[Vec<f64>], k: usize) -> Vec<Vec<f64>> {
    let mut cov = build_covariance(d, generators);
    let max_iters = 200;
    let mut result = Vec::with_capacity(k);

    for _ in 0..k {
        let (eigvec, eigval) = power_iteration(&cov, d, max_iters);
        let scale = eigval.max(0.0).sqrt();
        let component: Vec<f64> = eigvec.iter().map(|x| x * scale).collect();
        result.push(component);
        deflate_matrix(&mut cov, &eigvec, eigval, d);
    }
    result
}

/// Build the d x d covariance matrix G^T G from generators.
fn build_covariance(d: usize, generators: &[Vec<f64>]) -> Vec<Vec<f64>> {
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
    cov
}

/// Single dominant eigenvector extraction via power iteration.
fn power_iteration(matrix: &[Vec<f64>], d: usize, max_iters: usize) -> (Vec<f64>, f64) {
    let init_norm = (d as f64).sqrt();
    let mut v: Vec<f64> = vec![1.0 / init_norm; d];

    for _ in 0..max_iters {
        let mut new_v = vec![0.0; d];
        for i in 0..d {
            for j in 0..d {
                new_v[i] += matrix[i][j] * v[j];
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
        let row_dot: f64 = matrix[i].iter().zip(v.iter()).map(|(a, b)| a * b).sum();
        eigenvalue += v[i] * row_dot;
    }
    (v, eigenvalue)
}

/// Deflate matrix by removing the contribution of an eigenvector.
fn deflate_matrix(matrix: &mut [Vec<f64>], eigvec: &[f64], eigval: f64, d: usize) {
    for i in 0..d {
        for j in 0..d {
            matrix[i][j] -= eigval * eigvec[i] * eigvec[j];
        }
    }
}

/// Girard's order reduction method.
///
/// Generators are sorted by their column norm (L1 norm across dimensions).
/// The `max_generators` largest are kept unchanged; the remaining small
/// generators are merged into an axis-aligned box (diagonal generator matrix).
///
/// The box is represented as `d` generators, one per dimension, where each
/// generator's j-th component equals the sum of absolute values of the j-th
/// components of all merged generators. This preserves the interval hull (T12)
/// while distributing the error across axis-aligned directions.
///
/// Girard's method is preferred when subsequent operations (like linear
/// transforms) benefit from axis-aligned error terms.
#[must_use]
pub(crate) fn reduce_girard(z: &ConcreteZonotope, max_generators: usize) -> ConcreteZonotope {
    let n = z.num_generators();
    if max_generators >= n {
        return z.clone();
    }

    let d = z.dim();
    let mut ranked = rank_by_column_norm(&z.generators, d);
    ranked.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    let mut keep_set = vec![false; n];
    let mut new_generators: Vec<Vec<f64>> = Vec::with_capacity(max_generators + d);

    for &(idx, _) in ranked.iter().take(max_generators) {
        keep_set[idx] = true;
        new_generators.push(z.generators[idx].clone());
    }

    // Merge remaining generators into axis-aligned box generators.
    let mut box_diag = vec![0.0; d];
    let mut has_merged = false;
    for (i, gvec) in z.generators.iter().enumerate() {
        if !keep_set[i] {
            has_merged = true;
            for (j, val) in gvec.iter().enumerate() {
                box_diag[j] += val.abs();
            }
        }
    }

    if has_merged {
        for j in 0..d {
            if box_diag[j] > TOL {
                let mut axis_gen = vec![0.0; d];
                axis_gen[j] = box_diag[j];
                new_generators.push(axis_gen);
            }
        }
    }

    ConcreteZonotope::new(z.center.clone(), new_generators)
}

/// Verify that a reduced zonotope over-approximates the original via sampling.
///
/// Samples random points from the original zonotope and checks that each
/// lies within the interval hull of the reduced zonotope. Returns `true`
/// if all sampled points are contained.
///
/// This is a probabilistic soundness check, not a formal proof. It uses
/// `DEFAULT_SAMPLES` (500) random coefficient vectors.
#[must_use]
pub(crate) fn verify_reduction_soundness(
    original: &ConcreteZonotope,
    reduced: &ConcreteZonotope,
) -> bool {
    debug_assert_eq!(
        original.dim(),
        reduced.dim(),
        "dimension mismatch in reduction soundness check"
    );

    let (lo, hi) = reduced.to_interval();
    let n = original.num_generators();
    let mut seed: u64 = 0xABCD_1234_5678_EF00;

    for _ in 0..DEFAULT_SAMPLES {
        let coeffs: Vec<f64> = (0..n).map(|_| pseudo_random(&mut seed)).collect();
        let point = match original.sample_point(&coeffs) {
            Ok(p) => p,
            Err(_) => return false,
        };
        for (j, &xj) in point.iter().enumerate() {
            if xj < lo[j] - TOL || xj > hi[j] + TOL {
                return false;
            }
        }
    }
    true
}

/// Hausdorff-like error estimate between original and reduced zonotopes.
///
/// Computes the maximum over all dimensions of the absolute difference in
/// interval hull half-widths: `max_j | hw_orig_j - hw_reduced_j |`.
///
/// This gives an upper bound on the Hausdorff distance between the two
/// interval hulls. A value of 0 means the interval hulls are identical.
#[must_use]
pub(crate) fn reduction_error_bound(
    original: &ConcreteZonotope,
    reduced: &ConcreteZonotope,
) -> f64 {
    debug_assert_eq!(
        original.dim(),
        reduced.dim(),
        "dimension mismatch in error bound computation"
    );

    let d = original.dim();
    if d == 0 {
        return 0.0;
    }

    let mut max_diff = 0.0f64;
    for j in 0..d {
        let orig_spread: f64 = original.generators.iter().map(|g| g[j].abs()).sum();
        let reduced_spread: f64 = reduced.generators.iter().map(|g| g[j].abs()).sum();
        max_diff = max_diff.max((orig_spread - reduced_spread).abs());
    }
    max_diff
}

/// Rank generators by L2 norm. Returns `(index, magnitude)` pairs.
fn rank_by_l2(generators: &[Vec<f64>]) -> Vec<(usize, f64)> {
    generators
        .iter()
        .enumerate()
        .map(|(i, g)| {
            let mag = g.iter().map(|x| x * x).sum::<f64>().sqrt();
            (i, mag)
        })
        .collect()
}

/// Rank generators by column norm (L1 norm across all dimensions).
/// Returns `(index, column_norm)` pairs.
fn rank_by_column_norm(generators: &[Vec<f64>], d: usize) -> Vec<(usize, f64)> {
    generators
        .iter()
        .enumerate()
        .map(|(i, g)| {
            let norm: f64 = (0..d).map(|j| g[j].abs()).sum();
            (i, norm)
        })
        .collect()
}
