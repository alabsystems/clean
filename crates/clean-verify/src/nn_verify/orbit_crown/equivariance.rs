// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weight equivariance verification for neural network layers.
//!
//! A weight matrix W is **equivariant** under a symmetry group G if:
//!   `W * rho(g) = rho(g) * W` for all group elements g in G.
//!
//! Equivalently, W commutes with all representation matrices rho(g).
//!
//! Since checking all group elements is expensive (|G| may be large),
//! it suffices to check the generators: if W commutes with all generators,
//! it commutes with all products of generators, hence all group elements.
//!
//! ## Verification Strategy
//!
//! For each generator g:
//! 1. Compute `rho(g)` (permutation matrix from g.mapping).
//! 2. Compute `diff = W * rho(g) - rho(g) * W`.
//! 3. Check `||diff||_F < eps` (Frobenius norm tolerance).
//!
//! The tolerance `eps` accounts for floating-point imprecision in
//! approximately-equivariant networks (e.g., trained with soft equivariance
//! constraints).

use super::symmetry::{GroupElement, SymmetryGroup};

/// Error type for equivariance verification.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum EquivarianceError {
    /// Weight matrix is not equivariant: the commutator norm exceeds tolerance.
    NotEquivariant {
        /// Index of the generator that fails the equivariance check.
        generator_index: usize,
        /// Frobenius norm of `W * rho(g) - rho(g) * W`.
        commutator_norm: f64,
        /// Tolerance that was exceeded.
        tolerance: f64,
    },
    /// Dimension mismatch between weight matrix and group action.
    DimensionMismatch {
        weight_rows: usize,
        weight_cols: usize,
        group_dim: usize,
    },
}

impl std::fmt::Display for EquivarianceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotEquivariant {
                generator_index,
                commutator_norm,
                tolerance,
            } => {
                write!(
                    f,
                    "weight not equivariant: generator {generator_index} has \
                     commutator norm {commutator_norm:.6e} > tolerance {tolerance:.6e}"
                )
            }
            Self::DimensionMismatch {
                weight_rows,
                weight_cols,
                group_dim,
            } => {
                write!(
                    f,
                    "dimension mismatch: weight is {weight_rows}x{weight_cols}, \
                     group acts on R^{group_dim}"
                )
            }
        }
    }
}

impl std::error::Error for EquivarianceError {}

/// Result of an equivariance verification check.
#[derive(Debug, Clone, PartialEq)]
pub struct EquivarianceResult {
    /// Whether the weight matrix is equivariant within tolerance.
    pub is_equivariant: bool,
    /// Maximum commutator norm across all generators.
    pub max_commutator_norm: f64,
    /// Per-generator commutator norms.
    pub generator_norms: Vec<f64>,
    /// Tolerance used for the check.
    pub tolerance: f64,
}

/// Verify that a square weight matrix W commutes with all generators of G.
///
/// Returns `Ok(EquivarianceResult)` with `is_equivariant = true` if
/// `||W * rho(g) - rho(g) * W||_F < tolerance` for all generators g.
///
/// # Errors
///
/// Returns `EquivarianceError::DimensionMismatch` if the weight matrix
/// dimensions don't match the group's action dimension.
pub fn verify_equivariance(
    weight: &[Vec<f64>],
    group: &dyn SymmetryGroup,
    tolerance: f64,
) -> Result<EquivarianceResult, EquivarianceError> {
    let n = group.dim();
    if weight.len() != n {
        return Err(EquivarianceError::DimensionMismatch {
            weight_rows: weight.len(),
            weight_cols: weight.first().map_or(0, |r| r.len()),
            group_dim: n,
        });
    }
    for row in weight {
        if row.len() != n {
            return Err(EquivarianceError::DimensionMismatch {
                weight_rows: weight.len(),
                weight_cols: row.len(),
                group_dim: n,
            });
        }
    }

    let generators = group.generators();
    verify_equivariance_generators(weight, &generators, tolerance)
}

/// Verify equivariance against an explicit list of generators.
///
/// This is the core computation: for each generator g, compute
/// `||W * rho(g) - rho(g) * W||_F` and check against tolerance.
///
/// # Errors
///
/// Returns `EquivarianceError::NotEquivariant` with details of the first
/// generator that violates equivariance (for diagnostic purposes, all
/// generators are still checked and norms reported).
pub fn verify_equivariance_generators(
    weight: &[Vec<f64>],
    generators: &[GroupElement],
    tolerance: f64,
) -> Result<EquivarianceResult, EquivarianceError> {
    let n = weight.len();
    let mut generator_norms = Vec::with_capacity(generators.len());
    let mut max_norm = 0.0_f64;

    for generator in generators {
        let rho = generator.to_permutation_matrix();
        let norm = commutator_frobenius_norm(weight, &rho, n);
        generator_norms.push(norm);
        max_norm = max_norm.max(norm);
    }

    let is_equivariant = max_norm < tolerance;

    Ok(EquivarianceResult {
        is_equivariant,
        max_commutator_norm: max_norm,
        generator_norms,
        tolerance,
    })
}

/// Compute the Frobenius norm of the commutator `W * R - R * W`.
///
/// This avoids allocating the full commutator matrix by computing the
/// norm element-by-element.
fn commutator_frobenius_norm(w: &[Vec<f64>], rho: &[Vec<f64>], n: usize) -> f64 {
    let mut sum_sq = 0.0;
    for i in 0..n {
        for j in 0..n {
            // (W * R)[i][j] = sum_k W[i][k] * R[k][j]
            let wr_ij: f64 = (0..n).map(|k| w[i][k] * rho[k][j]).sum();
            // (R * W)[i][j] = sum_k R[i][k] * W[k][j]
            let rw_ij: f64 = (0..n).map(|k| rho[i][k] * w[k][j]).sum();
            let diff = wr_ij - rw_ij;
            sum_sq += diff * diff;
        }
    }
    sum_sq.sqrt()
}
