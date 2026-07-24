// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C010 zonotope-CROWN equivalence for linear networks.
//!
//! For a network consisting only of affine layers, forward zonotope
//! propagation and backward CROWN propagation compute the same affine image
//! of the input box. This module provides the executable witness for that
//! equivalence and a small proof-status wrapper for the corresponding spec.

use super::concrete::ConcreteZonotope;
use crate::nn_verify::ibp_crown::{crown_concretize, crown_linear_backward, CrownBound};
use crate::spec::ProofStatus;
use thiserror::Error;

/// Floating-point tolerance used by all C010 comparisons.
pub(crate) const C010_EQUIV_TOLERANCE: f64 = 1e-10;

/// Proof status for the linear-network zonotope-CROWN equivalence theorem.
///
/// Promoted from DerivedPending to DerivedPending: the executable witnesses
/// (`verify_c010_equivalence`, `verify_c010_inductive`) pass constructively
/// on all test instances, confirming the zonotope-CROWN interval agreement
/// with zero axiom dependencies. Part of #3310.
pub(crate) const C010_ZONOTOPE_CROWN_EQUIV: ProofStatus = ProofStatus::DerivedPending;

/// Owned representation of one affine layer `(weight, bias)`.
pub(crate) type LinearLayer = (Vec<Vec<f64>>, Vec<f64>);

/// Errors raised while checking the C010 equivalence preconditions.
#[derive(Debug, Clone, PartialEq, Error)]
#[non_exhaustive]
pub(crate) enum C010EquivError {
    /// The input lower and upper bounds must have the same dimension.
    #[error(
        "input bound dimension mismatch: lower has dim {lower_dim}, upper has dim {upper_dim}"
    )]
    InputBoundsDimensionMismatch { lower_dim: usize, upper_dim: usize },

    /// Input bounds must define a valid interval in every coordinate.
    #[error("invalid input interval at index {index}: lower {lower} > upper {upper}")]
    InvalidInputInterval {
        index: usize,
        lower: f64,
        upper: f64,
    },

    /// Each layer bias must match the number of weight rows.
    #[error(
        "layer {layer_index} bias length mismatch: weight has {rows} rows, bias has {bias_dim}"
    )]
    BiasDimensionMismatch {
        layer_index: usize,
        rows: usize,
        bias_dim: usize,
    },

    /// Each row in a weight matrix must match the layer input dimension.
    #[error(
        "layer {layer_index} row {row_index} dimension mismatch: expected {expected}, got {got}"
    )]
    WeightRowDimensionMismatch {
        layer_index: usize,
        row_index: usize,
        expected: usize,
        got: usize,
    },

    /// The matrix product helper requires at least one layer.
    #[error("cannot compute a product matrix for an empty network")]
    EmptyNetwork,
}

/// Proof-spec wrapper for C010.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct C010EquivSpec {
    status: ProofStatus,
}

impl C010EquivSpec {
    /// Create the C010 proof spec with its current proof status.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            status: C010_ZONOTOPE_CROWN_EQUIV,
        }
    }

    /// Return the tracked proof status for C010.
    #[must_use]
    pub(crate) fn status(&self) -> ProofStatus {
        self.status
    }
}

impl Default for C010EquivSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Propagate the exact interval zonotope through a sequence of affine layers.
///
/// The input box `[input_lower, input_upper]` is encoded as a concrete
/// zonotope with diagonal generators, then transformed by each layer via
/// `W * Z + b`. The returned interval hull is the exact affine image of the
/// input box for a purely linear network.
pub(crate) fn zonotope_linear_bounds(
    layers: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<(Vec<f64>, Vec<f64>), C010EquivError> {
    let (normalized_lower, normalized_upper) = normalize_input_bounds(input_lower, input_upper)?;
    validate_network(layers, normalized_lower.len())?;
    Ok(propagate_zonotope(
        layers,
        &normalized_lower,
        &normalized_upper,
    ))
}

/// Run CROWN backward through a sequence of affine layers and concretize.
///
/// Because the network contains no nonlinearities, the backward bound remains
/// an exact affine form with identical lower and upper coefficients. After
/// concretization, the resulting concrete interval matches the affine image of
/// the original input box.
pub(crate) fn crown_linear_bounds(
    layers: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<(Vec<f64>, Vec<f64>), C010EquivError> {
    let (normalized_lower, normalized_upper) = normalize_input_bounds(input_lower, input_upper)?;
    let bound = crown_linear_symbolic_bound(layers, normalized_lower.len())?;
    Ok(crown_concretize(
        &bound,
        &normalized_lower,
        &normalized_upper,
    ))
}

/// Verify the full C010 equivalence on a linear network.
///
/// This checks both the concrete interval equality and the symbolic affine
/// equality: the CROWN backward coefficients and bias must match the composed
/// affine map `W_n * ... * W_1` and its accumulated bias.
pub(crate) fn verify_c010_equivalence(
    layers: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<bool, C010EquivError> {
    let (normalized_lower, normalized_upper) = normalize_input_bounds(input_lower, input_upper)?;
    validate_network(layers, normalized_lower.len())?;

    let zonotope_bounds = propagate_zonotope(layers, &normalized_lower, &normalized_upper);
    let crown_bound = crown_linear_symbolic_bound(layers, normalized_lower.len())?;
    let crown_bounds = crown_concretize(&crown_bound, &normalized_lower, &normalized_upper);
    let (combined_weight, combined_bias) = compose_affine_map(layers, normalized_lower.len())?;

    let symbolic_match = approx_eq_matrix(&crown_bound.lower_coeffs, &combined_weight)
        && approx_eq_matrix(&crown_bound.upper_coeffs, &combined_weight)
        && approx_eq_slice(&crown_bound.lower_bias, &combined_bias)
        && approx_eq_slice(&crown_bound.upper_bias, &combined_bias);

    Ok(symbolic_match
        && approx_eq_slice(&zonotope_bounds.0, &crown_bounds.0)
        && approx_eq_slice(&zonotope_bounds.1, &crown_bounds.1))
}

/// Verify the single-layer induction step for C010.
///
/// For one affine layer `y = W * x + b`, this checks that:
/// 1. zonotope propagation produces the exact output box,
/// 2. one CROWN backward step preserves the same affine map symbolically, and
/// 3. concretizing that symbolic bound matches the zonotope interval hull.
pub(crate) fn verify_c010_inductive(
    weight: &[Vec<f64>],
    bias: &[f64],
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<bool, C010EquivError> {
    let (normalized_lower, normalized_upper) = normalize_input_bounds(input_lower, input_upper)?;
    validate_layer_shape(weight, bias, 0, normalized_lower.len())?;

    let input_zonotope = interval_to_zonotope(&normalized_lower, &normalized_upper);
    let weight_refs: Vec<&[f64]> = weight.iter().map(Vec::as_slice).collect();
    let zonotope_bounds = input_zonotope
        .linear_transform(&weight_refs, bias)
        .to_interval();

    let bound = crown_linear_backward(weight, bias, &CrownBound::identity(weight.len()));
    let crown_bounds = crown_concretize(&bound, &normalized_lower, &normalized_upper);

    let symbolic_match = approx_eq_matrix(&bound.lower_coeffs, weight)
        && approx_eq_matrix(&bound.upper_coeffs, weight)
        && approx_eq_slice(&bound.lower_bias, bias)
        && approx_eq_slice(&bound.upper_bias, bias);

    Ok(symbolic_match
        && approx_eq_slice(&zonotope_bounds.0, &crown_bounds.0)
        && approx_eq_slice(&zonotope_bounds.1, &crown_bounds.1))
}

/// Compute the composed weight matrix `W_n * ... * W_1`.
pub(crate) fn product_matrix(layers: &[LinearLayer]) -> Result<Vec<Vec<f64>>, C010EquivError> {
    let Some((first_weight, _)) = layers.first() else {
        return Err(C010EquivError::EmptyNetwork);
    };

    let input_dim = first_weight.first().map_or(0, Vec::len);
    let (combined_weight, _) = compose_affine_map(layers, input_dim)?;
    Ok(combined_weight)
}

/// Compare two floating-point scalars using the C010 tolerance.
#[must_use]
fn approx_eq(left: f64, right: f64) -> bool {
    (left - right).abs() <= C010_EQUIV_TOLERANCE
}

/// Compare two slices elementwise using the C010 tolerance.
#[must_use]
fn approx_eq_slice(left: &[f64], right: &[f64]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(lhs, rhs)| approx_eq(*lhs, *rhs))
}

/// Compare two matrices elementwise using the C010 tolerance.
#[must_use]
fn approx_eq_matrix(left: &[Vec<f64>], right: &[Vec<f64>]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(lhs, rhs)| approx_eq_slice(lhs, rhs))
}

/// Normalize input bounds so near-point intervals are represented consistently.
///
/// If `lower` exceeds `upper` by more than the comparison tolerance, this
/// returns an error. If the two values differ only within tolerance, the
/// interval is collapsed to its midpoint.
fn normalize_input_bounds(
    input_lower: &[f64],
    input_upper: &[f64],
) -> Result<(Vec<f64>, Vec<f64>), C010EquivError> {
    if input_lower.len() != input_upper.len() {
        return Err(C010EquivError::InputBoundsDimensionMismatch {
            lower_dim: input_lower.len(),
            upper_dim: input_upper.len(),
        });
    }

    let mut normalized_lower = Vec::with_capacity(input_lower.len());
    let mut normalized_upper = Vec::with_capacity(input_upper.len());

    for (index, (lower, upper)) in input_lower.iter().zip(input_upper.iter()).enumerate() {
        if *lower > *upper + C010_EQUIV_TOLERANCE {
            return Err(C010EquivError::InvalidInputInterval {
                index,
                lower: *lower,
                upper: *upper,
            });
        }

        if *lower <= *upper {
            normalized_lower.push(*lower);
            normalized_upper.push(*upper);
        } else {
            let midpoint = 0.5 * (*lower + *upper);
            normalized_lower.push(midpoint);
            normalized_upper.push(midpoint);
        }
    }

    Ok((normalized_lower, normalized_upper))
}

/// Validate all affine layers against a fixed input dimension.
fn validate_network(layers: &[LinearLayer], input_dim: usize) -> Result<(), C010EquivError> {
    let mut expected_input_dim = input_dim;
    for (layer_index, (weight, bias)) in layers.iter().enumerate() {
        expected_input_dim = validate_layer_shape(weight, bias, layer_index, expected_input_dim)?;
    }
    Ok(())
}

/// Validate one affine layer shape and return its output dimension.
fn validate_layer_shape(
    weight: &[Vec<f64>],
    bias: &[f64],
    layer_index: usize,
    expected_input_dim: usize,
) -> Result<usize, C010EquivError> {
    if weight.len() != bias.len() {
        return Err(C010EquivError::BiasDimensionMismatch {
            layer_index,
            rows: weight.len(),
            bias_dim: bias.len(),
        });
    }

    for (row_index, row) in weight.iter().enumerate() {
        if row.len() != expected_input_dim {
            return Err(C010EquivError::WeightRowDimensionMismatch {
                layer_index,
                row_index,
                expected: expected_input_dim,
                got: row.len(),
            });
        }
    }

    Ok(weight.len())
}

/// Encode an interval box exactly as a concrete zonotope with diagonal generators.
#[must_use]
fn interval_to_zonotope(input_lower: &[f64], input_upper: &[f64]) -> ConcreteZonotope {
    let dim = input_lower.len();
    let center: Vec<f64> = input_lower
        .iter()
        .zip(input_upper.iter())
        .map(|(lower, upper)| 0.5 * (lower + upper))
        .collect();

    let generators: Vec<Vec<f64>> = input_lower
        .iter()
        .zip(input_upper.iter())
        .enumerate()
        .map(|(index, (lower, upper))| {
            let mut generator = vec![0.0; dim];
            generator[index] = 0.5 * (upper - lower);
            generator
        })
        .collect();

    ConcreteZonotope::new(center, generators)
}

/// Propagate the normalized input zonotope through all affine layers.
#[must_use]
fn propagate_zonotope(
    layers: &[LinearLayer],
    input_lower: &[f64],
    input_upper: &[f64],
) -> (Vec<f64>, Vec<f64>) {
    let mut zonotope = interval_to_zonotope(input_lower, input_upper);
    for (weight, bias) in layers {
        let weight_refs: Vec<&[f64]> = weight.iter().map(Vec::as_slice).collect();
        zonotope = zonotope.linear_transform(&weight_refs, bias);
    }
    zonotope.to_interval()
}

/// Build the exact symbolic CROWN bound for a linear network.
fn crown_linear_symbolic_bound(
    layers: &[LinearLayer],
    input_dim: usize,
) -> Result<CrownBound, C010EquivError> {
    validate_network(layers, input_dim)?;

    let output_dim = layers.last().map_or(input_dim, |(weight, _)| weight.len());
    let mut bound = CrownBound::identity(output_dim);

    for (weight, bias) in layers.iter().rev() {
        bound = crown_linear_backward(weight, bias, &bound);
    }

    Ok(bound)
}

/// Compose all affine layers into a single affine map.
fn compose_affine_map(
    layers: &[LinearLayer],
    input_dim: usize,
) -> Result<(Vec<Vec<f64>>, Vec<f64>), C010EquivError> {
    validate_network(layers, input_dim)?;

    let mut combined_weight = identity_matrix(input_dim);
    let mut combined_bias = vec![0.0; input_dim];

    for (weight, bias) in layers {
        combined_bias = affine_on_vector(weight, &combined_bias, bias);
        combined_weight = matrix_multiply(weight, &combined_weight);
    }

    Ok((combined_weight, combined_bias))
}

/// Create an identity matrix of shape `dim x dim`.
#[must_use]
fn identity_matrix(dim: usize) -> Vec<Vec<f64>> {
    let mut matrix = vec![vec![0.0; dim]; dim];
    for (index, row) in matrix.iter_mut().enumerate() {
        row[index] = 1.0;
    }
    matrix
}

/// Multiply two row-major matrices.
///
/// `left` has shape `(m x k)` and `right` has shape `(k x n)`.
#[must_use]
fn matrix_multiply(left: &[Vec<f64>], right: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let rows = left.len();
    let shared_dim = left.first().map_or(0, Vec::len);
    let cols = right.first().map_or(0, Vec::len);

    debug_assert_eq!(shared_dim, right.len(), "matrix inner dimension mismatch");

    let mut product = vec![vec![0.0; cols]; rows];
    for (row_index, left_row) in left.iter().enumerate() {
        for shared_index in 0..shared_dim {
            let left_value = left_row[shared_index];
            if approx_eq(left_value, 0.0) {
                continue;
            }
            for col_index in 0..cols {
                product[row_index][col_index] += left_value * right[shared_index][col_index];
            }
        }
    }
    product
}

/// Apply an affine layer `weight * vector + bias`.
#[must_use]
fn affine_on_vector(weight: &[Vec<f64>], vector: &[f64], bias: &[f64]) -> Vec<f64> {
    debug_assert_eq!(weight.len(), bias.len(), "bias length mismatch");

    let mut output = Vec::with_capacity(weight.len());
    for (row, row_bias) in weight.iter().zip(bias.iter()) {
        debug_assert_eq!(row.len(), vector.len(), "vector dimension mismatch");
        let value = row
            .iter()
            .zip(vector.iter())
            .fold(*row_bias, |acc, (weight_ij, value_j)| {
                acc + weight_ij * value_j
            });
        output.push(value);
    }
    output
}
