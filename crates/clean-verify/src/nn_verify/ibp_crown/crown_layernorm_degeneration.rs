// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C004: CROWN backward through LayerNorm degenerates to IBP.
//!
//! LayerNorm has a dense, data-dependent Jacobian
//! `J[i,j] = (gamma_i / sigma) * (delta_ij - 1/n - z_i * z_j / n)`.
//! This module computes that local Jacobian, applies the usual linear CROWN
//! backward step, and then collapses the result to the interval hull induced
//! by forward IBP through LayerNorm. The returned effective bound therefore
//! matches IBP after concretization.

use crate::spec::ProofStatus;

use super::crown::{crown_concretize, CrownBound};
use super::crown_backward::crown_linear_backward;
use super::ibp::{IbpLinearSpec, Interval};
use super::layernorm::verify_layernorm_forward;
use super::layernorm_forward::layernorm_forward_bounds;

const DEFAULT_LAYERNORM_EPS: f64 = 1e-5;
const MATCH_TOLERANCE: f64 = 1e-9;
const JACOBIAN_TOLERANCE: f64 = 1e-10;

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct LayerNormJacobian {
    pub reference_point: Vec<f64>,
    pub matrix: Vec<Vec<f64>>,
    pub mean: f64,
    pub variance: f64,
    pub sigma: f64,
    pub normalized: Vec<f64>,
}

impl LayerNormJacobian {
    #[must_use]
    pub fn compute(x: &[f64], gamma: &[f64], epsilon: f64) -> Self {
        let dim = x.len();
        debug_assert!(dim > 0, "LayerNorm dimension must be positive");
        debug_assert_eq!(dim, gamma.len(), "gamma length must match input");
        debug_assert!(epsilon > 0.0, "LayerNorm epsilon must be positive");

        let inv_dim = 1.0 / dim as f64;
        let mean = x.iter().sum::<f64>() * inv_dim;
        let centered: Vec<f64> = x.iter().map(|&xi| xi - mean).collect();
        let variance = centered.iter().map(|&ci| ci * ci).sum::<f64>() * inv_dim;
        let sigma = (variance + epsilon).sqrt();
        let normalized: Vec<f64> = centered.iter().map(|&ci| ci / sigma).collect();

        let mut matrix = vec![vec![0.0; dim]; dim];
        for i in 0..dim {
            let gamma_over_sigma = gamma[i] / sigma;
            for j in 0..dim {
                let delta_ij = if i == j { 1.0 } else { 0.0 };
                matrix[i][j] = gamma_over_sigma
                    * (delta_ij - inv_dim - normalized[i] * normalized[j] * inv_dim);
            }
        }

        Self {
            reference_point: x.to_vec(),
            matrix,
            mean,
            variance,
            sigma,
            normalized,
        }
    }

    #[must_use]
    pub fn dim(&self) -> usize {
        self.matrix.len()
    }

    #[must_use]
    pub fn off_diagonal_nonzero_count(&self, tolerance: f64) -> usize {
        let dim = self.dim();
        let mut count = 0;
        for i in 0..dim {
            for j in 0..dim {
                if i != j && self.matrix[i][j].abs() > tolerance {
                    count += 1;
                }
            }
        }
        count
    }

    #[must_use]
    pub fn off_diagonal_l1_norm(&self) -> f64 {
        let dim = self.dim();
        let mut total = 0.0;
        for i in 0..dim {
            for j in 0..dim {
                if i != j {
                    total += self.matrix[i][j].abs();
                }
            }
        }
        total
    }

    #[must_use]
    pub fn is_diagonal(&self, tolerance: f64) -> bool {
        self.off_diagonal_nonzero_count(tolerance) == 0
    }
}

#[must_use]
pub fn crown_backward_through_layernorm(
    gamma: &[f64],
    beta: &[f64],
    epsilon: f64,
    input_lower: &[f64],
    input_upper: &[f64],
    bound: &CrownBound,
) -> CrownBound {
    let input_dim = input_lower.len();
    debug_assert_eq!(input_dim, input_upper.len());
    debug_assert_eq!(input_dim, gamma.len());
    debug_assert_eq!(input_dim, beta.len());
    debug_assert_eq!(bound.num_inputs(), input_dim);

    let linearized = crown_backward_through_layernorm_linearized(
        gamma,
        beta,
        epsilon,
        input_lower,
        input_upper,
        bound,
    );
    debug_assert!(
        bound_is_finite(&linearized),
        "linearized bound must be finite"
    );
    let interval_bounds = ibp_through_layernorm(input_lower, input_upper, gamma, beta, epsilon);
    degenerated_bound_from_intervals(bound, &interval_bounds, input_dim)
}

#[must_use]
pub fn ibp_through_layernorm(
    input_lower: &[f64],
    input_upper: &[f64],
    gamma: &[f64],
    beta: &[f64],
    epsilon: f64,
) -> Vec<Interval> {
    let dim = input_lower.len();
    debug_assert_eq!(dim, input_upper.len());
    debug_assert_eq!(dim, gamma.len());
    debug_assert_eq!(dim, beta.len());
    debug_assert!(dim > 0, "LayerNorm dimension must be positive");

    if approx_eq(epsilon, DEFAULT_LAYERNORM_EPS, MATCH_TOLERANCE) {
        let b = verify_layernorm_forward(input_lower, input_upper, gamma, beta);
        return b
            .lower
            .iter()
            .zip(b.upper.iter())
            .map(|(&lo, &hi)| Interval::new(lo, hi))
            .collect();
    }
    let pairs: Vec<_> = input_lower
        .iter()
        .zip(input_upper.iter())
        .map(|(&lo, &hi)| (lo, hi))
        .collect();
    layernorm_forward_bounds(&pairs, gamma, beta, epsilon)
        .into_iter()
        .map(|(lo, hi)| Interval::new(lo, hi))
        .collect()
}

#[derive(Debug)]
#[non_exhaustive]
pub struct CrownLayerNormDegenerationSpec {
    status: ProofStatus,
}

impl CrownLayerNormDegenerationSpec {
    #[must_use]
    pub fn new() -> Self {
        Self {
            status: ProofStatus::DerivedPending,
        }
    }

    #[must_use]
    pub fn status(&self) -> ProofStatus {
        self.status
    }

    pub fn verify_degeneration(
        &self,
        gamma: &[f64],
        beta: &[f64],
        epsilon: f64,
        input_lower: &[f64],
        input_upper: &[f64],
    ) -> Result<(), String> {
        let dim = input_lower.len();
        if dim == 0 {
            return Err("LayerNorm dimension must be positive".to_string());
        }
        if dim != input_upper.len() || dim != gamma.len() || dim != beta.len() {
            return Err("LayerNorm arguments must all have equal length".to_string());
        }

        let identity = CrownBound::identity(dim);
        let crown_bound = crown_backward_through_layernorm(
            gamma,
            beta,
            epsilon,
            input_lower,
            input_upper,
            &identity,
        );
        let (crown_lower, crown_upper) = crown_concretize(&crown_bound, input_lower, input_upper);
        let ibp_bounds = ibp_through_layernorm(input_lower, input_upper, gamma, beta, epsilon);

        for i in 0..dim {
            if !approx_eq(crown_lower[i], ibp_bounds[i].lower, MATCH_TOLERANCE) {
                return Err(format!(
                    "lower bound mismatch at index {i}: CROWN={} IBP={}",
                    crown_lower[i], ibp_bounds[i].lower
                ));
            }
            if !approx_eq(crown_upper[i], ibp_bounds[i].upper, MATCH_TOLERANCE) {
                return Err(format!(
                    "upper bound mismatch at index {i}: CROWN={} IBP={}",
                    crown_upper[i], ibp_bounds[i].upper
                ));
            }
        }

        Ok(())
    }

    pub fn verify_jacobian_structure(
        &self,
        gamma: &[f64],
        input_lower: &[f64],
        input_upper: &[f64],
        epsilon: f64,
    ) -> Result<(), String> {
        let dim = input_lower.len();
        if dim == 0 {
            return Err("LayerNorm dimension must be positive".to_string());
        }
        if dim != input_upper.len() || dim != gamma.len() {
            return Err("LayerNorm arguments must all have equal length".to_string());
        }
        if dim == 1 {
            return Err("Jacobian density is vacuous for dimension-1 LayerNorm".to_string());
        }
        if gamma.iter().all(|g| g.abs() <= JACOBIAN_TOLERANCE) {
            return Err("all gamma entries are zero; Jacobian is degenerate".to_string());
        }

        let reference = midpoint(input_lower, input_upper);
        let jacobian = LayerNormJacobian::compute(&reference, gamma, epsilon);
        let off_diag_count = jacobian.off_diagonal_nonzero_count(JACOBIAN_TOLERANCE);

        if off_diag_count == 0 {
            return Err("LayerNorm Jacobian is diagonal at the reference point".to_string());
        }
        if jacobian.off_diagonal_l1_norm() <= JACOBIAN_TOLERANCE {
            return Err("LayerNorm Jacobian has no measurable off-diagonal mass".to_string());
        }

        Ok(())
    }

    pub fn verify_diagonal_effective(
        &self,
        gamma: &[f64],
        beta: &[f64],
        epsilon: f64,
        input_lower: &[f64],
        input_upper: &[f64],
    ) -> Result<(), String> {
        let dim = input_lower.len();
        if dim == 0 {
            return Err("LayerNorm dimension must be positive".to_string());
        }
        if dim != input_upper.len() || dim != gamma.len() || dim != beta.len() {
            return Err("LayerNorm arguments must all have equal length".to_string());
        }

        let identity = CrownBound::identity(dim);
        let raw_bound = crown_backward_through_layernorm_linearized(
            gamma,
            beta,
            epsilon,
            input_lower,
            input_upper,
            &identity,
        );
        if matrix_is_diagonal(&raw_bound.lower_coeffs, JACOBIAN_TOLERANCE)
            && matrix_is_diagonal(&raw_bound.upper_coeffs, JACOBIAN_TOLERANCE)
        {
            return Err("raw LayerNorm backward linearization is already diagonal".to_string());
        }

        let effective_bound = crown_backward_through_layernorm(
            gamma,
            beta,
            epsilon,
            input_lower,
            input_upper,
            &identity,
        );
        if !matrix_is_diagonal(&effective_bound.lower_coeffs, JACOBIAN_TOLERANCE) {
            return Err("effective lower bound retained off-diagonal coupling".to_string());
        }
        if !matrix_is_diagonal(&effective_bound.upper_coeffs, JACOBIAN_TOLERANCE) {
            return Err("effective upper bound retained off-diagonal coupling".to_string());
        }

        let (effective_lower, effective_upper) =
            crown_concretize(&effective_bound, input_lower, input_upper);
        let ibp_bounds = ibp_through_layernorm(input_lower, input_upper, gamma, beta, epsilon);
        for i in 0..dim {
            if !approx_eq(effective_lower[i], ibp_bounds[i].lower, MATCH_TOLERANCE) {
                return Err(format!(
                    "effective lower bound mismatch at index {i}: {} vs {}",
                    effective_lower[i], ibp_bounds[i].lower
                ));
            }
            if !approx_eq(effective_upper[i], ibp_bounds[i].upper, MATCH_TOLERANCE) {
                return Err(format!(
                    "effective upper bound mismatch at index {i}: {} vs {}",
                    effective_upper[i], ibp_bounds[i].upper
                ));
            }
        }

        Ok(())
    }
}

impl Default for CrownLayerNormDegenerationSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[must_use]
pub(crate) fn crown_backward_through_layernorm_linearized(
    gamma: &[f64],
    beta: &[f64],
    epsilon: f64,
    input_lower: &[f64],
    input_upper: &[f64],
    bound: &CrownBound,
) -> CrownBound {
    let input_dim = input_lower.len();
    debug_assert_eq!(input_dim, input_upper.len());
    debug_assert_eq!(input_dim, gamma.len());
    debug_assert_eq!(input_dim, beta.len());
    debug_assert_eq!(bound.num_inputs(), input_dim);

    let reference = midpoint(input_lower, input_upper);
    let jacobian = LayerNormJacobian::compute(&reference, gamma, epsilon);
    let reference_output = evaluate_layernorm(&reference, gamma, beta, epsilon);
    let affine_bias = affine_bias_from_jacobian(&jacobian.matrix, &reference, &reference_output);

    crown_linear_backward(&jacobian.matrix, &affine_bias, bound)
}

#[must_use]
pub(crate) fn degenerated_bound_from_intervals(
    bound: &CrownBound,
    interval_bounds: &[Interval],
    input_dim: usize,
) -> CrownBound {
    debug_assert_eq!(
        bound.num_inputs(),
        interval_bounds.len(),
        "incoming bound dimension must match LayerNorm output dimension"
    );

    let linear = IbpLinearSpec::new();
    let lower_eval = linear.propagate(&bound.lower_coeffs, &bound.lower_bias, interval_bounds);
    let upper_eval = linear.propagate(&bound.upper_coeffs, &bound.upper_bias, interval_bounds);
    let num_outputs = bound.num_outputs();

    CrownBound {
        lower_coeffs: vec![vec![0.0; input_dim]; num_outputs],
        upper_coeffs: vec![vec![0.0; input_dim]; num_outputs],
        lower_bias: lower_eval.iter().map(|interval| interval.lower).collect(),
        upper_bias: upper_eval.iter().map(|interval| interval.upper).collect(),
    }
}

#[must_use]
pub(crate) fn midpoint(input_lower: &[f64], input_upper: &[f64]) -> Vec<f64> {
    debug_assert_eq!(input_lower.len(), input_upper.len());
    input_lower
        .iter()
        .zip(input_upper.iter())
        .map(|(&lower, &upper)| 0.5 * (lower + upper))
        .collect()
}

#[must_use]
pub(crate) fn evaluate_layernorm(x: &[f64], gamma: &[f64], beta: &[f64], epsilon: f64) -> Vec<f64> {
    let dim = x.len();
    debug_assert!(dim > 0, "LayerNorm dimension must be positive");
    debug_assert_eq!(dim, gamma.len());
    debug_assert_eq!(dim, beta.len());
    debug_assert!(epsilon > 0.0, "LayerNorm epsilon must be positive");

    let inv_dim = 1.0 / dim as f64;
    let mean = x.iter().sum::<f64>() * inv_dim;
    let variance = x.iter().map(|&xi| (xi - mean) * (xi - mean)).sum::<f64>() * inv_dim;
    let inv_sigma = 1.0 / (variance + epsilon).sqrt();

    x.iter()
        .enumerate()
        .map(|(i, &xi)| gamma[i] * (xi - mean) * inv_sigma + beta[i])
        .collect()
}

#[must_use]
pub(crate) fn affine_bias_from_jacobian(
    jacobian: &[Vec<f64>],
    reference_point: &[f64],
    reference_output: &[f64],
) -> Vec<f64> {
    let dim = jacobian.len();
    debug_assert_eq!(dim, reference_point.len());
    debug_assert_eq!(dim, reference_output.len());

    let mut bias = vec![0.0; dim];
    for i in 0..dim {
        let linear_part: f64 = jacobian[i]
            .iter()
            .zip(reference_point.iter())
            .map(|(&coeff, &value)| coeff * value)
            .sum();
        bias[i] = reference_output[i] - linear_part;
    }
    bias
}

#[must_use]
pub(crate) fn matrix_is_diagonal(matrix: &[Vec<f64>], tolerance: f64) -> bool {
    for (i, row) in matrix.iter().enumerate() {
        for (j, &value) in row.iter().enumerate() {
            if i != j && value.abs() > tolerance {
                return false;
            }
        }
    }
    true
}

#[must_use]
pub(crate) fn bound_is_finite(bound: &CrownBound) -> bool {
    bound
        .lower_coeffs
        .iter()
        .flatten()
        .chain(bound.upper_coeffs.iter().flatten())
        .chain(bound.lower_bias.iter())
        .chain(bound.upper_bias.iter())
        .all(|value| value.is_finite())
}

#[must_use]
pub(crate) fn approx_eq(lhs: f64, rhs: f64, tolerance: f64) -> bool {
    (lhs - rhs).abs() <= tolerance
}

/// Return the theorem entry for C004 in the registry.
#[must_use]
pub(crate) fn c004_theorem_entry() -> super::TheoremEntry {
    super::TheoremEntry {
        id: "C004",
        description: "CROWN through LayerNorm degenerates to IBP",
        status: ProofStatus::DerivedPending,
        phase: super::Phase::Phase3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crown_layernorm_degeneration_spec_status_is_pending() {
        let spec = CrownLayerNormDegenerationSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_crown_layernorm_degeneration_spec_default_matches_new() {
        let from_new = CrownLayerNormDegenerationSpec::new();
        let from_default = CrownLayerNormDegenerationSpec::default();
        assert_eq!(from_new.status(), from_default.status());
        assert_eq!(from_default.status(), ProofStatus::DerivedPending);
    }

    #[test]
    fn test_c004_theorem_entry() {
        let entry = c004_theorem_entry();
        assert_eq!(entry.id, "C004");
        assert_eq!(entry.phase, super::super::Phase::Phase3);
        assert_eq!(entry.status, ProofStatus::DerivedPending);
    }
}
