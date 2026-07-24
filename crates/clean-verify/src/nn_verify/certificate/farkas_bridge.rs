// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge from ExternalFarkasCert to IntervalBounds (T09).
//!
//! Connects the Rust-side certificate verifier (`clean-elab/src/cert/external/`)
//! to the formalized `IntervalBounds` type in the proof layer.
//!
//! ## Certificate Model
//!
//! An external Farkas certificate proves:
//!   input in polyhedron_in => output in polyhedron_out
//! via non-negative linear combination (Farkas multipliers).
//!
//! When the polyhedra are box constraints (axis-aligned), we can extract
//! per-dimension `Interval` bounds. Box constraints encode dimension i as:
//!   +e_i coefficient => x_i <= b   (upper bound row)
//!   -e_i coefficient => x_i >= -b  (lower bound row, i.e. -x_i <= -l => x_i >= l)
//!
//! ## Chaining
//!
//! `chain_farkas_certs` implements T70 (entailment transitivity) at the
//! Farkas certificate level: if cert1 proves A => B and cert2 proves B => C,
//! the chained certificate proves A => C by composing the linear combinations.

use crate::nn_verify::ibp_crown::Interval;
use thiserror::Error;

/// Tolerance for floating-point comparisons in certificate verification.
const EPSILON: f64 = 1e-9;

/// An external Farkas certificate from gamma-crown.
///
/// The certificate proves: input in polyhedron_in => output in polyhedron_out
/// via non-negative linear combination (Farkas multipliers).
#[derive(Debug, Clone)]
pub struct ExternalFarkasCert {
    /// Farkas multipliers (non-negative coefficients for the linear combination).
    pub multipliers: Vec<f64>,
    /// Input constraint matrix (each row is a linear constraint a^T x <= b).
    pub input_matrix: Vec<Vec<f64>>,
    /// Input constraint bounds (right-hand sides b).
    pub input_bounds: Vec<f64>,
    /// Output constraint matrix.
    pub output_matrix: Vec<Vec<f64>>,
    /// Output constraint bounds.
    pub output_bounds: Vec<f64>,
    /// Input dimension.
    pub input_dim: usize,
    /// Output dimension.
    pub output_dim: usize,
}

/// Result of Farkas certificate verification.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum FarkasVerifyResult {
    /// Certificate is valid: multipliers are non-negative, constraints compose correctly.
    Valid,
    /// Certificate has negative multipliers.
    NegativeMultiplier {
        /// Index of the offending multiplier.
        index: usize,
        /// The negative value found.
        value: f64,
    },
    /// Linear combination does not produce the claimed output constraints.
    ConstraintMismatch {
        /// Output constraint row index.
        row: usize,
        /// Expected coefficient or bound value.
        expected: f64,
        /// Actual coefficient or bound value.
        got: f64,
    },
    /// Dimension mismatch in the certificate.
    DimensionError {
        /// Expected dimension.
        expected: usize,
        /// Actual dimension.
        got: usize,
    },
}

/// Errors from the Farkas bridge operations.
#[derive(Debug, Clone, PartialEq, Error)]
#[non_exhaustive]
pub enum FarkasBridgeError {
    /// The certificate failed verification.
    #[error("invalid certificate: {0}")]
    InvalidCertificate(String),

    /// Dimension mismatch between expected and actual.
    #[error("dimension mismatch: expected {expected}, got {got}")]
    DimensionMismatch {
        /// Expected dimension.
        expected: usize,
        /// Actual dimension.
        got: usize,
    },

    /// Interface mismatch when chaining: cert1 output dims != cert2 input dims.
    #[error("interface mismatch: cert1 output constraints do not match cert2 input constraints")]
    InterfaceMismatch,

    /// Constraints are not in box (axis-aligned) form.
    #[error(
        "constraints are not in box form (expected axis-aligned identity/negated-identity rows)"
    )]
    NonBoxConstraints,
}

/// Verify that a Farkas certificate is valid.
///
/// Checks:
/// 1. All multipliers are non-negative
/// 2. For each output constraint, the weighted combination of input constraints
///    (using the corresponding block of multipliers) produces matching
///    coefficients with a bound that implies the output bound
/// 3. Dimensions are consistent
///
/// ## Multiplier layout
///
/// Multipliers are laid out in blocks: one block per output constraint row.
/// Block j starts at index `j * (num_input_rows / num_output_rows)`.
/// When input and output have equal row counts, each output row maps 1:1
/// to one input row with a single multiplier.
#[must_use]
pub fn verify_farkas_certificate(cert: &ExternalFarkasCert) -> FarkasVerifyResult {
    // Dimension consistency checks.
    if cert.input_matrix.len() != cert.input_bounds.len() {
        return FarkasVerifyResult::DimensionError {
            expected: cert.input_matrix.len(),
            got: cert.input_bounds.len(),
        };
    }
    if cert.output_matrix.len() != cert.output_bounds.len() {
        return FarkasVerifyResult::DimensionError {
            expected: cert.output_matrix.len(),
            got: cert.output_bounds.len(),
        };
    }
    for row in &cert.input_matrix {
        if row.len() != cert.input_dim {
            return FarkasVerifyResult::DimensionError {
                expected: cert.input_dim,
                got: row.len(),
            };
        }
    }
    for row in &cert.output_matrix {
        if row.len() != cert.output_dim {
            return FarkasVerifyResult::DimensionError {
                expected: cert.output_dim,
                got: row.len(),
            };
        }
    }

    // Multiplier count must divide evenly among output constraints.
    let num_out = cert.output_matrix.len();
    let num_in = cert.input_matrix.len();
    if num_out == 0 {
        // No output constraints: vacuously valid if multipliers also empty.
        return if cert.multipliers.is_empty() {
            FarkasVerifyResult::Valid
        } else {
            FarkasVerifyResult::DimensionError {
                expected: 0,
                got: cert.multipliers.len(),
            }
        };
    }
    if cert.multipliers.len() != num_in || !num_in.is_multiple_of(num_out) {
        return FarkasVerifyResult::DimensionError {
            expected: num_in,
            got: cert.multipliers.len(),
        };
    }

    // All multipliers must be non-negative.
    for (i, &m) in cert.multipliers.iter().enumerate() {
        if m < -EPSILON {
            return FarkasVerifyResult::NegativeMultiplier { index: i, value: m };
        }
    }

    // Input and output must be in the same variable space for box certs.
    if cert.input_dim != cert.output_dim {
        return FarkasVerifyResult::DimensionError {
            expected: cert.input_dim,
            got: cert.output_dim,
        };
    }

    // For each output constraint row, verify the weighted combination.
    let block_size = num_in / num_out;
    for (j, output_row) in cert.output_matrix.iter().enumerate() {
        let result = verify_output_row(cert, j, output_row, block_size);
        if result != FarkasVerifyResult::Valid {
            return result;
        }
    }

    FarkasVerifyResult::Valid
}

/// Verify a single output constraint row against its input block.
///
/// Checks that the weighted combination of input constraints (from the j-th
/// multiplier block) produces coefficients matching `output_row` and a bound
/// that implies the output bound.
fn verify_output_row(
    cert: &ExternalFarkasCert,
    j: usize,
    output_row: &[f64],
    block_size: usize,
) -> FarkasVerifyResult {
    let block_start = j * block_size;
    let mut weighted_coeffs = vec![0.0_f64; cert.output_dim];
    let mut weighted_bound = 0.0_f64;

    for local_i in 0..block_size {
        let global_i = block_start + local_i;
        let mult = cert.multipliers[global_i];
        weighted_bound += mult * cert.input_bounds[global_i];
        for (k, &coeff) in cert.input_matrix[global_i].iter().enumerate() {
            weighted_coeffs[k] += mult * coeff;
        }
    }

    // Verify coefficient match.
    for (k, &expected_coeff) in output_row.iter().enumerate() {
        if (weighted_coeffs[k] - expected_coeff).abs() > EPSILON {
            return FarkasVerifyResult::ConstraintMismatch {
                row: j,
                expected: expected_coeff,
                got: weighted_coeffs[k],
            };
        }
    }

    // Verify bound: weighted bound <= output bound.
    let output_bound = cert.output_bounds[j];
    if weighted_bound > output_bound + EPSILON {
        return FarkasVerifyResult::ConstraintMismatch {
            row: j,
            expected: output_bound,
            got: weighted_bound,
        };
    }

    FarkasVerifyResult::Valid
}

/// Convert verified Farkas certificate to interval bounds.
///
/// Given a valid Farkas cert with input/output polyhedra expressed as
/// box constraints (x_i in [l_i, u_i]), extract the `Interval` for each
/// dimension.
///
/// # Errors
///
/// Returns `FarkasBridgeError::InvalidCertificate` if the certificate fails
/// verification, or `FarkasBridgeError::NonBoxConstraints` if the polyhedra
/// are not axis-aligned box constraints.
pub fn farkas_to_interval(
    cert: &ExternalFarkasCert,
) -> Result<(Vec<Interval>, Vec<Interval>), FarkasBridgeError> {
    // Verify the certificate first.
    let result = verify_farkas_certificate(cert);
    if result != FarkasVerifyResult::Valid {
        return Err(FarkasBridgeError::InvalidCertificate(format!(
            "certificate verification failed: {result:?}"
        )));
    }

    let input_intervals =
        box_constraints_to_interval(&cert.input_matrix, &cert.input_bounds, cert.input_dim)?;
    let output_intervals =
        box_constraints_to_interval(&cert.output_matrix, &cert.output_bounds, cert.output_dim)?;

    Ok((input_intervals, output_intervals))
}

/// Convert box constraints to a vector of intervals.
///
/// Box constraints encode dimension i as pairs of rows:
///   - Upper bound row: coefficient +1 at position i, 0 elsewhere => x_i <= b
///   - Lower bound row: coefficient -1 at position i, 0 elsewhere => -x_i <= -l, i.e. x_i >= l
///
/// The constraint matrix must consist entirely of axis-aligned unit vectors
/// (with exactly one non-zero entry per row, either +1 or -1).
///
/// # Errors
///
/// Returns `FarkasBridgeError::NonBoxConstraints` if any row is not an
/// axis-aligned unit vector, or `FarkasBridgeError::DimensionMismatch`
/// if dimensions are inconsistent.
pub fn box_constraints_to_interval(
    constraint_matrix: &[Vec<f64>],
    bounds: &[f64],
    dim: usize,
) -> Result<Vec<Interval>, FarkasBridgeError> {
    if constraint_matrix.len() != bounds.len() {
        return Err(FarkasBridgeError::DimensionMismatch {
            expected: constraint_matrix.len(),
            got: bounds.len(),
        });
    }

    // We need exactly 2 * dim rows (one upper, one lower per dimension).
    if constraint_matrix.len() != 2 * dim {
        return Err(FarkasBridgeError::NonBoxConstraints);
    }

    let mut lowers = vec![f64::NEG_INFINITY; dim];
    let mut uppers = vec![f64::INFINITY; dim];

    for (row_idx, row) in constraint_matrix.iter().enumerate() {
        if row.len() != dim {
            return Err(FarkasBridgeError::DimensionMismatch {
                expected: dim,
                got: row.len(),
            });
        }

        // Find the single non-zero entry in this row.
        let mut nonzero_col = None;
        let mut nonzero_val = 0.0;
        for (col, &val) in row.iter().enumerate() {
            if val.abs() > EPSILON {
                if nonzero_col.is_some() {
                    // More than one non-zero entry: not a box constraint.
                    return Err(FarkasBridgeError::NonBoxConstraints);
                }
                nonzero_col = Some(col);
                nonzero_val = val;
            }
        }

        let col = nonzero_col.ok_or(FarkasBridgeError::NonBoxConstraints)?;

        // Validate it is +1 or -1 (unit vector).
        if (nonzero_val - 1.0).abs() < EPSILON {
            // +1 coefficient: x_col <= bound => upper bound
            let bound = bounds[row_idx];
            if bound < uppers[col] {
                uppers[col] = bound;
            }
        } else if (nonzero_val + 1.0).abs() < EPSILON {
            // -1 coefficient: -x_col <= bound => x_col >= -bound => lower bound
            let bound = -bounds[row_idx];
            if bound > lowers[col] {
                lowers[col] = bound;
            }
        } else {
            // Coefficient is not +1 or -1: not a standard box constraint.
            return Err(FarkasBridgeError::NonBoxConstraints);
        }
    }

    // Build intervals. All dimensions should have both bounds set.
    let mut intervals = Vec::with_capacity(dim);
    for i in 0..dim {
        if lowers[i] == f64::NEG_INFINITY || uppers[i] == f64::INFINITY {
            return Err(FarkasBridgeError::NonBoxConstraints);
        }
        if lowers[i] > uppers[i] + EPSILON {
            return Err(FarkasBridgeError::InvalidCertificate(format!(
                "dimension {i}: lower bound {} > upper bound {}",
                lowers[i], uppers[i]
            )));
        }
        intervals.push(Interval::new(lowers[i], uppers[i]));
    }

    Ok(intervals)
}

/// Create box constraints from a vector of intervals.
///
/// For each dimension i with [l_i, u_i]:
///   Row 2i:   e_i coefficient = +1, bound = u_i   (x_i <= u_i)
///   Row 2i+1: e_i coefficient = -1, bound = -l_i  (-x_i <= -l_i => x_i >= l_i)
///
/// Returns (constraint_matrix, bounds).
#[must_use]
pub fn interval_to_box_constraints(intervals: &[Interval]) -> (Vec<Vec<f64>>, Vec<f64>) {
    let dim = intervals.len();
    let mut matrix = Vec::with_capacity(2 * dim);
    let mut bounds = Vec::with_capacity(2 * dim);

    for (i, iv) in intervals.iter().enumerate() {
        // Upper bound row: x_i <= u_i
        let mut upper_row = vec![0.0; dim];
        upper_row[i] = 1.0;
        matrix.push(upper_row);
        bounds.push(iv.upper);

        // Lower bound row: -x_i <= -l_i
        let mut lower_row = vec![0.0; dim];
        lower_row[i] = -1.0;
        matrix.push(lower_row);
        bounds.push(-iv.lower);
    }

    (matrix, bounds)
}

/// Build a simple 1D box-constraint Farkas certificate for testing.
///
/// Creates a certificate proving: x in [in_lower, in_upper] => x in [out_lower, out_upper]
/// where the input bounds are a subset of the output bounds.
///
/// The certificate uses identity multipliers (all 1.0) since the implication
/// follows directly from bound weakening.
#[cfg(test)]
pub(crate) fn build_simple_box_cert(
    dim: usize,
    in_lower: &[f64],
    in_upper: &[f64],
    out_lower: &[f64],
    out_upper: &[f64],
) -> ExternalFarkasCert {
    let in_intervals: Vec<Interval> = in_lower
        .iter()
        .zip(in_upper.iter())
        .map(|(&l, &u)| Interval::new(l, u))
        .collect();
    let out_intervals: Vec<Interval> = out_lower
        .iter()
        .zip(out_upper.iter())
        .map(|(&l, &u)| Interval::new(l, u))
        .collect();

    let (in_matrix, in_bounds) = interval_to_box_constraints(&in_intervals);
    let (out_matrix, out_bounds) = interval_to_box_constraints(&out_intervals);

    ExternalFarkasCert {
        multipliers: vec![1.0; in_matrix.len()],
        input_matrix: in_matrix,
        input_bounds: in_bounds,
        output_matrix: out_matrix,
        output_bounds: out_bounds,
        input_dim: dim,
        output_dim: dim,
    }
}
