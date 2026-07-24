// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Matrix type over rationals and interval matrix arithmetic.
//!
//! `Mat m n` is formalized as `Fin m -> Fin n -> Rat` in the clean spec layer.
//! `IntervalMatrix` provides sound interval arithmetic for NN verification:
//! each entry is an interval [lo, hi] bounding possible concrete values.

use crate::spec::ProofStatus;

/// Matrix type re-exported from vec module for consistency.
pub use super::vec::Mat;

/// M01: interval_multiply_sound
/// For any concrete A in M1 and B in M2, A*B is in
/// `interval_matrix_multiply(M1, M2)`.
pub const M01_INTERVAL_MULTIPLY_SOUND: ProofStatus = ProofStatus::DerivedPending;

/// M02: frobenius_bound
/// `frobenius_norm_interval` returns sound bounds on ||A||_F.
pub const M02_FROBENIUS_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// M03: gershgorin_bound
/// `spectral_radius_bound` gives an upper bound on spectral radius via
/// Gershgorin circle theorem.
pub const M03_GERSHGORIN_BOUND: ProofStatus = ProofStatus::DerivedPending;

/// Error type for interval matrix operations.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum IntervalMatrixError {
    #[error("data length {data_len} != {rows} x {cols} = {expected}")]
    DataLengthMismatch {
        data_len: usize,
        rows: usize,
        cols: usize,
        expected: usize,
    },
    #[error("dimension mismatch: {left_rows}x{left_cols} vs {right_rows}x{right_cols}")]
    DimensionMismatch {
        left_rows: usize,
        left_cols: usize,
        right_rows: usize,
        right_cols: usize,
    },
    #[error("inner dim mismatch: left {left_cols} cols, right {right_rows} rows")]
    InnerDimensionMismatch { left_cols: usize, right_rows: usize },
    #[error("matrix has {cols} cols but vector has {vec_len} entries")]
    VectorDimensionMismatch { cols: usize, vec_len: usize },
    #[error("invalid interval at ({row}, {col}): lo={lo} > hi={hi}")]
    InvalidInterval {
        row: usize,
        col: usize,
        lo: f64,
        hi: f64,
    },
}

/// Interval matrix: each entry is an interval [lo, hi].
///
/// Stored as two flat `Vec<f64>` in row-major order.
/// For an m x n matrix, `lo[i * cols + j]` is the lower bound of (i, j).
#[derive(Debug, Clone, PartialEq)]
pub struct IntervalMatrix {
    rows: usize,
    cols: usize,
    lo: Vec<f64>,
    hi: Vec<f64>,
}

impl IntervalMatrix {
    /// Create from separate lower/upper bound vectors (row-major).
    pub fn new(
        rows: usize,
        cols: usize,
        lo: Vec<f64>,
        hi: Vec<f64>,
    ) -> Result<Self, IntervalMatrixError> {
        let expected = rows * cols;
        if lo.len() != expected {
            return Err(IntervalMatrixError::DataLengthMismatch {
                data_len: lo.len(),
                rows,
                cols,
                expected,
            });
        }
        if hi.len() != expected {
            return Err(IntervalMatrixError::DataLengthMismatch {
                data_len: hi.len(),
                rows,
                cols,
                expected,
            });
        }
        for i in 0..rows {
            for j in 0..cols {
                let k = i * cols + j;
                if lo[k] > hi[k] {
                    return Err(IntervalMatrixError::InvalidInterval {
                        row: i,
                        col: j,
                        lo: lo[k],
                        hi: hi[k],
                    });
                }
            }
        }
        Ok(Self { rows, cols, lo, hi })
    }

    /// Create a zero interval matrix (all entries [0, 0]).
    #[must_use]
    pub fn zeros(rows: usize, cols: usize) -> Self {
        let n = rows * cols;
        Self {
            rows,
            cols,
            lo: vec![0.0; n],
            hi: vec![0.0; n],
        }
    }

    /// Create an identity interval matrix (diagonal [1,1], off-diagonal [0,0]).
    #[must_use]
    pub fn identity(n: usize) -> Self {
        let mut lo = vec![0.0; n * n];
        let mut hi = vec![0.0; n * n];
        for i in 0..n {
            lo[i * n + i] = 1.0;
            hi[i * n + i] = 1.0;
        }
        Self {
            rows: n,
            cols: n,
            lo,
            hi,
        }
    }

    #[must_use]
    pub fn rows(&self) -> usize {
        self.rows
    }

    #[must_use]
    pub fn cols(&self) -> usize {
        self.cols
    }

    #[must_use]
    pub fn lo(&self, i: usize, j: usize) -> f64 {
        self.lo[i * self.cols + j]
    }

    #[must_use]
    pub fn hi(&self, i: usize, j: usize) -> f64 {
        self.hi[i * self.cols + j]
    }

    /// Transpose: swap rows/cols and mirror lo/hi.
    #[must_use]
    pub fn transpose(&self) -> Self {
        let mut lo = vec![0.0; self.rows * self.cols];
        let mut hi = vec![0.0; self.rows * self.cols];
        for i in 0..self.rows {
            for j in 0..self.cols {
                lo[j * self.rows + i] = self.lo[i * self.cols + j];
                hi[j * self.rows + i] = self.hi[i * self.cols + j];
            }
        }
        Self {
            rows: self.cols,
            cols: self.rows,
            lo,
            hi,
        }
    }

    /// Check that a concrete matrix (row-major flat f64) is in this interval.
    pub fn verify_containment(&self, concrete: &[f64]) -> Result<(), IntervalMatrixError> {
        let expected = self.rows * self.cols;
        if concrete.len() != expected {
            return Err(IntervalMatrixError::DataLengthMismatch {
                data_len: concrete.len(),
                rows: self.rows,
                cols: self.cols,
                expected,
            });
        }
        for i in 0..self.rows {
            for j in 0..self.cols {
                let k = i * self.cols + j;
                let v = concrete[k];
                if v < self.lo[k] - f64::EPSILON || v > self.hi[k] + f64::EPSILON {
                    return Err(IntervalMatrixError::InvalidInterval {
                        row: i,
                        col: j,
                        lo: self.lo[k],
                        hi: self.hi[k],
                    });
                }
            }
        }
        Ok(())
    }
}

/// Sound addition: `[a_lo + b_lo, a_hi + b_hi]`.
pub fn interval_matrix_add(
    a: &IntervalMatrix,
    b: &IntervalMatrix,
) -> Result<IntervalMatrix, IntervalMatrixError> {
    if a.rows != b.rows || a.cols != b.cols {
        return Err(IntervalMatrixError::DimensionMismatch {
            left_rows: a.rows,
            left_cols: a.cols,
            right_rows: b.rows,
            right_cols: b.cols,
        });
    }
    let n = a.rows * a.cols;
    let lo = (0..n).map(|k| a.lo[k] + b.lo[k]).collect();
    let hi = (0..n).map(|k| a.hi[k] + b.hi[k]).collect();
    Ok(IntervalMatrix {
        rows: a.rows,
        cols: a.cols,
        lo,
        hi,
    })
}

/// Hadamard (element-wise) product using four-product interval multiplication.
pub fn hadamard_product(
    a: &IntervalMatrix,
    b: &IntervalMatrix,
) -> Result<IntervalMatrix, IntervalMatrixError> {
    if a.rows != b.rows || a.cols != b.cols {
        return Err(IntervalMatrixError::DimensionMismatch {
            left_rows: a.rows,
            left_cols: a.cols,
            right_rows: b.rows,
            right_cols: b.cols,
        });
    }
    let n = a.rows * a.cols;
    let mut lo = Vec::with_capacity(n);
    let mut hi = Vec::with_capacity(n);
    for k in 0..n {
        let (l, h) = interval_mul(a.lo[k], a.hi[k], b.lo[k], b.hi[k]);
        lo.push(l);
        hi.push(h);
    }
    Ok(IntervalMatrix {
        rows: a.rows,
        cols: a.cols,
        lo,
        hi,
    })
}

/// Sound multiplication via interval dot products per entry.
pub fn interval_matrix_multiply(
    a: &IntervalMatrix,
    b: &IntervalMatrix,
) -> Result<IntervalMatrix, IntervalMatrixError> {
    if a.cols != b.rows {
        return Err(IntervalMatrixError::InnerDimensionMismatch {
            left_cols: a.cols,
            right_rows: b.rows,
        });
    }
    let (m, n, p) = (a.rows, b.cols, a.cols);
    let mut lo = Vec::with_capacity(m * n);
    let mut hi = Vec::with_capacity(m * n);
    for i in 0..m {
        for j in 0..n {
            let mut sum_lo = 0.0_f64;
            let mut sum_hi = 0.0_f64;
            for k in 0..p {
                let (pl, ph) = interval_mul(
                    a.lo[i * p + k],
                    a.hi[i * p + k],
                    b.lo[k * n + j],
                    b.hi[k * n + j],
                );
                sum_lo += pl;
                sum_hi += ph;
            }
            lo.push(sum_lo);
            hi.push(sum_hi);
        }
    }
    Ok(IntervalMatrix {
        rows: m,
        cols: n,
        lo,
        hi,
    })
}

/// Sound matrix-vector multiply. Vector given as interval bounds [v_lo, v_hi].
pub fn interval_matrix_vector_multiply(
    mat: &IntervalMatrix,
    v_lo: &[f64],
    v_hi: &[f64],
) -> Result<(Vec<f64>, Vec<f64>), IntervalMatrixError> {
    if v_lo.len() != mat.cols || v_hi.len() != mat.cols {
        return Err(IntervalMatrixError::VectorDimensionMismatch {
            cols: mat.cols,
            vec_len: v_lo.len(),
        });
    }
    let (m, n) = (mat.rows, mat.cols);
    let mut out_lo = Vec::with_capacity(m);
    let mut out_hi = Vec::with_capacity(m);
    for i in 0..m {
        let mut sl = 0.0_f64;
        let mut sh = 0.0_f64;
        for j in 0..n {
            let (pl, ph) = interval_mul(mat.lo[i * n + j], mat.hi[i * n + j], v_lo[j], v_hi[j]);
            sl += pl;
            sh += ph;
        }
        out_lo.push(sl);
        out_hi.push(sh);
    }
    Ok((out_lo, out_hi))
}

/// Verify that for concrete A in m1, B in m2, A*B is in the product interval.
pub fn verify_multiplication_sound(
    m1: &IntervalMatrix,
    m2: &IntervalMatrix,
    a: &[f64],
    b: &[f64],
) -> Result<(), IntervalMatrixError> {
    m1.verify_containment(a)?;
    m2.verify_containment(b)?;
    let product_interval = interval_matrix_multiply(m1, m2)?;
    let (m, n, p) = (m1.rows, m2.cols, m1.cols);
    let mut c = vec![0.0; m * n];
    for i in 0..m {
        for j in 0..n {
            let mut s = 0.0_f64;
            for k in 0..p {
                s += a[i * p + k] * b[k * n + j];
            }
            c[i * n + j] = s;
        }
    }
    product_interval.verify_containment(&c)
}

/// Interval bounds on the Frobenius norm.
///
/// Lower bound uses minimum absolute value per entry; upper uses maximum.
#[must_use]
pub fn frobenius_norm_interval(mat: &IntervalMatrix) -> (f64, f64) {
    let mut sq_lo = 0.0_f64;
    let mut sq_hi = 0.0_f64;
    for k in 0..(mat.rows * mat.cols) {
        let (lo, hi) = (mat.lo[k], mat.hi[k]);
        let abs_min = if lo <= 0.0 && hi >= 0.0 {
            0.0
        } else {
            lo.abs().min(hi.abs())
        };
        let abs_max = lo.abs().max(hi.abs());
        sq_lo += abs_min * abs_min;
        sq_hi += abs_max * abs_max;
    }
    (sq_lo.sqrt(), sq_hi.sqrt())
}

/// Upper bound on spectral radius via Gershgorin circles.
///
/// Returns `None` for non-square matrices.
#[must_use]
pub fn spectral_radius_bound(mat: &IntervalMatrix) -> Option<f64> {
    if mat.rows != mat.cols {
        return None;
    }
    let n = mat.rows;
    if n == 0 {
        return Some(0.0);
    }
    let mut max_radius = 0.0_f64;
    for i in 0..n {
        let diag_abs = mat.lo[i * n + i].abs().max(mat.hi[i * n + i].abs());
        let off_sum: f64 = (0..n)
            .filter(|&j| j != i)
            .map(|j| mat.lo[i * n + j].abs().max(mat.hi[i * n + j].abs()))
            .sum();
        max_radius = max_radius.max(diag_abs + off_sum);
    }
    Some(max_radius)
}

/// Interval multiplication: [a_lo, a_hi] * [b_lo, b_hi] via four products.
fn interval_mul(a_lo: f64, a_hi: f64, b_lo: f64, b_hi: f64) -> (f64, f64) {
    let p1 = a_lo * b_lo;
    let p2 = a_lo * b_hi;
    let p3 = a_hi * b_lo;
    let p4 = a_hi * b_hi;
    (p1.min(p2).min(p3).min(p4), p1.max(p2).max(p3).max(p4))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_status_tracking() {
        assert!(matches!(
            M01_INTERVAL_MULTIPLY_SOUND,
            ProofStatus::DerivedPending
        ));
        assert!(matches!(M02_FROBENIUS_BOUND, ProofStatus::DerivedPending));
        assert!(matches!(M03_GERSHGORIN_BOUND, ProofStatus::DerivedPending));
    }
}

#[cfg(test)]
#[path = "tests_mat.rs"]
mod tests_mat;
