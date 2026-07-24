// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete norm computation for vectors and matrices.
//!
//! All functions operate on `f64` values. For exact arithmetic with rationals
//! (e.g., L1 and Linf where no square root is needed), see the rational
//! variants suffixed `_exact`.
//!
//! # Vector norms
//!
//! - [`l1_norm`]: `||x||_1 = sum |x_i|`
//! - [`l2_norm`]: `||x||_2 = sqrt(sum x_i^2)`
//! - [`linf_norm`]: `||x||_inf = max |x_i|`
//!
//! # Matrix operator norms
//!
//! - [`matrix_l1_norm`]: max column sum of absolute values (induced L1)
//! - [`matrix_linf_norm`]: max row sum of absolute values (induced Linf)
//! - [`matrix_frobenius_norm`]: `sqrt(sum a_ij^2)` (not an operator norm, but
//!   useful as an upper bound for `||A||_2`)

use super::types::{Matrix, NormKind, Vector};
use crate::theories::rational::Rational;

// ---------------------------------------------------------------------------
// Vector norms (f64)
// ---------------------------------------------------------------------------

/// L1 norm: `||x||_1 = sum_i |x_i|`.
#[must_use]
pub fn l1_norm(v: &Vector<f64>) -> f64 {
    v.as_slice().iter().map(|x| x.abs()).sum()
}

/// L2 norm: `||x||_2 = sqrt(sum_i x_i^2)`.
#[must_use]
pub fn l2_norm(v: &Vector<f64>) -> f64 {
    v.as_slice().iter().map(|x| x * x).sum::<f64>().sqrt()
}

/// Linf norm: `||x||_inf = max_i |x_i|`.
///
/// Returns 0.0 for an empty vector.
#[must_use]
pub fn linf_norm(v: &Vector<f64>) -> f64 {
    v.as_slice().iter().map(|x| x.abs()).fold(0.0_f64, f64::max)
}

/// Dispatch to the appropriate vector norm by [`NormKind`].
#[must_use]
pub fn vector_norm(v: &Vector<f64>, kind: NormKind) -> f64 {
    match kind {
        NormKind::L1 => l1_norm(v),
        NormKind::L2 => l2_norm(v),
        NormKind::Linf => linf_norm(v),
    }
}

// ---------------------------------------------------------------------------
// Vector norms (exact rational — no square roots needed for L1 / Linf)
// ---------------------------------------------------------------------------

/// Exact L1 norm over rationals: `sum_i |x_i|`.
///
/// Returns `None` on arithmetic overflow.
#[must_use]
pub fn l1_norm_exact(v: &Vector<Rational>) -> Option<Rational> {
    let mut acc = Rational::ZERO;
    for x in v.as_slice() {
        acc = acc.add(&x.abs())?;
    }
    Some(acc)
}

/// Exact Linf norm over rationals: `max_i |x_i|`.
///
/// Returns `Rational::ZERO` for an empty vector.
#[must_use]
pub fn linf_norm_exact(v: &Vector<Rational>) -> Rational {
    v.as_slice()
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or(Rational::ZERO)
}

// ---------------------------------------------------------------------------
// Matrix operator norms (f64)
// ---------------------------------------------------------------------------

/// Induced L1 matrix norm: maximum absolute column sum.
///
/// `||A||_1 = max_j sum_i |a_ij|`
#[must_use]
pub fn matrix_l1_norm(m: &Matrix<f64>) -> f64 {
    if m.cols() == 0 || m.rows() == 0 {
        return 0.0;
    }
    let mut max_col_sum = 0.0_f64;
    for j in 0..m.cols() {
        let col_sum: f64 = (0..m.rows()).map(|i| m.get(i, j).abs()).sum();
        max_col_sum = max_col_sum.max(col_sum);
    }
    max_col_sum
}

/// Induced Linf matrix norm: maximum absolute row sum.
///
/// `||A||_inf = max_i sum_j |a_ij|`
#[must_use]
pub fn matrix_linf_norm(m: &Matrix<f64>) -> f64 {
    m.row_iter()
        .map(|row| row.iter().map(|x| x.abs()).sum::<f64>())
        .fold(0.0_f64, f64::max)
}

/// Frobenius norm: `||A||_F = sqrt(sum_ij a_ij^2)`.
///
/// Not an operator norm, but satisfies `||A||_2 <= ||A||_F` and is useful as
/// an inexpensive upper bound for the spectral norm.
#[must_use]
pub fn matrix_frobenius_norm(m: &Matrix<f64>) -> f64 {
    m.as_slice().iter().map(|x| x * x).sum::<f64>().sqrt()
}
