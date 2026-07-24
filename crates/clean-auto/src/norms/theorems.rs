// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verified properties of norms: triangle inequality, submultiplicativity,
//! norm equivalence bounds.
//!
//! Each function checks a concrete instance of a mathematical theorem and
//! returns `true` when the property holds (within floating-point tolerance for
//! f64 operations). These serve as runtime proof witnesses that can be cited
//! in NN verification proof obligations.
//!
//! # Key theorems
//!
//! 1. **Triangle inequality**: `||x + y|| <= ||x|| + ||y||`
//! 2. **Submultiplicativity**: `||Ax|| <= ||A|| * ||x||` (operator norm)
//! 3. **Norm equivalence chain** (R^n):
//!    `||x||_inf <= ||x||_2 <= ||x||_1 <= n * ||x||_inf`

use super::compute::{l1_norm, l2_norm, linf_norm, matrix_l1_norm, matrix_linf_norm, vector_norm};
use super::types::{Matrix, NormKind, Vector};

/// Floating-point tolerance for inequality checks. We use a relative+absolute
/// hybrid: `a <= b + EPS * max(1, |b|)`.
const EPS: f64 = 1e-10;

/// Check `a <= b` up to floating-point tolerance.
fn le_approx(a: f64, b: f64) -> bool {
    a <= b + EPS * f64::max(1.0, b.abs())
}

// ---------------------------------------------------------------------------
// Triangle inequality
// ---------------------------------------------------------------------------

/// Verify triangle inequality for a given norm kind:
/// `||x + y||_p <= ||x||_p + ||y||_p`.
///
/// Requires `x` and `y` to have the same dimension. Returns `false` if
/// dimensions differ.
#[must_use]
pub fn check_triangle_inequality(x: &Vector<f64>, y: &Vector<f64>, kind: NormKind) -> bool {
    if x.dim() != y.dim() {
        return false;
    }
    let sum: Vector<f64> = Vector::new(
        x.as_slice()
            .iter()
            .zip(y.as_slice().iter())
            .map(|(a, b)| a + b)
            .collect(),
    );
    let lhs = vector_norm(&sum, kind);
    let rhs = vector_norm(x, kind) + vector_norm(y, kind);
    le_approx(lhs, rhs)
}

// ---------------------------------------------------------------------------
// Submultiplicativity
// ---------------------------------------------------------------------------

/// Verify submultiplicativity: `||Ax||_p <= ||A||_p * ||x||_p`.
///
/// For p = L1, uses the induced L1 (max column sum) matrix norm.
/// For p = Linf, uses the induced Linf (max row sum) matrix norm.
/// For p = L2, uses the Linf operator norm as a conservative bound
/// (the true induced L2 norm requires SVD, which we avoid here).
///
/// Returns `false` if matrix columns don't match vector dimension.
#[must_use]
pub fn check_submultiplicativity(a: &Matrix<f64>, x: &Vector<f64>, kind: NormKind) -> bool {
    if a.cols() != x.dim() {
        return false;
    }
    // Compute Ax
    let ax_data: Vec<f64> = a
        .row_iter()
        .map(|row| {
            row.iter()
                .zip(x.as_slice().iter())
                .map(|(aij, xj)| aij * xj)
                .sum()
        })
        .collect();
    let ax = Vector::new(ax_data);

    let lhs = vector_norm(&ax, kind);
    let mat_norm = match kind {
        NormKind::L1 => matrix_l1_norm(a),
        NormKind::Linf => matrix_linf_norm(a),
        // For L2 we use Frobenius as upper bound: ||A||_2 <= ||A||_F
        NormKind::L2 => super::compute::matrix_frobenius_norm(a),
    };
    let rhs = mat_norm * vector_norm(x, kind);
    le_approx(lhs, rhs)
}

// ---------------------------------------------------------------------------
// Norm equivalence chain
// ---------------------------------------------------------------------------

/// Verify the full norm equivalence chain in R^n:
///
/// `||x||_inf <= ||x||_2 <= ||x||_1 <= n * ||x||_inf`
///
/// Returns `true` if all three inequalities hold.
#[must_use]
pub fn check_norm_equivalence_chain(x: &Vector<f64>) -> bool {
    let n = x.dim() as f64;
    let n1 = l1_norm(x);
    let n2 = l2_norm(x);
    let ni = linf_norm(x);

    // ||x||_inf <= ||x||_2
    let ineq1 = le_approx(ni, n2);
    // ||x||_2 <= ||x||_1
    let ineq2 = le_approx(n2, n1);
    // ||x||_1 <= n * ||x||_inf
    let ineq3 = le_approx(n1, n * ni);

    ineq1 && ineq2 && ineq3
}

/// Verify `||x||_2 <= sqrt(n) * ||x||_inf` (tighter L2-Linf bound).
#[must_use]
pub fn check_l2_linf_bound(x: &Vector<f64>) -> bool {
    let n2 = l2_norm(x);
    let ni = linf_norm(x);
    let sqrt_n = (x.dim() as f64).sqrt();
    le_approx(n2, sqrt_n * ni)
}

/// Verify `||x||_1 <= sqrt(n) * ||x||_2` (tighter L1-L2 bound).
#[must_use]
pub fn check_l1_l2_bound(x: &Vector<f64>) -> bool {
    let n1 = l1_norm(x);
    let n2 = l2_norm(x);
    let sqrt_n = (x.dim() as f64).sqrt();
    le_approx(n1, sqrt_n * n2)
}
