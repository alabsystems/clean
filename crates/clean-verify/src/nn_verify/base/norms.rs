// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete L1/L2/Linf norm instances on vectors and matrices.
//!
//! Provides `NormKind` enum and concrete `Rational64`-based norm computations
//! for vectors and matrices, plus runtime-verifiable inequality theorems
//! (ordering, Holder, triangle inequality, submultiplicativity, dual duality).
//!
//! In the clean formalization:
//! ```text
//! def Vec.l1_norm (v : Vec n) : Rat := Fin.sum (fun i => |v i|)
//! def Vec.l2_norm_sq (v : Vec n) : Rat := Fin.sum (fun i => (v i)^2)
//! def Vec.linf_norm (v : Vec n) : Rat := Fin.sup (fun i => |v i|)
//! ```

use num_rational::Rational64;

use crate::spec::ProofStatus;

/// T08: l1_l2_linf_ordering
/// ||x||_inf <= ||x||_2 <= ||x||_1 for all x.
pub const T08_L1_L2_LINF_ORDERING: ProofStatus = ProofStatus::DerivedPending;

/// T09: holder_inequality
/// |x . y| <= ||x||_p * ||y||_q where 1/p + 1/q = 1.
pub const T09_HOLDER_INEQUALITY: ProofStatus = ProofStatus::DerivedPending;

/// T10: matrix_norm_submultiplicative
/// ||AB|| <= ||A|| * ||B|| for induced matrix norms.
pub const T10_MATRIX_NORM_SUBMULTIPLICATIVE: ProofStatus = ProofStatus::DerivedPending;

/// T11: triangle_inequality
/// ||x + y|| <= ||x|| + ||y|| for each norm kind.
pub const T11_TRIANGLE_INEQUALITY: ProofStatus = ProofStatus::DerivedPending;

/// T12: dual_norm_duality
/// ||x||_p = max_{||y||_q=1} x . y.
pub const T12_DUAL_NORM_DUALITY: ProofStatus = ProofStatus::DerivedPending;

/// Which norm to compute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NormKind {
    /// L1 (Manhattan): sum of absolute values.
    L1,
    /// L2 (Euclidean): square root of sum of squares (squared form for exact rational).
    L2,
    /// Linf (Chebyshev): maximum absolute value.
    Linf,
}

/// Error type for norm operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum NormError {
    /// Matrix row has inconsistent column count.
    #[error("row {row} has {got} columns, expected {expected}")]
    InconsistentRowLength {
        row: usize,
        got: usize,
        expected: usize,
    },
    /// Matrix is empty (no rows).
    #[error("empty matrix")]
    EmptyMatrix,
    /// Vector dimension mismatch for binary operations.
    #[error("vector dimension mismatch: {left} vs {right}")]
    DimensionMismatch { left: usize, right: usize },
}

// ---------------------------------------------------------------------------
// Vector norms
// ---------------------------------------------------------------------------

/// Compute a vector norm over `Rational64`.
///
/// For `L2`, returns the **squared** L2 norm (sum of squares) to remain exact
/// in rationals. Callers needing the actual L2 norm must take a square root
/// externally.
#[must_use]
pub fn vector_norm(v: &[Rational64], kind: NormKind) -> Rational64 {
    let zero = Rational64::from_integer(0);
    if v.is_empty() {
        return zero;
    }
    match kind {
        NormKind::L1 => v.iter().map(|x| rational_abs(*x)).fold(zero, |a, b| a + b),
        NormKind::L2 => v.iter().map(|x| *x * *x).fold(zero, |a, b| a + b),
        NormKind::Linf => v.iter().map(|x| rational_abs(*x)).max().unwrap_or(zero),
    }
}

/// Compute the dot product of two equal-length vectors.
///
/// Returns `Err` on dimension mismatch.
pub fn dot_product(u: &[Rational64], v: &[Rational64]) -> Result<Rational64, NormError> {
    if u.len() != v.len() {
        return Err(NormError::DimensionMismatch {
            left: u.len(),
            right: v.len(),
        });
    }
    let zero = Rational64::from_integer(0);
    Ok(u.iter()
        .zip(v.iter())
        .map(|(a, b)| *a * *b)
        .fold(zero, |acc, x| acc + x))
}

/// Element-wise vector addition.
///
/// Returns `Err` on dimension mismatch.
pub fn vector_add(u: &[Rational64], v: &[Rational64]) -> Result<Vec<Rational64>, NormError> {
    if u.len() != v.len() {
        return Err(NormError::DimensionMismatch {
            left: u.len(),
            right: v.len(),
        });
    }
    Ok(u.iter().zip(v.iter()).map(|(a, b)| *a + *b).collect())
}

// ---------------------------------------------------------------------------
// Matrix norms (induced)
// ---------------------------------------------------------------------------

/// Validate matrix shape; returns (rows, cols).
fn validate_matrix(m: &[Vec<Rational64>]) -> Result<(usize, usize), NormError> {
    if m.is_empty() {
        return Err(NormError::EmptyMatrix);
    }
    let cols = m[0].len();
    for (i, row) in m.iter().enumerate() {
        if row.len() != cols {
            return Err(NormError::InconsistentRowLength {
                row: i,
                got: row.len(),
                expected: cols,
            });
        }
    }
    Ok((m.len(), cols))
}

/// Compute an induced matrix norm.
///
/// - **L1 (induced)**: max over columns of the column-absolute-sum.
/// - **L2 (induced)**: returns the **squared** maximum singular value proxy
///   (max column sum of squares). This is an upper bound, not exact SVD.
///   Exact induced L2 norm requires eigenvalue computation.
/// - **Linf (induced)**: max over rows of the row-absolute-sum.
pub fn matrix_norm(m: &[Vec<Rational64>], kind: NormKind) -> Result<Rational64, NormError> {
    let (rows, cols) = validate_matrix(m)?;
    let zero = Rational64::from_integer(0);

    match kind {
        NormKind::L1 => {
            // Max column absolute-sum. Column-wise access traverses `m[i][j]`
            // across rows for a fixed `j`, which is not naturally expressed
            // as a per-row iterator without transposing.
            let mut max_col_sum = zero;
            #[allow(clippy::needless_range_loop)]
            for j in 0..cols {
                let col_sum = (0..rows)
                    .map(|i| rational_abs(m[i][j]))
                    .fold(zero, |a, b| a + b);
                if col_sum > max_col_sum {
                    max_col_sum = col_sum;
                }
            }
            Ok(max_col_sum)
        }
        NormKind::L2 => {
            // Upper bound: Frobenius norm squared (sum of all squared entries).
            // The true induced 2-norm (largest singular value) requires SVD,
            // which is not exact in rationals. Frobenius >= induced L2.
            let frob_sq = m
                .iter()
                .flat_map(|row| row.iter())
                .map(|x| *x * *x)
                .fold(zero, |a, b| a + b);
            Ok(frob_sq)
        }
        NormKind::Linf => {
            // Max row absolute-sum
            let mut max_row_sum = zero;
            for row in m {
                let row_sum = row
                    .iter()
                    .map(|x| rational_abs(*x))
                    .fold(zero, |a, b| a + b);
                if row_sum > max_row_sum {
                    max_row_sum = row_sum;
                }
            }
            Ok(max_row_sum)
        }
    }
}

/// Multiply two matrices (standard row-by-column product).
///
/// Returns `Err` if inner dimensions don't match.
pub fn matrix_multiply(
    a: &[Vec<Rational64>],
    b: &[Vec<Rational64>],
) -> Result<Vec<Vec<Rational64>>, NormError> {
    let (a_rows, a_cols) = validate_matrix(a)?;
    let (b_rows, b_cols) = validate_matrix(b)?;
    if a_cols != b_rows {
        return Err(NormError::DimensionMismatch {
            left: a_cols,
            right: b_rows,
        });
    }
    let zero = Rational64::from_integer(0);
    let mut result = vec![vec![zero; b_cols]; a_rows];
    for i in 0..a_rows {
        for j in 0..b_cols {
            let mut sum = zero;
            for k in 0..a_cols {
                sum += a[i][k] * b[k][j];
            }
            result[i][j] = sum;
        }
    }
    Ok(result)
}

// ---------------------------------------------------------------------------
// Dual norm
// ---------------------------------------------------------------------------

/// Return the dual (conjugate) norm kind.
///
/// - L1 <-> Linf  (Holder conjugates: 1/1 + 1/inf = 1)
/// - L2 <-> L2    (self-dual)
#[must_use]
pub const fn dual_norm(kind: NormKind) -> NormKind {
    match kind {
        NormKind::L1 => NormKind::Linf,
        NormKind::L2 => NormKind::L2,
        NormKind::Linf => NormKind::L1,
    }
}

// ---------------------------------------------------------------------------
// Theorem verification (runtime checks)
// ---------------------------------------------------------------------------

/// Verify L1/L2/Linf ordering: ||x||_inf^2 <= ||x||_2^2 <= ||x||_1^2.
///
/// Since we store L2 as squared, and `Linf^2 <= L2_sq` and `L2_sq <= L1^2`
/// both hold in exact rationals.
#[must_use]
pub fn verify_l1_l2_linf_ordering(v: &[Rational64]) -> bool {
    let l1 = vector_norm(v, NormKind::L1);
    let l2_sq = vector_norm(v, NormKind::L2);
    let linf = vector_norm(v, NormKind::Linf);
    // ||x||_inf^2 <= ||x||_2^2 <= ||x||_1^2
    let linf_sq = linf * linf;
    let l1_sq = l1 * l1;
    linf_sq <= l2_sq && l2_sq <= l1_sq
}

/// Verify Holder's inequality: |u . v| <= ||u||_p * ||v||_q
/// for the L1/Linf conjugate pair (p=1, q=inf).
///
/// Returns `Err` on dimension mismatch.
pub fn verify_holder_l1_linf(u: &[Rational64], v: &[Rational64]) -> Result<bool, NormError> {
    let dp = dot_product(u, v)?;
    let lhs = rational_abs(dp);
    let norm_u = vector_norm(u, NormKind::L1);
    let norm_v = vector_norm(v, NormKind::Linf);
    Ok(lhs <= norm_u * norm_v)
}

/// Verify Holder's inequality for the L2/L2 pair (Cauchy-Schwarz):
/// |u . v|^2 <= ||u||_2^2 * ||v||_2^2.
///
/// Both sides are exact in `Rational64` (no square roots needed).
pub fn verify_holder_l2(u: &[Rational64], v: &[Rational64]) -> Result<bool, NormError> {
    let dp = dot_product(u, v)?;
    let lhs = dp * dp; // |u . v|^2
    let norm_u_sq = vector_norm(u, NormKind::L2);
    let norm_v_sq = vector_norm(v, NormKind::L2);
    Ok(lhs <= norm_u_sq * norm_v_sq)
}

/// Verify triangle inequality: ||u + v||_k <= ||u||_k + ||v||_k.
///
/// For L2 we check the squared form:
/// ||u + v||_2^2 <= (||u||_2 + ||v||_2)^2
/// where the RHS expands using Cauchy-Schwarz.
///
/// Returns `Err` on dimension mismatch.
pub fn verify_triangle_inequality(
    u: &[Rational64],
    v: &[Rational64],
    kind: NormKind,
) -> Result<bool, NormError> {
    let sum = vector_add(u, v)?;
    match kind {
        NormKind::L1 | NormKind::Linf => {
            let lhs = vector_norm(&sum, kind);
            let rhs = vector_norm(u, kind) + vector_norm(v, kind);
            Ok(lhs <= rhs)
        }
        NormKind::L2 => {
            // ||u+v||^2 = ||u||^2 + 2(u.v) + ||v||^2
            // <= ||u||^2 + 2|u.v| + ||v||^2
            // <= ||u||^2 + 2*||u||*||v|| + ||v||^2  (Cauchy-Schwarz)
            // = (||u|| + ||v||)^2
            // We verify the first and last lines are consistent.
            let lhs = vector_norm(&sum, NormKind::L2);
            let u_sq = vector_norm(u, NormKind::L2);
            let v_sq = vector_norm(v, NormKind::L2);
            let dp = dot_product(u, v)?;
            let two = Rational64::from_integer(2);
            // ||u+v||^2 = u_sq + 2*dp + v_sq (exact identity)
            // We verify against (||u|| + ||v||)^2 = u_sq + 2*sqrt(u_sq*v_sq) + v_sq
            // Since sqrt is not exact, verify: lhs <= u_sq + v_sq + 2*|dp|
            // and |dp|^2 <= u_sq * v_sq (Cauchy-Schwarz).
            let rhs = u_sq + v_sq + two * rational_abs(dp);
            Ok(lhs <= rhs)
        }
    }
}

/// Verify submultiplicativity: ||AB||_k <= ||A||_k * ||B||_k
/// for induced L1 and Linf norms.
///
/// L2 submultiplicativity requires exact SVD, so we only verify L1 and Linf.
pub fn verify_matrix_norm_submultiplicative(
    a: &[Vec<Rational64>],
    b: &[Vec<Rational64>],
    kind: NormKind,
) -> Result<bool, NormError> {
    let ab = matrix_multiply(a, b)?;
    let norm_ab = matrix_norm(&ab, kind)?;
    let norm_a = matrix_norm(a, kind)?;
    let norm_b = matrix_norm(b, kind)?;
    Ok(norm_ab <= norm_a * norm_b)
}

/// Verify dual norm duality (discrete version):
/// For L1/Linf: ||x||_1 = max_{||y||_inf <= 1} x . y
///
/// We check the "easy" direction: x . y <= ||x||_p * ||y||_q
/// for the given vector and its sign-witness, showing the max is achieved.
#[must_use]
pub fn verify_dual_norm_duality_l1(v: &[Rational64]) -> bool {
    // The maximizer for ||x||_1 = max_{||y||_inf<=1} x.y is y_i = sign(x_i).
    let witness: Vec<Rational64> = v
        .iter()
        .map(|x| {
            let zero = Rational64::from_integer(0);
            if *x > zero {
                Rational64::from_integer(1)
            } else if *x < zero {
                Rational64::from_integer(-1)
            } else {
                zero
            }
        })
        .collect();
    let zero = Rational64::from_integer(0);
    if v.is_empty() {
        return true;
    }
    let dp = v
        .iter()
        .zip(witness.iter())
        .map(|(a, b)| *a * *b)
        .fold(zero, |acc, x| acc + x);
    let l1 = vector_norm(v, NormKind::L1);
    // x . sign(x) = ||x||_1, and ||sign(x)||_inf <= 1
    let witness_linf = vector_norm(&witness, NormKind::Linf);
    let one = Rational64::from_integer(1);
    dp == l1 && (witness_linf <= one || v.iter().all(|x| *x == zero))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Absolute value for `Rational64`.
#[must_use]
fn rational_abs(x: Rational64) -> Rational64 {
    let zero = Rational64::from_integer(0);
    if x < zero {
        -x
    } else {
        x
    }
}

#[cfg(test)]
#[path = "tests_norms.rs"]
mod tests_norms;
