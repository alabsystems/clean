// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edit Algebra: Rank-1 Update Properties
//!
//! Formalizes the algebraic structure of rank-1 weight updates:
//!   dW = u * v^T
//!
//! ## Key Theorems
//!
//! 1. **Commutativity**: dW1 + dW2 = dW2 + dW1 (matrix addition is commutative)
//! 2. **Associativity**: (dW1 + dW2) + dW3 = dW1 + (dW2 + dW3)
//! 3. **Identity**: dW + 0 = dW (zero matrix is additive identity)
//! 4. **Inverse**: dW + (-dW) = 0 (negation is additive inverse)
//! 5. **Exact invertibility**: (W + dW) - dW = W in exact arithmetic
//! 6. **Approximate invertibility**: ||(W + dW) - dW - W|| <= eps * ||W|| in IEEE-754

use super::NeuralSurgeryError;

/// A rank-1 weight update: dW = u * v^T.
///
/// Stored as the outer product factors rather than the full matrix,
/// since rank-1 structure is essential for the algebraic properties.
#[derive(Debug, Clone, PartialEq)]
pub struct RankOneUpdate {
    /// Left factor (column vector u).
    u: Vec<f64>,
    /// Right factor (column vector v, transposed to row in the outer product).
    v: Vec<f64>,
}

impl RankOneUpdate {
    /// Create a new rank-1 update from vectors u and v.
    ///
    /// The resulting matrix is dW = u * v^T with dimensions |u| x |v|.
    #[must_use]
    pub fn new(u: Vec<f64>, v: Vec<f64>) -> Self {
        Self { u, v }
    }

    /// Number of rows in the update matrix.
    #[must_use]
    pub fn rows(&self) -> usize {
        self.u.len()
    }

    /// Number of columns in the update matrix.
    #[must_use]
    pub fn cols(&self) -> usize {
        self.v.len()
    }

    /// Compute the (i, j) entry of the outer product u * v^T.
    #[must_use]
    pub fn entry(&self, i: usize, j: usize) -> f64 {
        self.u[i] * self.v[j]
    }

    /// Compute the Frobenius norm: ||dW||_F = ||u|| * ||v||.
    ///
    /// For rank-1 matrices, the Frobenius norm factors as the product of
    /// the vector 2-norms.
    #[must_use]
    pub fn frobenius_norm(&self) -> f64 {
        let u_norm: f64 = self.u.iter().map(|x| x * x).sum::<f64>().sqrt();
        let v_norm: f64 = self.v.iter().map(|x| x * x).sum::<f64>().sqrt();
        u_norm * v_norm
    }

    /// Negate the update: -dW = (-u) * v^T.
    #[must_use]
    pub fn negate(&self) -> Self {
        Self {
            u: self.u.iter().map(|x| -x).collect(),
            v: self.v.clone(),
        }
    }

    /// Zero update of the same dimensions.
    #[must_use]
    pub fn zero(rows: usize, cols: usize) -> Self {
        Self {
            u: vec![0.0; rows],
            v: vec![0.0; cols],
        }
    }
}

/// Specification of edit algebra theorems.
///
/// Each method returns `Ok(())` if the theorem holds for the given inputs,
/// or an error describing the violation. These serve as executable
/// specifications that can be checked against concrete inputs as well as
/// formal proof obligations.
#[derive(Debug)]
pub struct EditAlgebraSpec {
    /// Tolerance for floating-point comparisons in approximate theorems.
    tolerance: f64,
}

impl EditAlgebraSpec {
    /// Create a new spec with default tolerance (128 * f64 machine epsilon).
    #[must_use]
    pub fn new() -> Self {
        Self {
            tolerance: 128.0 * f64::EPSILON,
        }
    }

    /// Create a spec with custom tolerance.
    #[must_use]
    pub fn with_tolerance(tolerance: f64) -> Self {
        Self { tolerance }
    }

    // ---------------------------------------------------------------
    // Theorem 1: Commutativity of rank-1 update addition
    // ---------------------------------------------------------------

    /// **Theorem (Commutativity):** For rank-1 updates dW1, dW2 of the same
    /// dimensions, dW1 + dW2 = dW2 + dW1 entry-wise.
    ///
    /// Proof sketch: Matrix addition inherits commutativity from field addition.
    /// For each (i,j): (dW1 + dW2)[i,j] = dW1[i,j] + dW2[i,j]
    ///                                    = dW2[i,j] + dW1[i,j]  (commutativity of R)
    ///                                    = (dW2 + dW1)[i,j]
    pub fn verify_commutativity(
        &self,
        dw1: &RankOneUpdate,
        dw2: &RankOneUpdate,
    ) -> Result<(), NeuralSurgeryError> {
        if dw1.rows() != dw2.rows() || dw1.cols() != dw2.cols() {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "commutativity requires same dimensions".to_string(),
            });
        }
        for i in 0..dw1.rows() {
            for j in 0..dw1.cols() {
                let lhs = dw1.entry(i, j) + dw2.entry(i, j);
                let rhs = dw2.entry(i, j) + dw1.entry(i, j);
                if (lhs - rhs).abs() > self.tolerance {
                    return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                        property: format!("commutativity failed at ({i},{j}): {lhs} != {rhs}"),
                    });
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Theorem 2: Associativity of rank-1 update addition
    // ---------------------------------------------------------------

    /// **Theorem (Associativity):** For rank-1 updates dW1, dW2, dW3,
    /// (dW1 + dW2) + dW3 = dW1 + (dW2 + dW3) entry-wise.
    ///
    /// In exact arithmetic this is exact. In floating-point, associativity
    /// holds to within rounding error.
    pub fn verify_associativity(
        &self,
        dw1: &RankOneUpdate,
        dw2: &RankOneUpdate,
        dw3: &RankOneUpdate,
    ) -> Result<(), NeuralSurgeryError> {
        if dw1.rows() != dw2.rows()
            || dw2.rows() != dw3.rows()
            || dw1.cols() != dw2.cols()
            || dw2.cols() != dw3.cols()
        {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "associativity requires same dimensions".to_string(),
            });
        }
        for i in 0..dw1.rows() {
            for j in 0..dw1.cols() {
                let a = dw1.entry(i, j);
                let b = dw2.entry(i, j);
                let c = dw3.entry(i, j);
                let lhs = (a + b) + c;
                let rhs = a + (b + c);
                if (lhs - rhs).abs() > self.tolerance {
                    return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                        property: format!("associativity failed at ({i},{j}): {lhs} != {rhs}"),
                    });
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Theorem 3: Additive identity
    // ---------------------------------------------------------------

    /// **Theorem (Identity):** For any rank-1 update dW,
    /// dW + 0 = dW entry-wise.
    pub fn verify_identity(&self, dw: &RankOneUpdate) -> Result<(), NeuralSurgeryError> {
        let zero = RankOneUpdate::zero(dw.rows(), dw.cols());
        for i in 0..dw.rows() {
            for j in 0..dw.cols() {
                let lhs = dw.entry(i, j) + zero.entry(i, j);
                let rhs = dw.entry(i, j);
                if (lhs - rhs).abs() > self.tolerance {
                    return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                        property: format!("identity failed at ({i},{j}): {lhs} != {rhs}"),
                    });
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Theorem 4: Additive inverse
    // ---------------------------------------------------------------

    /// **Theorem (Inverse):** For any rank-1 update dW,
    /// dW + (-dW) = 0 entry-wise.
    pub fn verify_inverse(&self, dw: &RankOneUpdate) -> Result<(), NeuralSurgeryError> {
        let neg = dw.negate();
        for i in 0..dw.rows() {
            for j in 0..dw.cols() {
                let sum = dw.entry(i, j) + neg.entry(i, j);
                if sum.abs() > self.tolerance {
                    return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                        property: format!("inverse failed at ({i},{j}): dW + (-dW) = {sum} != 0"),
                    });
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Theorem 5: Exact invertibility
    // ---------------------------------------------------------------

    /// **Theorem (Exact Invertibility):** In exact arithmetic,
    /// (W + dW) - dW = W for any weight matrix W and rank-1 update dW.
    ///
    /// This is a direct consequence of the additive inverse property
    /// applied to each matrix entry.
    // Nested indexing into two distinct sources (`w[i][j]` and
    // `dw.entry(i, j)`); iterator rewrites would require `.zip` of nested
    // rows and obscure the (i, j) coordinates used in the error message.
    #[allow(clippy::needless_range_loop)]
    pub fn verify_exact_invertibility(
        &self,
        w: &[Vec<f64>],
        dw: &RankOneUpdate,
    ) -> Result<(), NeuralSurgeryError> {
        if w.is_empty() {
            return Ok(());
        }
        let rows = w.len();
        let cols = w[0].len();
        if rows != dw.rows() || cols != dw.cols() {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "dimension mismatch between W and dW".to_string(),
            });
        }
        for i in 0..rows {
            for j in 0..cols {
                let original = w[i][j];
                let edited = original + dw.entry(i, j);
                let recovered = edited - dw.entry(i, j);
                if (recovered - original).abs() > self.tolerance {
                    return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                        property: format!(
                            "exact invertibility failed at ({i},{j}): \
                             recovered={recovered}, original={original}"
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------
    // Theorem 6: Approximate invertibility under IEEE-754
    // ---------------------------------------------------------------

    /// **Theorem (Approximate Invertibility):** In IEEE-754 f32 arithmetic,
    /// ||(W + dW) - dW - W||_F <= eps * cond * ||W||_F
    ///
    /// where eps is machine epsilon and cond is the condition number
    /// of the operation (bounded by 2 for addition/subtraction).
    ///
    /// This bounds the roundtrip error of apply-then-undo.
    pub fn verify_approximate_invertibility(
        &self,
        w: &[Vec<f32>],
        dw_u: &[f32],
        dw_v: &[f32],
    ) -> Result<f64, NeuralSurgeryError> {
        if w.is_empty() {
            return Ok(0.0);
        }
        let rows = w.len();
        let cols = w[0].len();
        if rows != dw_u.len() || cols != dw_v.len() {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "dimension mismatch in f32 invertibility check".to_string(),
            });
        }

        let mut error_sq = 0.0_f64;
        let mut w_norm_sq = 0.0_f64;

        for i in 0..rows {
            for j in 0..cols {
                let w_ij = w[i][j];
                let dw_ij = dw_u[i] * dw_v[j];
                let edited = w_ij + dw_ij;
                let recovered = edited - dw_ij;
                let err = (recovered - w_ij) as f64;
                error_sq += err * err;
                w_norm_sq += (w_ij as f64) * (w_ij as f64);
            }
        }

        let error_norm = error_sq.sqrt();
        let w_norm = w_norm_sq.sqrt();

        // The theoretical bound: 2 * eps * ||W||
        // Factor of 2: one rounding in addition, one in subtraction.
        let bound = 2.0 * super::F32_MACHINE_EPSILON * w_norm;

        if error_norm > bound * (1.0 + self.tolerance) {
            return Err(NeuralSurgeryError::ErrorBoundExceeded {
                computed: error_norm,
                bound,
            });
        }

        Ok(error_norm)
    }
}

impl Default for EditAlgebraSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_update() -> RankOneUpdate {
        RankOneUpdate::new(vec![1.0, 2.0, 3.0], vec![4.0, 5.0])
    }

    fn sample_update_2() -> RankOneUpdate {
        RankOneUpdate::new(vec![0.5, -1.0, 0.3], vec![2.0, -3.0])
    }

    fn sample_update_3() -> RankOneUpdate {
        RankOneUpdate::new(vec![-0.7, 0.4, 1.2], vec![1.5, 0.8])
    }

    #[test]
    fn test_rank_one_entry() {
        let dw = sample_update();
        assert!((dw.entry(0, 0) - 4.0).abs() < 1e-10);
        assert!((dw.entry(1, 0) - 8.0).abs() < 1e-10);
        assert!((dw.entry(2, 1) - 15.0).abs() < 1e-10);
    }

    #[test]
    fn test_frobenius_norm() {
        let dw = RankOneUpdate::new(vec![3.0, 4.0], vec![1.0]);
        // ||u|| = 5, ||v|| = 1, ||dW||_F = 5
        assert!((dw.frobenius_norm() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_negate() {
        let dw = sample_update();
        let neg = dw.negate();
        assert!((neg.entry(0, 0) - (-4.0)).abs() < 1e-10);
        assert!((neg.entry(1, 1) - (-10.0)).abs() < 1e-10);
    }

    #[test]
    fn test_commutativity() {
        let spec = EditAlgebraSpec::new();
        let dw1 = sample_update();
        let dw2 = sample_update_2();
        spec.verify_commutativity(&dw1, &dw2)
            .expect("commutativity should hold");
    }

    #[test]
    fn test_associativity() {
        let spec = EditAlgebraSpec::new();
        let dw1 = sample_update();
        let dw2 = sample_update_2();
        let dw3 = sample_update_3();
        spec.verify_associativity(&dw1, &dw2, &dw3)
            .expect("associativity should hold");
    }

    #[test]
    fn test_identity() {
        let spec = EditAlgebraSpec::new();
        let dw = sample_update();
        spec.verify_identity(&dw).expect("identity should hold");
    }

    #[test]
    fn test_inverse() {
        let spec = EditAlgebraSpec::new();
        let dw = sample_update();
        spec.verify_inverse(&dw).expect("inverse should hold");
    }

    #[test]
    fn test_exact_invertibility() {
        let spec = EditAlgebraSpec::new();
        let w = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];
        let dw = sample_update();
        spec.verify_exact_invertibility(&w, &dw)
            .expect("exact invertibility should hold");
    }

    #[test]
    fn test_approximate_invertibility_f32() {
        let spec = EditAlgebraSpec::new();
        let w: Vec<Vec<f32>> = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];
        let u: Vec<f32> = vec![0.1, 0.2, 0.3];
        let v: Vec<f32> = vec![0.4, 0.5];
        let error = spec
            .verify_approximate_invertibility(&w, &u, &v)
            .expect("approximate invertibility should hold within bound");
        // Error should be very small for well-conditioned inputs
        assert!(error < 1e-5, "roundtrip error = {error}");
    }

    #[test]
    fn test_dimension_mismatch_commutativity() {
        let spec = EditAlgebraSpec::new();
        let dw1 = RankOneUpdate::new(vec![1.0, 2.0], vec![3.0]);
        let dw2 = RankOneUpdate::new(vec![1.0, 2.0, 3.0], vec![3.0]);
        assert!(spec.verify_commutativity(&dw1, &dw2).is_err());
    }

    #[test]
    fn test_zero_update_properties() {
        let spec = EditAlgebraSpec::new();
        let zero = RankOneUpdate::zero(3, 2);
        assert!((zero.frobenius_norm()).abs() < 1e-10);
        spec.verify_identity(&zero)
            .expect("identity on zero should hold");
        spec.verify_inverse(&zero)
            .expect("inverse of zero should hold");
    }
}
