// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Polynomial zonotope type and core arithmetic.
//!
//! A polynomial zonotope extends the standard zonotope with quadratic (and
//! higher-order) generator terms, enabling exact or near-exact propagation
//! through polynomial nonlinearities.
//!
//! ## Definition
//!
//! A polynomial zonotope of order p in d dimensions is:
//!
//! ```text
//! PZ = { c + sum_i eps_i * G_i + sum_{i<=j} eps_i * eps_j * Q_{ij}
//!        + delta * R  :  eps_i in [-1, 1], delta in [-1, 1] }
//! ```
//!
//! where:
//! - `c` is the center (d-dimensional)
//! - `G_i` are linear generators (d-dimensional, n of them)
//! - `Q_{ij}` are quadratic generators (d-dimensional, n*(n+1)/2 of them)
//! - `R` is the remainder vector (independent interval error from higher-order
//!   term overapproximation)
//!
//! The key advantage: when computing `x * y` where both x and y are
//! polynomial zonotopes sharing the same noise symbols eps_i, the quadratic
//! terms `eps_i * eps_j` capture the correlation exactly rather than
//! overapproximating with independent intervals.
//!
//! ## References
//!
//! - Kochdumper & Althoff, "Sparse Polynomial Zonotopes" (2020)
//! - Ladner et al., "Automatic Abstraction for Polynomial Zonotopes" (2023)
//! - Althoff, "Reachability Analysis of Nonlinear Systems" (2013)

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use crate::nn_verify::zonotope::ZonotopeError;

/// Error type for polynomial zonotope operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum PolyZonotopeError {
    /// Dimension mismatch in polynomial zonotope construction or operation.
    #[error("poly zonotope dimension mismatch: expected {expected}, got {got} at {context}")]
    DimensionMismatch {
        expected: usize,
        got: usize,
        context: &'static str,
    },

    /// Noise symbol count mismatch in binary operation.
    #[error("noise symbol mismatch: left has {left} symbols, right has {right}")]
    NoiseSymbolMismatch { left: usize, right: usize },

    /// Matrix dimensions incompatible for multiplication.
    #[error(
        "matrix dimension mismatch: {rows}x{cols} matrix cannot multiply {vec_dim}-dim vector"
    )]
    MatrixDimensionMismatch {
        rows: usize,
        cols: usize,
        vec_dim: usize,
    },

    /// Inherited zonotope error.
    #[error("zonotope error: {0}")]
    Zonotope(#[from] ZonotopeError),
}

/// Polynomial zonotope with f64 arithmetic.
///
/// Represents the set:
/// ```text
/// PZ = { c + sum_i eps_i * g_i + sum_{i<=j} eps_i * eps_j * q_{ij}
///        + delta * r  :  eps_i in [-1, 1], delta in [-1, 1] }
/// ```
///
/// where `r` is the remainder vector capturing overapproximation of
/// higher-order (cubic, quartic) terms from polynomial multiplication.
///
/// The noise symbols `eps_i` are shared across operations, enabling
/// dependency tracking through nonlinear computations.
#[derive(Debug, Clone, PartialEq)]
pub struct PolyZonotope {
    /// Center point (dimension d).
    pub(crate) center: Vec<f64>,
    /// Linear generators: `linear_gens[k]` is the d-dimensional generator
    /// for noise symbol k. Shape: n_sym generators, each of dimension d.
    pub(crate) linear_gens: Vec<Vec<f64>>,
    /// Quadratic generators stored in flattened upper-triangular order.
    /// For noise symbols i, j (i <= j): index = i * n_sym - i*(i-1)/2 + (j - i).
    /// Each entry is a d-dimensional vector.
    pub(crate) quad_gens: Vec<Vec<f64>>,
    /// Number of noise symbols.
    pub(crate) n_sym: usize,
    /// Independent interval remainder from higher-order term overapproximation.
    /// Adds +/- remainder[k] to dimension k of the interval hull.
    pub(crate) remainder: Vec<f64>,
}

impl PolyZonotope {
    /// Create a new polynomial zonotope with zero remainder.
    ///
    /// # Arguments
    /// - `center`: d-dimensional center point
    /// - `linear_gens`: n_sym linear generators, each d-dimensional
    /// - `quad_gens`: n_sym*(n_sym+1)/2 quadratic generators in upper-triangular
    ///   order, each d-dimensional
    /// - `n_sym`: number of noise symbols
    pub fn try_new(
        center: Vec<f64>,
        linear_gens: Vec<Vec<f64>>,
        quad_gens: Vec<Vec<f64>>,
        n_sym: usize,
    ) -> Result<Self, PolyZonotopeError> {
        let d = center.len();
        let expected_quad = n_sym * (n_sym + 1) / 2;

        if linear_gens.len() != n_sym {
            return Err(PolyZonotopeError::DimensionMismatch {
                expected: n_sym,
                got: linear_gens.len(),
                context: "linear generator count",
            });
        }

        for (i, g) in linear_gens.iter().enumerate() {
            if g.len() != d {
                return Err(PolyZonotopeError::DimensionMismatch {
                    expected: d,
                    got: g.len(),
                    context: if i == 0 {
                        "linear generator 0 dimension"
                    } else {
                        "linear generator dimension"
                    },
                });
            }
        }

        if quad_gens.len() != expected_quad {
            return Err(PolyZonotopeError::DimensionMismatch {
                expected: expected_quad,
                got: quad_gens.len(),
                context: "quadratic generator count",
            });
        }

        for (i, q) in quad_gens.iter().enumerate() {
            if q.len() != d {
                return Err(PolyZonotopeError::DimensionMismatch {
                    expected: d,
                    got: q.len(),
                    context: if i == 0 {
                        "quadratic generator 0 dimension"
                    } else {
                        "quadratic generator dimension"
                    },
                });
            }
        }

        Ok(Self {
            remainder: vec![0.0; d],
            center,
            linear_gens,
            quad_gens,
            n_sym,
        })
    }

    /// Create a polynomial zonotope with zero quadratic generators.
    ///
    /// This is equivalent to a standard (linear) zonotope lifted into
    /// polynomial zonotope representation.
    pub fn from_linear(
        center: Vec<f64>,
        linear_gens: Vec<Vec<f64>>,
    ) -> Result<Self, PolyZonotopeError> {
        let d = center.len();
        let n_sym = linear_gens.len();

        for (i, g) in linear_gens.iter().enumerate() {
            if g.len() != d {
                return Err(PolyZonotopeError::DimensionMismatch {
                    expected: d,
                    got: g.len(),
                    context: if i == 0 {
                        "linear generator 0 dimension"
                    } else {
                        "linear generator dimension"
                    },
                });
            }
        }

        let n_quad = n_sym * (n_sym + 1) / 2;
        let quad_gens = vec![vec![0.0; d]; n_quad];
        Ok(Self {
            remainder: vec![0.0; d],
            center,
            linear_gens,
            quad_gens,
            n_sym,
        })
    }

    /// Create a scalar polynomial zonotope (d=1) from interval [lo, hi].
    ///
    /// Center = (lo + hi) / 2, one linear generator = (hi - lo) / 2.
    #[must_use]
    pub fn from_interval(lo: f64, hi: f64) -> Self {
        let center = vec![(lo + hi) / 2.0];
        let half_width = (hi - lo) / 2.0;
        let linear_gens = vec![vec![half_width]];
        let quad_gens = vec![vec![0.0]]; // one quad gen for (0,0)
        Self {
            center,
            linear_gens,
            quad_gens,
            n_sym: 1,
            remainder: vec![0.0],
        }
    }

    /// Ambient dimension.
    #[must_use]
    pub fn dim(&self) -> usize {
        self.center.len()
    }

    /// Number of noise symbols.
    #[must_use]
    pub fn num_symbols(&self) -> usize {
        self.n_sym
    }

    /// Number of linear generators.
    #[must_use]
    pub fn num_linear_gens(&self) -> usize {
        self.linear_gens.len()
    }

    /// Number of quadratic generators.
    #[must_use]
    pub fn num_quad_gens(&self) -> usize {
        self.quad_gens.len()
    }

    /// Access the center.
    #[must_use]
    pub fn center(&self) -> &[f64] {
        &self.center
    }

    /// Access linear generators.
    #[must_use]
    pub fn linear_gens(&self) -> &[Vec<f64>] {
        &self.linear_gens
    }

    /// Access quadratic generators.
    #[must_use]
    pub fn quad_gens(&self) -> &[Vec<f64>] {
        &self.quad_gens
    }

    /// Index into upper-triangular quadratic generator storage.
    ///
    /// For noise symbols i, j (with i <= j):
    /// index = i * n_sym - i*(i-1)/2 + (j - i)
    #[must_use]
    pub(crate) fn quad_index(&self, i: usize, j: usize) -> usize {
        let (i, j) = if i <= j { (i, j) } else { (j, i) };
        i * self.n_sym - i * (i.wrapping_sub(1)) / 2 + (j - i)
    }

    /// Compute the interval hull (axis-aligned bounding box).
    ///
    /// For each dimension k, the hull accounts for:
    /// 1. Linear generators: eps_i in [-1, 1] contributes +/- |G_i[k]|
    /// 2. Quadratic generators:
    ///    - Off-diagonal (i != j): eps_i*eps_j in [-1, 1], contributes +/- |Q_{ij}[k]|
    ///    - Diagonal (i == j): eps_i^2 in [0, 1], contributes center shift of
    ///      Q_{ii}[k]*0.5 and half-width |Q_{ii}[k]|*0.5
    /// 3. Independent remainder: delta in [-1, 1] contributes +/- remainder[k]
    #[must_use]
    pub fn to_interval(&self) -> (Vec<f64>, Vec<f64>) {
        let d = self.dim();
        let mut lower = self.center.clone();
        let mut upper = self.center.clone();

        // Linear generators: eps_i in [-1, 1]
        for g in &self.linear_gens {
            for k in 0..d {
                let abs_g = g[k].abs();
                lower[k] -= abs_g;
                upper[k] += abs_g;
            }
        }

        // Quadratic generators: iterate through upper-triangular (i, j) pairs
        let mut idx = 0;
        for i in 0..self.n_sym {
            for j in i..self.n_sym {
                let q = &self.quad_gens[idx];
                if i == j {
                    // Diagonal: eps_i^2 in [0, 1], midpoint = 0.5, half-width = 0.5
                    // Shift center by Q_{ii}[k] * 0.5, add +/- |Q_{ii}[k]| * 0.5
                    for k in 0..d {
                        let shift = q[k] * 0.5;
                        let half_width = q[k].abs() * 0.5;
                        lower[k] += shift - half_width;
                        upper[k] += shift + half_width;
                    }
                } else {
                    // Off-diagonal: eps_i * eps_j in [-1, 1]
                    for k in 0..d {
                        let abs_q = q[k].abs();
                        lower[k] -= abs_q;
                        upper[k] += abs_q;
                    }
                }
                idx += 1;
            }
        }

        // Independent remainder from higher-order term overapproximation
        for k in 0..d {
            lower[k] -= self.remainder[k];
            upper[k] += self.remainder[k];
        }

        (lower, upper)
    }

    /// Addition of two polynomial zonotopes sharing the same noise symbols.
    ///
    /// PZ1 + PZ2 = (c1 + c2, G1 + G2, Q1 + Q2, R1 + R2)
    ///
    /// Both must have the same number of noise symbols and same dimension.
    pub fn add(&self, other: &PolyZonotope) -> Result<PolyZonotope, PolyZonotopeError> {
        if self.n_sym != other.n_sym {
            return Err(PolyZonotopeError::NoiseSymbolMismatch {
                left: self.n_sym,
                right: other.n_sym,
            });
        }
        if self.dim() != other.dim() {
            return Err(PolyZonotopeError::DimensionMismatch {
                expected: self.dim(),
                got: other.dim(),
                context: "addition operand dimension",
            });
        }

        let _d = self.dim();

        let center: Vec<f64> = self
            .center
            .iter()
            .zip(other.center.iter())
            .map(|(a, b)| a + b)
            .collect();

        let linear_gens: Vec<Vec<f64>> = self
            .linear_gens
            .iter()
            .zip(other.linear_gens.iter())
            .map(|(a, b)| a.iter().zip(b.iter()).map(|(x, y)| x + y).collect())
            .collect();

        let quad_gens: Vec<Vec<f64>> = self
            .quad_gens
            .iter()
            .zip(other.quad_gens.iter())
            .map(|(a, b)| a.iter().zip(b.iter()).map(|(x, y)| x + y).collect())
            .collect();

        let remainder: Vec<f64> = self
            .remainder
            .iter()
            .zip(other.remainder.iter())
            .map(|(a, b)| a + b)
            .collect();

        let mut pz = PolyZonotope::try_new(center, linear_gens, quad_gens, self.n_sym)?;
        pz.remainder = remainder;
        Ok(pz)
    }

    /// Scalar multiplication: scale all generators, center, and remainder.
    #[must_use]
    pub fn scale(&self, s: f64) -> PolyZonotope {
        let center: Vec<f64> = self.center.iter().map(|c| c * s).collect();
        let linear_gens: Vec<Vec<f64>> = self
            .linear_gens
            .iter()
            .map(|g| g.iter().map(|v| v * s).collect())
            .collect();
        let quad_gens: Vec<Vec<f64>> = self
            .quad_gens
            .iter()
            .map(|q| q.iter().map(|v| v * s).collect())
            .collect();
        let remainder: Vec<f64> = self.remainder.iter().map(|r| r * s.abs()).collect();

        PolyZonotope {
            center,
            linear_gens,
            quad_gens,
            n_sym: self.n_sym,
            remainder,
        }
    }

    /// Matrix-vector multiplication: W * PZ + b.
    ///
    /// If PZ has center c and generators {G_i}, {Q_ij}, then W*PZ + b has:
    /// - center' = W*c + b
    /// - linear_gen'_i = W * G_i
    /// - quad_gen'_ij = W * Q_ij
    /// - remainder' = |W| * remainder (element-wise absolute matrix)
    ///
    /// `weight` is an m x d matrix (m rows, d cols), `bias` has length m.
    pub fn linear_transform(
        &self,
        weight: &[Vec<f64>],
        bias: &[f64],
    ) -> Result<PolyZonotope, PolyZonotopeError> {
        let m = weight.len();
        let d = self.dim();

        if m != bias.len() {
            return Err(PolyZonotopeError::MatrixDimensionMismatch {
                rows: m,
                cols: d,
                vec_dim: bias.len(),
            });
        }

        for row in weight {
            if row.len() != d {
                return Err(PolyZonotopeError::MatrixDimensionMismatch {
                    rows: m,
                    cols: row.len(),
                    vec_dim: d,
                });
            }
        }

        let mat_vec = |v: &[f64]| -> Vec<f64> {
            weight
                .iter()
                .enumerate()
                .map(|(i, row)| row.iter().zip(v.iter()).map(|(w, x)| w * x).sum::<f64>() + bias[i])
                .collect()
        };

        let mat_vec_no_bias = |v: &[f64]| -> Vec<f64> {
            weight
                .iter()
                .map(|row| row.iter().zip(v.iter()).map(|(w, x)| w * x).sum::<f64>())
                .collect()
        };

        let new_center = mat_vec(&self.center);
        let new_linear: Vec<Vec<f64>> = self
            .linear_gens
            .iter()
            .map(|g| mat_vec_no_bias(g))
            .collect();
        let new_quad: Vec<Vec<f64>> = self.quad_gens.iter().map(|q| mat_vec_no_bias(q)).collect();

        // Transform remainder: |W| * R
        let new_remainder: Vec<f64> = weight
            .iter()
            .map(|row| {
                row.iter()
                    .zip(self.remainder.iter())
                    .map(|(w, r)| w.abs() * r)
                    .sum()
            })
            .collect();

        let mut pz = PolyZonotope::try_new(new_center, new_linear, new_quad, self.n_sym)?;
        pz.remainder = new_remainder;
        Ok(pz)
    }

    /// Hadamard (element-wise) product of two 1D polynomial zonotopes.
    ///
    /// For scalar polynomial zonotopes x and y sharing noise symbols:
    /// ```text
    /// x = cx + sum_i eps_i * gx_i + sum_{ij} eps_i*eps_j * qx_{ij} + delta_x * rx
    /// y = cy + sum_i eps_i * gy_i + sum_{ij} eps_i*eps_j * qy_{ij} + delta_y * ry
    /// ```
    ///
    /// The product x*y generates:
    /// - Center: cx * cy
    /// - Linear terms from cx * gy_i + cy * gx_i
    /// - Quadratic terms from cx * qy_{ij} + cy * qx_{ij} + gx_i * gy_j
    /// - Higher-order terms (cubic, quartic) are bounded and added to the
    ///   independent remainder.
    ///
    /// This captures the key quadratic dependencies that linear zonotopes miss.
    pub fn hadamard_product_scalar(
        &self,
        other: &PolyZonotope,
    ) -> Result<PolyZonotope, PolyZonotopeError> {
        if self.dim() != 1 || other.dim() != 1 {
            return Err(PolyZonotopeError::DimensionMismatch {
                expected: 1,
                got: self.dim().max(other.dim()),
                context: "hadamard_product_scalar requires d=1",
            });
        }
        if self.n_sym != other.n_sym {
            return Err(PolyZonotopeError::NoiseSymbolMismatch {
                left: self.n_sym,
                right: other.n_sym,
            });
        }

        let n = self.n_sym;
        let cx = self.center[0];
        let cy = other.center[0];

        // Center of product
        let new_center = cx * cy;

        // Linear generators: cx * gy_i + cy * gx_i
        let mut new_linear = Vec::with_capacity(n);
        for i in 0..n {
            let gx_i = self.linear_gens[i][0];
            let gy_i = other.linear_gens[i][0];
            new_linear.push(vec![cx * gy_i + cy * gx_i]);
        }

        // Quadratic generators: cx*qy_{ij} + cy*qx_{ij} + gx_i*gy_j
        let n_quad = n * (n + 1) / 2;
        let mut new_quad = Vec::with_capacity(n_quad);
        for i in 0..n {
            for j in i..n {
                let idx = self.quad_index(i, j);
                let qx = self.quad_gens[idx][0];
                let qy = other.quad_gens[idx][0];

                let gx_i = self.linear_gens[i][0];
                let gy_j = other.linear_gens[j][0];
                let cross = if i == j {
                    gx_i * gy_j
                } else {
                    // For i != j: eps_i*eps_j appears from gx_i*gy_j and gx_j*gy_i
                    let gx_j = self.linear_gens[j][0];
                    let gy_i = other.linear_gens[i][0];
                    gx_i * gy_j + gx_j * gy_i
                };

                new_quad.push(vec![cx * qy + cy * qx + cross]);
            }
        }

        // Higher-order remainder: overapproximate cubic and quartic terms.
        // The cubic terms come from linear * quad cross-products,
        // the quartic terms from quad * quad products.
        // Also account for existing remainders interacting with everything.
        let mut ho_remainder = 0.0;

        // Cubic terms: gx_i * qy_{jk} * eps_i * eps_j * eps_k
        //              gy_i * qx_{jk} * eps_i * eps_j * eps_k
        // Each |eps_i * eps_j * eps_k| <= 1, so bound by sum of abs values.
        for i in 0..n {
            let gx_i = self.linear_gens[i][0].abs();
            let gy_i = other.linear_gens[i][0].abs();
            for jk_idx in 0..n_quad {
                let qy = other.quad_gens[jk_idx][0].abs();
                let qx = self.quad_gens[jk_idx][0].abs();
                ho_remainder += gx_i * qy + gy_i * qx;
            }
        }

        // Quartic terms: qx_{ij} * qy_{kl} * eps_i * eps_j * eps_k * eps_l
        for idx1 in 0..n_quad {
            let qx = self.quad_gens[idx1][0].abs();
            for idx2 in 0..n_quad {
                let qy = other.quad_gens[idx2][0].abs();
                ho_remainder += qx * qy;
            }
        }

        // Existing remainder interactions:
        // rx * (|cy| + sum |gy_i| + sum |qy_{ij}|)
        // ry * (|cx| + sum |gx_i| + sum |qx_{ij}|)
        // rx * ry
        let rx = self.remainder[0];
        let ry = other.remainder[0];
        if rx > 0.0 || ry > 0.0 {
            let abs_x_total: f64 = cy.abs()
                + other.linear_gens.iter().map(|g| g[0].abs()).sum::<f64>()
                + other.quad_gens.iter().map(|q| q[0].abs()).sum::<f64>()
                + ry;
            let abs_y_total: f64 = cx.abs()
                + self.linear_gens.iter().map(|g| g[0].abs()).sum::<f64>()
                + self.quad_gens.iter().map(|q| q[0].abs()).sum::<f64>()
                + rx;
            ho_remainder += rx * abs_x_total + ry * abs_y_total;
        }

        let mut pz = PolyZonotope::try_new(vec![new_center], new_linear, new_quad, n)?;
        pz.remainder = vec![ho_remainder];
        Ok(pz)
    }

    /// Evaluate the polynomial zonotope at specific noise symbol values.
    ///
    /// Computes: `c + sum_i eps[i] * G_i + sum_{i<=j} eps[i]*eps[j] * Q_{ij}`
    ///
    /// Note: the remainder is not included in evaluation since it represents
    /// an independent overapproximation interval, not a function of the noise
    /// symbols.
    pub fn evaluate(&self, eps: &[f64]) -> Result<Vec<f64>, PolyZonotopeError> {
        if eps.len() != self.n_sym {
            return Err(PolyZonotopeError::DimensionMismatch {
                expected: self.n_sym,
                got: eps.len(),
                context: "noise symbol vector length",
            });
        }

        let d = self.dim();
        let mut result = self.center.clone();

        // Linear terms
        for (i, g) in self.linear_gens.iter().enumerate() {
            for k in 0..d {
                result[k] += eps[i] * g[k];
            }
        }

        // Quadratic terms
        for i in 0..self.n_sym {
            for j in i..self.n_sym {
                let idx = self.quad_index(i, j);
                let q = &self.quad_gens[idx];
                let coeff = eps[i] * eps[j];
                for k in 0..d {
                    result[k] += coeff * q[k];
                }
            }
        }

        Ok(result)
    }

    /// Compute the maximum absolute value of all generators in a given
    /// dimension, used for tightness analysis.
    #[must_use]
    #[allow(dead_code)] // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    pub(crate) fn generator_norm(&self, dim: usize) -> f64 {
        let linear_sum: f64 = self.linear_gens.iter().map(|g| g[dim].abs()).sum();
        let quad_sum: f64 = self.quad_gens.iter().map(|q| q[dim].abs()).sum();
        linear_sum + quad_sum + self.remainder[dim]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poly_zonotope_from_interval() {
        let pz = PolyZonotope::from_interval(1.0, 3.0);
        assert_eq!(pz.dim(), 1);
        assert_eq!(pz.num_symbols(), 1);
        assert!((pz.center[0] - 2.0).abs() < 1e-10);
        assert!((pz.linear_gens[0][0] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_evaluate_center() {
        let pz = PolyZonotope::from_linear(vec![1.0, 2.0], vec![vec![0.5, 0.0], vec![0.0, 0.3]])
            .expect("should create linear poly zonotope");

        let result = pz.evaluate(&[0.0, 0.0]).expect("should evaluate");
        assert!((result[0] - 1.0).abs() < 1e-10);
        assert!((result[1] - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_evaluate_at_corners() {
        let pz = PolyZonotope::from_interval(1.0, 3.0);

        // eps = 1 -> center + linear = 2 + 1 = 3 (+ quad[0]*1 = 0)
        let hi = pz.evaluate(&[1.0]).expect("should evaluate");
        assert!((hi[0] - 3.0).abs() < 1e-10);

        // eps = -1 -> center - linear = 2 - 1 = 1
        let lo = pz.evaluate(&[-1.0]).expect("should evaluate");
        assert!((lo[0] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_interval_hull() {
        let pz = PolyZonotope::try_new(
            vec![5.0],
            vec![vec![2.0], vec![1.0]],
            vec![vec![0.5], vec![0.3], vec![0.1]],
            2,
        )
        .expect("should construct");

        let (lo, hi) = pz.to_interval();
        // Linear: lower = 5 - 2 - 1 = 2.0, upper = 5 + 2 + 1 = 8.0
        // Quad (0,0) diagonal: eps_0^2 in [0,1], q=0.5: shift=0.25, hw=0.25
        //   lower += 0 = 2.0, upper += 0.5 = 8.5
        // Quad (0,1) off-diagonal: eps_0*eps_1 in [-1,1], q=0.3: +/- 0.3
        //   lower = 1.7, upper = 8.8
        // Quad (1,1) diagonal: eps_1^2 in [0,1], q=0.1: shift=0.05, hw=0.05
        //   lower += 0 = 1.7, upper += 0.1 = 8.9
        assert!((lo[0] - 1.7).abs() < 1e-10);
        assert!((hi[0] - 8.9).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_add() {
        let pz1 = PolyZonotope::from_interval(1.0, 3.0);
        let pz2 = PolyZonotope::from_interval(2.0, 4.0);

        let sum = pz1.add(&pz2).expect("should add");
        assert!((sum.center[0] - 5.0).abs() < 1e-10);
        // linear: 1.0 + 1.0 = 2.0
        assert!((sum.linear_gens[0][0] - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_scale() {
        let pz = PolyZonotope::from_interval(1.0, 3.0);
        let scaled = pz.scale(2.0);
        assert!((scaled.center[0] - 4.0).abs() < 1e-10);
        assert!((scaled.linear_gens[0][0] - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_linear_transform() {
        let pz = PolyZonotope::from_linear(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]])
            .expect("should create");

        // 2x2 identity + bias [10, 20]
        let weight = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
        let bias = vec![10.0, 20.0];
        let result = pz
            .linear_transform(&weight, &bias)
            .expect("should transform");

        assert!((result.center[0] - 11.0).abs() < 1e-10);
        assert!((result.center[1] - 22.0).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_hadamard_scalar() {
        // x in [0, 2] (center=1, gen=1), y in [1, 3] (center=2, gen=1)
        // Product range: [0*1, 2*3] = [0, 6], center = 1*2=2
        let x = PolyZonotope::try_new(vec![1.0], vec![vec![1.0]], vec![vec![0.0]], 1)
            .expect("should create x");
        let y = PolyZonotope::try_new(vec![2.0], vec![vec![1.0]], vec![vec![0.0]], 1)
            .expect("should create y");

        let product = x.hadamard_product_scalar(&y).expect("should multiply");

        // Center: 1*2 = 2
        assert!((product.center[0] - 2.0).abs() < 1e-10);
        // Linear gen: cx*gy + cy*gx = 1*1 + 2*1 = 3
        assert!((product.linear_gens[0][0] - 3.0).abs() < 1e-10);
        // Quad gen (0,0): cross term gx*gy = 1*1 = 1
        assert!((product.quad_gens[0][0] - 1.0).abs() < 1e-10);
        // Remainder should be 0 (no existing quad gens to create cubics)
        assert!((product.remainder[0]).abs() < 1e-10);
    }

    #[test]
    fn test_poly_zonotope_dimension_mismatch() {
        let result = PolyZonotope::try_new(
            vec![1.0, 2.0],
            vec![vec![1.0]], // wrong dim: should be 2
            vec![vec![0.0, 0.0]],
            1,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_poly_zonotope_noise_symbol_mismatch() {
        let pz1 = PolyZonotope::from_interval(0.0, 1.0);
        let pz2 = PolyZonotope::try_new(
            vec![0.5],
            vec![vec![0.25], vec![0.25]],
            vec![vec![0.0], vec![0.0], vec![0.0]],
            2,
        )
        .expect("should create");

        let result = pz1.add(&pz2);
        assert!(result.is_err());
    }

    #[test]
    fn test_poly_zonotope_hadamard_soundness() {
        // Verify that the product interval hull contains all true product values
        let x = PolyZonotope::try_new(vec![1.5], vec![vec![0.5]], vec![vec![0.0]], 1)
            .expect("should create x");
        let y = PolyZonotope::try_new(vec![2.0], vec![vec![0.3]], vec![vec![0.0]], 1)
            .expect("should create y");

        let product = x.hadamard_product_scalar(&y).expect("should multiply");
        let (lo, hi) = product.to_interval();

        for &eps in &[-1.0, -0.5, 0.0, 0.5, 1.0] {
            let xv = x.evaluate(&[eps]).expect("eval")[0];
            let yv = y.evaluate(&[eps]).expect("eval")[0];
            let true_prod = xv * yv;
            assert!(
                true_prod >= lo[0] - 1e-10 && true_prod <= hi[0] + 1e-10,
                "product {true_prod} outside [{}, {}] at eps={eps}",
                lo[0],
                hi[0]
            );
        }
    }
}
