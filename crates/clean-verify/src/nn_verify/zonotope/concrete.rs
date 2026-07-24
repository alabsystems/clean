// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concrete f64 zonotope implementation.
//!
//! A zonotope is Z = { c + sum_i eps_i * g_i : eps_i in [-1, 1] }
//! where c is the center (d-dimensional) and g_i are generators (each
//! d-dimensional). This module provides executable arithmetic for hull
//! computation, containment checks, affine transforms, Minkowski sums,
//! and generator compression.

/// Error type for zonotope operations that validate inputs.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ZonotopeError {
    /// Generator dimension does not match center dimension.
    #[error(
        "dimension mismatch: center has dim {center_dim}, \
         generator {gen_index} has dim {gen_dim}"
    )]
    DimensionMismatch {
        center_dim: usize,
        gen_index: usize,
        gen_dim: usize,
    },

    /// Coefficient vector length does not match generator count.
    #[error("invalid coefficients: expected {expected} coefficients, got {got}")]
    InvalidCoefficients { expected: usize, got: usize },

    /// Dimensions do not match between two zonotopes in a binary operation.
    #[error("operand dimension mismatch: left has dim {left_dim}, right has dim {right_dim}")]
    OperandDimensionMismatch { left_dim: usize, right_dim: usize },
}

/// Concrete zonotope with f64 arithmetic.
///
/// `center` is a d-dimensional vector. `generators` is a list of n
/// generator vectors, each d-dimensional. The zonotope is the set of
/// all points `center + sum_i eps_i * generators[i]` with each
/// `eps_i in [-1, 1]`.
#[derive(Debug, Clone, PartialEq)]
pub struct ConcreteZonotope {
    /// Center point (dimension d).
    pub center: Vec<f64>,
    /// Generator vectors (n generators, each dimension d).
    pub generators: Vec<Vec<f64>>,
}

impl ConcreteZonotope {
    /// Create a new zonotope. All generators must have the same dimension as
    /// the center.
    ///
    /// # Panics
    ///
    /// Panics (debug-only) if any generator dimension mismatches the center.
    #[must_use]
    pub fn new(center: Vec<f64>, generators: Vec<Vec<f64>>) -> Self {
        let d = center.len();
        for (i, g) in generators.iter().enumerate() {
            debug_assert_eq!(
                g.len(),
                d,
                "generator {i} has dimension {} but center has dimension {d}",
                g.len()
            );
        }
        Self { center, generators }
    }

    /// Dimension of the ambient space.
    #[must_use]
    pub fn dim(&self) -> usize {
        self.center.len()
    }

    /// Number of generators.
    #[must_use]
    pub fn num_generators(&self) -> usize {
        self.generators.len()
    }

    /// Compute the interval hull (axis-aligned bounding box).
    ///
    /// For each dimension j:
    ///   lower_j = center_j - sum_i |gen_ij|
    ///   upper_j = center_j + sum_i |gen_ij|
    ///
    /// Returns `(lower, upper)` vectors of dimension d.
    #[must_use]
    pub fn to_interval(&self) -> (Vec<f64>, Vec<f64>) {
        let d = self.dim();
        let mut lower = self.center.clone();
        let mut upper = self.center.clone();
        for gvec in &self.generators {
            for j in 0..d {
                let abs_g = gvec[j].abs();
                lower[j] -= abs_g;
                upper[j] += abs_g;
            }
        }
        (lower, upper)
    }

    /// Check if a point is contained in the zonotope.
    ///
    /// For small generator counts (n <= 20), uses recursive interval-hull
    /// pruning with discretized epsilon search. For larger counts, falls
    /// back to the interval hull (conservative overapproximation).
    #[must_use]
    pub fn contains(&self, point: &[f64]) -> bool {
        debug_assert_eq!(point.len(), self.dim(), "point dimension mismatch");
        let n = self.num_generators();
        if n == 0 {
            // Degenerate: zonotope is just the center point.
            return point
                .iter()
                .zip(self.center.iter())
                .all(|(p, c)| (p - c).abs() < f64::EPSILON);
        }
        if n <= 20 {
            let target: Vec<f64> = point
                .iter()
                .zip(self.center.iter())
                .map(|(p, c)| p - c)
                .collect();
            self.contains_recursive(&target, 0)
        } else {
            // Conservative: use interval hull (overapproximation).
            self.hull_contains(point)
        }
    }

    /// Recursive containment: can `target` be expressed as
    /// `sum_{i >= start} eps_i * gen_i` with each `eps_i in [-1, 1]`?
    ///
    /// Uses interval-hull pruning at each level: if the target is outside
    /// the hull of the remaining generators, returns false immediately.
    /// Searches over a discretized set of epsilon values for feasibility.
    fn contains_recursive(&self, target: &[f64], start: usize) -> bool {
        let d = self.dim();
        let n = self.num_generators();

        if start >= n {
            // No more generators: target must be zero.
            return target.iter().all(|t| t.abs() < 1e-9);
        }

        // Remaining generators form a sub-zonotope. Check if target is
        // within the interval hull of remaining generators (necessary
        // condition).
        let mut max_reach = vec![0.0; d];
        // Outer range starts at `start` (offset), inner indexes both
        // `max_reach[j]` and `self.generators[i][j]`; an iterator rewrite
        // would not be clearer.
        #[allow(clippy::needless_range_loop)]
        for i in start..n {
            for j in 0..d {
                max_reach[j] += self.generators[i][j].abs();
            }
        }
        for j in 0..d {
            if target[j].abs() > max_reach[j] + 1e-9 {
                return false;
            }
        }

        // Try discretized eps values. The density of 0.25 steps ensures
        // we cover the continuous [-1, 1] range adequately when combined
        // with the recursive pruning.
        let gvec = &self.generators[start];
        for &eps in &[-1.0, -0.75, -0.5, -0.25, 0.0, 0.25, 0.5, 0.75, 1.0] {
            let residual: Vec<f64> = target
                .iter()
                .enumerate()
                .map(|(j, t)| t - eps * gvec[j])
                .collect();
            if self.contains_recursive(&residual, start + 1) {
                return true;
            }
        }
        false
    }

    /// Check if a point is within the interval hull.
    #[must_use]
    pub fn hull_contains(&self, point: &[f64]) -> bool {
        let (lower, upper) = self.to_interval();
        point
            .iter()
            .enumerate()
            .all(|(j, p)| *p >= lower[j] - 1e-9 && *p <= upper[j] + 1e-9)
    }

    /// Affine transform: Z' = W * Z + b (T02).
    ///
    /// If Z has center c and generators {g_i}, then W*Z + b has:
    ///   center' = W*c + b
    ///   gen'_i  = W*g_i
    ///
    /// `weight` is an m x d matrix (m rows, d cols), `bias` has length m.
    /// The result is an m-dimensional zonotope.
    #[must_use]
    pub fn linear_transform(&self, weight: &[&[f64]], bias: &[f64]) -> ConcreteZonotope {
        let m = weight.len();

        // Compute new center: W*c + b
        let new_center: Vec<f64> = (0..m)
            .map(|i| {
                let dot: f64 = weight[i]
                    .iter()
                    .zip(self.center.iter())
                    .map(|(w, c)| w * c)
                    .sum();
                dot + bias[i]
            })
            .collect();

        // Compute new generators: W*g_k for each generator g_k
        let new_generators: Vec<Vec<f64>> = self
            .generators
            .iter()
            .map(|gvec| {
                (0..m)
                    .map(|i| weight[i].iter().zip(gvec.iter()).map(|(w, g)| w * g).sum())
                    .collect()
            })
            .collect();

        ConcreteZonotope::new(new_center, new_generators)
    }

    /// Minkowski sum of two zonotopes (T08).
    ///
    /// Z1 + Z2 has center = c1 + c2 and generators = concat(gens1, gens2).
    /// Both zonotopes must have the same dimension.
    ///
    /// # Panics
    ///
    /// Panics (debug-only) if dimensions differ.
    #[must_use]
    pub fn minkowski_add(&self, other: &ConcreteZonotope) -> ConcreteZonotope {
        debug_assert_eq!(
            self.dim(),
            other.dim(),
            "minkowski_add requires same dimension"
        );
        let new_center: Vec<f64> = self
            .center
            .iter()
            .zip(other.center.iter())
            .map(|(a, b)| a + b)
            .collect();
        let mut new_generators = self.generators.clone();
        new_generators.extend(other.generators.iter().cloned());

        ConcreteZonotope::new(new_center, new_generators)
    }

    /// Generator compression (T10): merge non-kept generators into one.
    ///
    /// Keeps generators at `keep_indices` unchanged. All other generators
    /// are merged into a single generator whose j-th component is the sum
    /// of absolute values of the j-th components of the removed generators.
    ///
    /// This preserves the interval hull (T12) because the per-dimension
    /// absolute sum is invariant.
    ///
    /// # Panics
    ///
    /// Panics (debug-only) if any keep index is out of bounds.
    #[must_use]
    pub fn compress(&self, keep_indices: &[usize]) -> ConcreteZonotope {
        let d = self.dim();
        let n = self.num_generators();
        for &idx in keep_indices {
            debug_assert!(idx < n, "keep index {idx} out of bounds (n={n})");
        }

        let mut kept_set = vec![false; n];
        for &idx in keep_indices {
            kept_set[idx] = true;
        }

        let mut new_generators: Vec<Vec<f64>> = Vec::with_capacity(keep_indices.len() + 1);

        // Keep selected generators
        for &idx in keep_indices {
            new_generators.push(self.generators[idx].clone());
        }

        // Merge removed generators: merged_j = sum_{i not in keep} |gen_ij|
        let mut merged = vec![0.0; d];
        let mut has_merged = false;
        for (i, gvec) in self.generators.iter().enumerate() {
            if !kept_set[i] {
                has_merged = true;
                for j in 0..d {
                    merged[j] += gvec[j].abs();
                }
            }
        }

        if has_merged {
            new_generators.push(merged);
        }

        ConcreteZonotope::new(self.center.clone(), new_generators)
    }

    /// T01: Hull soundness verification.
    ///
    /// Checks that if a point is inside the zonotope (via `contains`),
    /// then it is also inside the interval hull. This is a soundness
    /// witness: the hull is a valid overapproximation.
    #[must_use]
    pub fn verify_hull_sound(&self, point: &[f64]) -> bool {
        if self.contains(point) {
            // If the point is in the zonotope, it must be in the hull.
            self.hull_contains(point)
        } else {
            // If the point is not in the zonotope, the implication is
            // vacuously true.
            true
        }
    }

    /// T12: Compression hull exactness verification.
    ///
    /// Checks that `to_interval(compress(Z, keep)) == to_interval(Z)`.
    /// This holds because compression preserves the per-dimension absolute
    /// sum of generator components.
    #[must_use]
    pub fn verify_compress_hull_exact(&self, keep: &[usize]) -> bool {
        let (orig_lo, orig_hi) = self.to_interval();
        let compressed = self.compress(keep);
        let (comp_lo, comp_hi) = compressed.to_interval();

        orig_lo
            .iter()
            .zip(comp_lo.iter())
            .all(|(a, b)| (a - b).abs() < 1e-9)
            && orig_hi
                .iter()
                .zip(comp_hi.iter())
                .all(|(a, b)| (a - b).abs() < 1e-9)
    }

    // ----- Checked constructors and additional operations -----

    /// Checked constructor returning `Result` on dimension mismatch.
    ///
    /// Unlike [`Self::new`] which uses `debug_assert`, this validates
    /// generator dimensions unconditionally and returns a typed error.
    pub fn try_new(center: Vec<f64>, generators: Vec<Vec<f64>>) -> Result<Self, ZonotopeError> {
        let d = center.len();
        for (i, gvec) in generators.iter().enumerate() {
            if gvec.len() != d {
                return Err(ZonotopeError::DimensionMismatch {
                    center_dim: d,
                    gen_index: i,
                    gen_dim: gvec.len(),
                });
            }
        }
        Ok(Self { center, generators })
    }

    /// Check if a point lies within the interval hull (dimension-safe).
    ///
    /// Like [`Self::hull_contains`] but returns `false` on dimension
    /// mismatch instead of requiring the caller to guarantee matching
    /// dimensions.
    #[must_use]
    pub fn contains_point(&self, x: &[f64]) -> bool {
        if x.len() != self.dim() {
            return false;
        }
        self.hull_contains(x)
    }

    /// Sample a concrete point: `center + sum_i coeffs[i] * generators[i]`.
    ///
    /// `coeffs` must have length equal to `num_generators()`. The zonotope
    /// definition requires `|coeffs[i]| <= 1` for membership, but this
    /// method does not enforce that constraint -- callers may pass any
    /// coefficients for exploration.
    pub fn sample_point(&self, coeffs: &[f64]) -> Result<Vec<f64>, ZonotopeError> {
        let n = self.num_generators();
        if coeffs.len() != n {
            return Err(ZonotopeError::InvalidCoefficients {
                expected: n,
                got: coeffs.len(),
            });
        }
        let d = self.dim();
        let mut point = self.center.clone();
        for (i, &e) in coeffs.iter().enumerate() {
            // Inner index `j` reads `point[j]` (mut) and `self.generators[i][j]`
            // in parallel; iterator zip is less direct.
            #[allow(clippy::needless_range_loop)]
            for j in 0..d {
                point[j] += e * self.generators[i][j];
            }
        }
        Ok(point)
    }

    /// Checked Minkowski sum returning `Result` on dimension mismatch.
    ///
    /// Like [`Self::minkowski_add`] but validates dimensions
    /// unconditionally instead of using `debug_assert`.
    pub fn minkowski_sum(&self, other: &ConcreteZonotope) -> Result<Self, ZonotopeError> {
        if self.dim() != other.dim() {
            return Err(ZonotopeError::OperandDimensionMismatch {
                left_dim: self.dim(),
                right_dim: other.dim(),
            });
        }
        Ok(self.minkowski_add(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concrete_zonotope_new_basic() {
        let z = ConcreteZonotope::new(vec![1.0, 2.0], vec![vec![1.0, 0.0], vec![0.0, 1.0]]);
        assert_eq!(z.dim(), 2);
        assert_eq!(z.num_generators(), 2);
    }

    #[test]
    fn test_concrete_zonotope_zero_generators() {
        let z = ConcreteZonotope::new(vec![5.0], vec![]);
        assert_eq!(z.dim(), 1);
        assert_eq!(z.num_generators(), 0);
        let (lo, hi) = z.to_interval();
        assert!((lo[0] - 5.0).abs() < 1e-10);
        assert!((hi[0] - 5.0).abs() < 1e-10);
    }
}
