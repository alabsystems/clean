// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bound Propagation Under Edits
//!
//! Formalizes how gamma-crown verified output bounds propagate through
//! edited weights. The key theorem:
//!
//! If gamma-crown proves f(W, x) in [l, u] for all x in S,
//! and ||dW|| <= delta, then:
//!   f(W + dW, x) in [l - L*delta, u + L*delta]
//! where L is the local Lipschitz constant of f with respect to W.
//!
//! This is the mathematical foundation for delta verification:
//! after a weight edit, we can bound the new output range without
//! re-running full CROWN verification.

use super::edit_algebra::RankOneUpdate;
use super::NeuralSurgeryError;

/// A Lipschitz bound for a neural network layer or full network.
///
/// L is the Lipschitz constant: ||f(W1) - f(W2)|| <= L * ||W1 - W2||
/// for all weight matrices W1, W2 in the domain.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LipschitzBound {
    /// The Lipschitz constant L >= 0.
    constant: f64,
}

impl LipschitzBound {
    /// Create a new Lipschitz bound.
    ///
    /// # Panics
    ///
    /// Panics in debug mode if the constant is negative.
    #[must_use]
    pub fn new(constant: f64) -> Self {
        debug_assert!(
            constant >= 0.0,
            "Lipschitz constant must be non-negative, got {constant}"
        );
        Self { constant }
    }

    /// Get the Lipschitz constant.
    #[must_use]
    pub fn constant(&self) -> f64 {
        self.constant
    }

    /// Compose two Lipschitz bounds (for sequential layers).
    ///
    /// If f has Lipschitz constant L1 and g has L2,
    /// then g(f(.)) has Lipschitz constant L1 * L2.
    #[must_use]
    pub fn compose(&self, other: &LipschitzBound) -> LipschitzBound {
        LipschitzBound {
            constant: self.constant * other.constant,
        }
    }
}

/// An output bound interval [lower, upper] verified by gamma-crown.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OutputBound {
    /// Lower bound on network output.
    pub lower: f64,
    /// Upper bound on network output.
    pub upper: f64,
}

impl OutputBound {
    /// Create a new output bound.
    #[must_use]
    pub fn new(lower: f64, upper: f64) -> Self {
        debug_assert!(
            lower <= upper,
            "lower bound must not exceed upper: {lower} > {upper}"
        );
        Self { lower, upper }
    }

    /// Width of the interval.
    #[must_use]
    pub fn width(&self) -> f64 {
        self.upper - self.lower
    }

    /// Check if a value falls within the bound.
    #[must_use]
    pub fn contains(&self, value: f64) -> bool {
        value >= self.lower && value <= self.upper
    }
}

/// Specification of bound propagation theorems.
#[derive(Debug)]
pub struct BoundPropagationSpec {
    _private: (),
}

impl BoundPropagationSpec {
    /// Create a new bound propagation specification.
    #[must_use]
    pub fn new() -> Self {
        Self { _private: () }
    }

    /// **Theorem (Bound Preservation Under Edit):**
    ///
    /// Given:
    /// - Original bounds: f(W, x) in [l, u] for all x in S
    /// - Weight perturbation: ||dW||_F <= delta
    /// - Lipschitz constant L of f w.r.t. W
    ///
    /// Then: f(W + dW, x) in [l - L*delta, u + L*delta] for all x in S.
    ///
    /// Returns the new (widened) output bound.
    #[must_use]
    pub fn propagate_bound(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
        perturbation_norm: f64,
    ) -> OutputBound {
        let slack = lipschitz.constant() * perturbation_norm;
        OutputBound {
            lower: original_bound.lower - slack,
            upper: original_bound.upper + slack,
        }
    }

    /// **Theorem (Monotonicity of Bound Degradation):**
    ///
    /// Larger perturbations produce wider bounds. For delta1 <= delta2:
    ///   width(propagate(bound, L, delta1)) <= width(propagate(bound, L, delta2))
    pub fn verify_monotonicity(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
        delta1: f64,
        delta2: f64,
    ) -> Result<(), NeuralSurgeryError> {
        if delta1 > delta2 {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: format!(
                    "monotonicity requires delta1 <= delta2, got {delta1} > {delta2}"
                ),
            });
        }
        let bound1 = self.propagate_bound(original_bound, lipschitz, delta1);
        let bound2 = self.propagate_bound(original_bound, lipschitz, delta2);
        if bound1.width() > bound2.width() + f64::EPSILON {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: format!(
                    "monotonicity violated: width({delta1})={} > width({delta2})={}",
                    bound1.width(),
                    bound2.width()
                ),
            });
        }
        Ok(())
    }

    /// **Theorem (Zero Perturbation Preserves Bounds):**
    ///
    /// If dW = 0, the propagated bounds equal the original bounds exactly.
    pub fn verify_zero_preserves_bounds(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
    ) -> Result<(), NeuralSurgeryError> {
        let propagated = self.propagate_bound(original_bound, lipschitz, 0.0);
        if (propagated.lower - original_bound.lower).abs() > f64::EPSILON
            || (propagated.upper - original_bound.upper).abs() > f64::EPSILON
        {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "zero perturbation should preserve bounds exactly".to_string(),
            });
        }
        Ok(())
    }

    /// **Theorem (Bound Propagation Through Rank-1 Edit):**
    ///
    /// Specialization of the general theorem to rank-1 updates, using
    /// the factored norm ||dW||_F = ||u|| * ||v||.
    pub fn verify_rank1_bound_propagation(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
        dw: &RankOneUpdate,
    ) -> Result<OutputBound, NeuralSurgeryError> {
        let delta = dw.frobenius_norm();
        let new_bound = self.propagate_bound(original_bound, lipschitz, delta);

        // Verify the bound is at least as wide as the original
        if new_bound.width() < original_bound.width() - f64::EPSILON {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "propagated bound should not be narrower than original".to_string(),
            });
        }

        Ok(new_bound)
    }
}

impl Default for BoundPropagationSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lipschitz_compose() {
        let l1 = LipschitzBound::new(2.0);
        let l2 = LipschitzBound::new(3.0);
        let composed = l1.compose(&l2);
        assert!((composed.constant() - 6.0).abs() < 1e-10);
    }

    #[test]
    fn test_output_bound_basics() {
        let b = OutputBound::new(-1.0, 1.0);
        assert!((b.width() - 2.0).abs() < 1e-10);
        assert!(b.contains(0.0));
        assert!(b.contains(-1.0));
        assert!(b.contains(1.0));
        assert!(!b.contains(1.5));
    }

    #[test]
    fn test_propagate_bound() {
        let spec = BoundPropagationSpec::new();
        let bound = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(2.0);
        let new_bound = spec.propagate_bound(&bound, &lip, 0.5);
        // l - L*delta = -1 - 2*0.5 = -2
        // u + L*delta = 1 + 2*0.5 = 2
        assert!((new_bound.lower - (-2.0)).abs() < 1e-10);
        assert!((new_bound.upper - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_monotonicity() {
        let spec = BoundPropagationSpec::new();
        let bound = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(5.0);
        spec.verify_monotonicity(&bound, &lip, 0.1, 0.5)
            .expect("monotonicity should hold");
        spec.verify_monotonicity(&bound, &lip, 0.0, 1.0)
            .expect("monotonicity from zero should hold");
    }

    #[test]
    fn test_zero_preserves_bounds() {
        let spec = BoundPropagationSpec::new();
        let bound = OutputBound::new(-std::f64::consts::PI, 2.71);
        let lip = LipschitzBound::new(100.0);
        spec.verify_zero_preserves_bounds(&bound, &lip)
            .expect("zero perturbation should preserve bounds");
    }

    #[test]
    fn test_rank1_bound_propagation() {
        let spec = BoundPropagationSpec::new();
        let bound = OutputBound::new(0.0, 1.0);
        let lip = LipschitzBound::new(1.0);
        let dw = RankOneUpdate::new(vec![0.1, 0.2], vec![0.3, 0.4]);
        let new_bound = spec
            .verify_rank1_bound_propagation(&bound, &lip, &dw)
            .expect("rank-1 bound propagation should succeed");
        assert!(new_bound.lower <= bound.lower);
        assert!(new_bound.upper >= bound.upper);
    }

    #[test]
    fn test_monotonicity_violated_ordering() {
        let spec = BoundPropagationSpec::new();
        let bound = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(1.0);
        assert!(
            spec.verify_monotonicity(&bound, &lip, 0.5, 0.1).is_err(),
            "should reject delta1 > delta2"
        );
    }
}
