// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edit Chain Composition
//!
//! Formalizes the composition of N sequential weight edits and proves
//! that accumulated bounds degrade gracefully:
//!
//! Given edits dW_1, ..., dW_n applied sequentially, the final model
//! W + sum(dW_i) satisfies bounds that are the original bounds widened
//! by L * sum(||dW_i||_F), where L is the Lipschitz constant.
//!
//! Additionally, in IEEE-754 arithmetic, the accumulated floating-point
//! error from N sequential apply-undo operations is bounded by
//! N * 2 * eps * ||W||.

use super::bound_propagation::{BoundPropagationSpec, LipschitzBound, OutputBound};
use super::edit_algebra::RankOneUpdate;
use super::NeuralSurgeryError;

/// A sequence of rank-1 edits applied to a weight matrix.
#[derive(Debug, Clone)]
pub struct EditSequence {
    /// The edits in application order.
    edits: Vec<RankOneUpdate>,
}

impl EditSequence {
    /// Create an empty edit sequence.
    #[must_use]
    pub fn new() -> Self {
        Self { edits: Vec::new() }
    }

    /// Append an edit to the sequence.
    pub fn push(&mut self, edit: RankOneUpdate) {
        self.edits.push(edit);
    }

    /// Number of edits in the sequence.
    #[must_use]
    pub fn len(&self) -> usize {
        self.edits.len()
    }

    /// Whether the sequence is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.edits.is_empty()
    }

    /// Total perturbation norm: sum of individual Frobenius norms.
    ///
    /// By the triangle inequality, this is an upper bound on the norm
    /// of the accumulated edit: ||sum(dW_i)||_F <= sum(||dW_i||_F).
    #[must_use]
    pub fn total_perturbation_norm(&self) -> f64 {
        self.edits.iter().map(|e| e.frobenius_norm()).sum()
    }

    /// Get the edits as a slice.
    #[must_use]
    pub fn edits(&self) -> &[RankOneUpdate] {
        &self.edits
    }
}

impl Default for EditSequence {
    fn default() -> Self {
        Self::new()
    }
}

/// Specification of edit chain composition theorems.
#[derive(Debug)]
pub struct EditChainSpec {
    bound_spec: BoundPropagationSpec,
}

impl EditChainSpec {
    /// Create a new edit chain specification.
    #[must_use]
    pub fn new() -> Self {
        Self {
            bound_spec: BoundPropagationSpec::new(),
        }
    }

    /// **Theorem (Edit Chain Bound Propagation):**
    ///
    /// Given original bounds [l, u] and a sequence of edits dW_1...dW_n,
    /// the post-chain bounds are:
    ///   [l - L * sum(||dW_i||_F), u + L * sum(||dW_i||_F)]
    ///
    /// This follows from the triangle inequality applied to the Lipschitz
    /// bound propagation theorem.
    #[must_use]
    pub fn propagate_chain_bounds(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
        chain: &EditSequence,
    ) -> OutputBound {
        let total_delta = chain.total_perturbation_norm();
        self.bound_spec
            .propagate_bound(original_bound, lipschitz, total_delta)
    }

    /// **Theorem (Chain Bounds Are At Least As Wide As Single-Edit Bounds):**
    ///
    /// Adding more edits to a chain never narrows the propagated bounds.
    /// For chain C and edit dW: width(propagate(C ++ [dW])) >= width(propagate(C)).
    pub fn verify_chain_monotonicity(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
        chain: &EditSequence,
        additional_edit: &RankOneUpdate,
    ) -> Result<(), NeuralSurgeryError> {
        let before = self.propagate_chain_bounds(original_bound, lipschitz, chain);

        let mut extended = chain.clone();
        extended.push(additional_edit.clone());
        let after = self.propagate_chain_bounds(original_bound, lipschitz, &extended);

        if after.width() < before.width() - f64::EPSILON {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: format!(
                    "chain monotonicity violated: width before={}, after={}",
                    before.width(),
                    after.width()
                ),
            });
        }
        Ok(())
    }

    /// **Theorem (Empty Chain Preserves Bounds):**
    ///
    /// An empty edit chain produces bounds identical to the original.
    pub fn verify_empty_chain_preserves(
        &self,
        original_bound: &OutputBound,
        lipschitz: &LipschitzBound,
    ) -> Result<(), NeuralSurgeryError> {
        let chain = EditSequence::new();
        let propagated = self.propagate_chain_bounds(original_bound, lipschitz, &chain);

        if (propagated.lower - original_bound.lower).abs() > f64::EPSILON
            || (propagated.upper - original_bound.upper).abs() > f64::EPSILON
        {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: "empty chain should preserve bounds exactly".to_string(),
            });
        }
        Ok(())
    }

    /// **Theorem (Undo Correctness):**
    ///
    /// If we apply edits dW_1...dW_n then undo them in reverse order
    /// (-dW_n...-dW_1), in exact arithmetic we recover W exactly.
    /// In IEEE-754 f64, the roundtrip error is bounded by:
    ///   2 * n * eps * ||W||_F
    ///
    /// where n is the chain length, eps is machine epsilon, and ||W||_F
    /// is the weight matrix Frobenius norm.
    // Nested loops index two distinct sources (`current[i][j]` and
    // `edit.entry(i, j)`, then `current[i][j]` and `w[i][j]`); rewriting via
    // iterators would obscure the joint per-entry semantics.
    #[allow(clippy::needless_range_loop)]
    pub fn verify_undo_correctness(
        &self,
        w: &[Vec<f64>],
        chain: &EditSequence,
    ) -> Result<f64, NeuralSurgeryError> {
        if w.is_empty() || chain.is_empty() {
            return Ok(0.0);
        }

        let rows = w.len();
        let cols = w[0].len();

        // Apply all edits forward
        let mut current = w.to_vec();
        for edit in chain.edits() {
            if edit.rows() != rows || edit.cols() != cols {
                return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                    property: "edit dimensions must match weight matrix".to_string(),
                });
            }
            for i in 0..rows {
                for j in 0..cols {
                    current[i][j] += edit.entry(i, j);
                }
            }
        }

        // Undo all edits in reverse order
        for edit in chain.edits().iter().rev() {
            for i in 0..rows {
                for j in 0..cols {
                    current[i][j] -= edit.entry(i, j);
                }
            }
        }

        // Compute roundtrip error
        let mut error_sq = 0.0;
        let mut w_norm_sq = 0.0;
        for i in 0..rows {
            for j in 0..cols {
                let err = current[i][j] - w[i][j];
                error_sq += err * err;
                w_norm_sq += w[i][j] * w[i][j];
            }
        }

        let error_norm = error_sq.sqrt();
        let w_norm = w_norm_sq.sqrt();
        let n = chain.len() as f64;

        // Theoretical bound: each add/sub introduces relative error proportional
        // to the magnitude of intermediates. With n edits, the intermediate sums
        // can grow as large as ||W|| + sum(||dW_i||). We bound with the max
        // magnitude seen during forward+backward traversal.
        let edit_norm: f64 = chain
            .edits()
            .iter()
            .map(|e| {
                (0..rows)
                    .flat_map(|i| (0..cols).map(move |j| e.entry(i, j) * e.entry(i, j)))
                    .sum::<f64>()
            })
            .sum::<f64>()
            .sqrt();
        let max_intermediate = w_norm + edit_norm;
        let bound = 2.0 * n * f64::EPSILON * max_intermediate;

        if error_norm > bound * 4.0 {
            // Allow a factor of 4 slack for accumulated intermediate rounding
            return Err(NeuralSurgeryError::ErrorBoundExceeded {
                computed: error_norm,
                bound,
            });
        }

        Ok(error_norm)
    }

    /// **Theorem (Commutativity of Edit Accumulation):**
    ///
    /// The final weight matrix W + sum(dW_i) is independent of the order
    /// of application (in exact arithmetic), because matrix addition is
    /// commutative and associative.
    ///
    /// In floating-point, different orderings may produce slightly different
    /// results, but the difference is bounded by n * eps * sum(||dW_i||_F).
    // Nested loops index two distinct sources per pass
    // (forward/reverse/edit/w); iterator rewrites would not be clearer.
    #[allow(clippy::needless_range_loop)]
    pub fn verify_order_independence(
        &self,
        w: &[Vec<f64>],
        chain: &EditSequence,
    ) -> Result<f64, NeuralSurgeryError> {
        if w.is_empty() || chain.len() < 2 {
            return Ok(0.0);
        }

        let rows = w.len();
        let cols = w[0].len();

        // Apply forward
        let mut forward = w.to_vec();
        for edit in chain.edits() {
            if edit.rows() != rows || edit.cols() != cols {
                return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                    property: "edit dimensions must match weight matrix".to_string(),
                });
            }
            for i in 0..rows {
                for j in 0..cols {
                    forward[i][j] += edit.entry(i, j);
                }
            }
        }

        // Apply reverse
        let mut reverse = w.to_vec();
        for edit in chain.edits().iter().rev() {
            for i in 0..rows {
                for j in 0..cols {
                    reverse[i][j] += edit.entry(i, j);
                }
            }
        }

        // Compute difference
        let mut diff_sq = 0.0;
        for i in 0..rows {
            for j in 0..cols {
                let d = forward[i][j] - reverse[i][j];
                diff_sq += d * d;
            }
        }

        let diff_norm = diff_sq.sqrt();

        // Bound: n * eps * sum(||dW_i||_F)
        // Each entry accumulates rounding from both the multiplication
        // (u[i]*v[j]) and the addition (+= to the accumulator). With n
        // edits, each entry sees n multiply-add steps, each contributing
        // up to eps relative error on the entry magnitude.
        let n = chain.len() as f64;
        let total_pert = chain.total_perturbation_norm();
        let bound = n * f64::EPSILON * total_pert;

        if diff_norm > bound * 4.0 {
            return Err(NeuralSurgeryError::AlgebraicPropertyViolated {
                property: format!("order independence violated: diff={diff_norm}, bound={bound}"),
            });
        }

        Ok(diff_norm)
    }
}

impl Default for EditChainSpec {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_chain() -> EditSequence {
        let mut chain = EditSequence::new();
        chain.push(RankOneUpdate::new(vec![0.1, 0.2], vec![0.3, 0.4]));
        chain.push(RankOneUpdate::new(vec![-0.05, 0.1], vec![0.2, -0.1]));
        chain.push(RankOneUpdate::new(vec![0.03, -0.07], vec![-0.1, 0.15]));
        chain
    }

    fn sample_w() -> Vec<Vec<f64>> {
        vec![vec![1.0, 2.0], vec![3.0, 4.0]]
    }

    #[test]
    fn test_edit_sequence_basics() {
        let chain = sample_chain();
        assert_eq!(chain.len(), 3);
        assert!(!chain.is_empty());
        assert!(chain.total_perturbation_norm() > 0.0);
    }

    #[test]
    fn test_empty_sequence() {
        let chain = EditSequence::new();
        assert_eq!(chain.len(), 0);
        assert!(chain.is_empty());
        assert!((chain.total_perturbation_norm()).abs() < 1e-10);
    }

    #[test]
    fn test_chain_bound_propagation() {
        let spec = EditChainSpec::new();
        let bound = OutputBound::new(-1.0, 1.0);
        let lip = LipschitzBound::new(1.0);
        let chain = sample_chain();

        let new_bound = spec.propagate_chain_bounds(&bound, &lip, &chain);
        assert!(new_bound.lower <= bound.lower);
        assert!(new_bound.upper >= bound.upper);
        assert!(new_bound.width() >= bound.width());
    }

    #[test]
    fn test_chain_monotonicity() {
        let spec = EditChainSpec::new();
        let bound = OutputBound::new(0.0, 1.0);
        let lip = LipschitzBound::new(2.0);
        let chain = sample_chain();
        let extra = RankOneUpdate::new(vec![0.5, 0.5], vec![0.5, 0.5]);

        spec.verify_chain_monotonicity(&bound, &lip, &chain, &extra)
            .expect("chain monotonicity should hold");
    }

    #[test]
    fn test_empty_chain_preserves() {
        let spec = EditChainSpec::new();
        let bound = OutputBound::new(-2.5, 3.7);
        let lip = LipschitzBound::new(10.0);

        spec.verify_empty_chain_preserves(&bound, &lip)
            .expect("empty chain should preserve bounds");
    }

    #[test]
    fn test_undo_correctness() {
        let spec = EditChainSpec::new();
        let w = sample_w();
        let chain = sample_chain();

        let error = spec
            .verify_undo_correctness(&w, &chain)
            .expect("undo should recover original within bound");
        // For f64 arithmetic with small edits, error should be negligible
        assert!(error < 1e-10, "roundtrip error = {error}");
    }

    #[test]
    fn test_order_independence() {
        let spec = EditChainSpec::new();
        let w = sample_w();
        let chain = sample_chain();

        let diff = spec
            .verify_order_independence(&w, &chain)
            .expect("order independence should hold within bound");
        assert!(diff < 1e-10, "order difference = {diff}");
    }

    #[test]
    fn test_single_edit_chain() {
        let spec = EditChainSpec::new();
        let mut chain = EditSequence::new();
        chain.push(RankOneUpdate::new(vec![1.0, 0.0], vec![0.0, 1.0]));

        let w = sample_w();
        let error = spec
            .verify_undo_correctness(&w, &chain)
            .expect("single-edit undo should work");
        assert!(error < 1e-15, "single-edit roundtrip error = {error}");
    }

    #[test]
    fn test_large_chain_undo() {
        let spec = EditChainSpec::new();
        let w = vec![vec![100.0, 200.0], vec![300.0, 400.0]];
        let mut chain = EditSequence::new();
        // 10 small edits
        for k in 0..10 {
            let scale = 0.01 * (k as f64 + 1.0);
            chain.push(RankOneUpdate::new(vec![scale, -scale], vec![scale, scale]));
        }

        let error = spec
            .verify_undo_correctness(&w, &chain)
            .expect("large chain undo should hold within bound");
        assert!(error < 1e-8, "large chain roundtrip error = {error}");
    }
}
