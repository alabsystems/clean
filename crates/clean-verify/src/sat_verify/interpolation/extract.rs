// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! High-level interpolant extraction from resolution proof DAGs.
//!
//! [`InterpolantExtractor`] wraps the low-level DAG walk from [`super::mcmillan`]
//! and [`super::reverse`] with a builder-style API that:
//!
//! - Tracks the A/B partition for every input clause
//! - Classifies variables as A-local, B-local, or shared
//! - Supports multiple extraction algorithms (McMillan, Pudlak, symmetric)
//! - Returns a structured [`ExtractionResult`] with diagnostics
//!
//! ## Usage
//!
//! ```text
//! let result = InterpolantExtractor::new()
//!     .add_a_clause(vec![1, 2])
//!     .add_b_clause(vec![-2, 3])
//!     .add_resolution(0, 1, 2)  // resolve on variable 2
//!     .extract(ExtractionAlgorithm::McMillan)?;
//! assert!(result.shared_vars.contains(&2));
//! ```
//!
//! ## References
//!
//! - McMillan (2003): "Interpolation and SAT-Based Model Checking", CAV 2003.
//! - Pudlak (1997): "Lower bounds on the size of interpolants"

use super::mcmillan::{
    extract_mcmillan_interpolant, verify_shared_variable_property, Partition, ResolutionDag,
    VarClass,
};
use super::reverse::pudlak_interpolation;
use super::PropFormula;
use std::collections::HashSet;
use thiserror::Error;

/// Errors during interpolant extraction.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExtractionError {
    /// The proof DAG contains no nodes.
    #[error("empty proof DAG: no clauses added")]
    EmptyDag,

    /// A resolution step references a node index that does not exist.
    #[error("resolution step references invalid node index {index}")]
    InvalidNodeIndex { index: usize },

    /// The DAG root is not the empty clause (not a valid refutation).
    #[error("DAG root is not the empty clause; proof is not a refutation")]
    NotARefutation,

    /// The interpolant contains variables outside Vars(A) intersection Vars(B).
    #[error("shared-variable property violated for variables: {0:?}")]
    SharedVariableViolation(Vec<u32>),

    /// Reverse interpolation failed.
    #[error("Pudlak extraction failed: {0}")]
    PudlakFailed(#[from] super::reverse::ReverseInterpolationError),
}

/// Which extraction algorithm to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExtractionAlgorithm {
    /// McMillan's algorithm: B-leaves map to True.
    McMillan,
    /// Pudlak's algorithm: B-leaves map to conjunction of negated shared literals.
    Pudlak,
    /// Both algorithms; return both results for comparison.
    Both,
}

/// Result of an interpolant extraction.
#[derive(Debug, Clone)]
pub struct ExtractionResult {
    /// The extracted interpolant (McMillan variant when `Both` is requested).
    pub interpolant: PropFormula,
    /// Optional Pudlak interpolant (populated when `Both` is requested).
    pub pudlak_interpolant: Option<PropFormula>,
    /// Variables shared between A and B.
    pub shared_vars: HashSet<u32>,
    /// Variables local to partition A.
    pub a_local_vars: HashSet<u32>,
    /// Variables local to partition B.
    pub b_local_vars: HashSet<u32>,
    /// Number of resolution steps in the DAG.
    pub resolution_step_count: usize,
    /// Number of input clauses in partition A.
    pub a_clause_count: usize,
    /// Number of input clauses in partition B.
    pub b_clause_count: usize,
}

/// Builder for constructing a resolution proof DAG and extracting interpolants.
///
/// Clauses are added via [`Self::add_a_clause`] and [`Self::add_b_clause`],
/// and resolution steps via [`Self::add_resolution`]. Call [`Self::extract`]
/// to run the chosen algorithm.
#[derive(Debug, Clone)]
pub struct InterpolantExtractor {
    dag: ResolutionDag,
    a_count: usize,
    b_count: usize,
    res_count: usize,
}

impl InterpolantExtractor {
    /// Create a new, empty extractor.
    #[must_use]
    pub fn new() -> Self {
        Self {
            dag: ResolutionDag::new(),
            a_count: 0,
            b_count: 0,
            res_count: 0,
        }
    }

    /// Add an input clause belonging to partition A. Returns the node index.
    pub fn add_a_clause(&mut self, clause: Vec<i32>) -> usize {
        self.a_count += 1;
        self.dag.add_input(clause, Partition::A)
    }

    /// Add an input clause belonging to partition B. Returns the node index.
    pub fn add_b_clause(&mut self, clause: Vec<i32>) -> usize {
        self.b_count += 1;
        self.dag.add_input(clause, Partition::B)
    }

    /// Add a resolution step resolving `left` and `right` on `pivot`.
    ///
    /// Both `left` and `right` must be valid node indices from prior
    /// `add_a_clause`, `add_b_clause`, or `add_resolution` calls.
    /// `pivot` is a literal (positive integer for the variable).
    pub fn add_resolution(&mut self, left: usize, right: usize, pivot: i32) -> usize {
        self.res_count += 1;
        self.dag.add_resolve(left, right, pivot)
    }

    /// Access the underlying DAG for inspection.
    #[must_use]
    pub fn dag(&self) -> &ResolutionDag {
        &self.dag
    }

    /// Extract the interpolant using the specified algorithm.
    ///
    /// # Errors
    ///
    /// Returns [`ExtractionError`] if the DAG is empty, structurally invalid,
    /// or the shared-variable property is violated.
    pub fn extract(
        &self,
        algorithm: ExtractionAlgorithm,
    ) -> Result<ExtractionResult, ExtractionError> {
        if self.dag.nodes.is_empty() {
            return Err(ExtractionError::EmptyDag);
        }

        // Validate root is empty clause (refutation).
        if let Some(root_clause) = self.dag.clauses.last() {
            if !root_clause.is_empty() {
                return Err(ExtractionError::NotARefutation);
            }
        }

        // Classify variables.
        let var_classes = self.dag.classify_variables();
        let mut shared_vars = HashSet::new();
        let mut a_local_vars = HashSet::new();
        let mut b_local_vars = HashSet::new();
        for (&var, &class) in &var_classes {
            match class {
                VarClass::Shared => {
                    shared_vars.insert(var);
                }
                VarClass::AOnly => {
                    a_local_vars.insert(var);
                }
                VarClass::BOnly => {
                    b_local_vars.insert(var);
                }
            }
        }

        let (mcmillan_interp, pudlak_interp) = match algorithm {
            ExtractionAlgorithm::McMillan => {
                let interp = extract_mcmillan_interpolant(&self.dag);
                (interp, None)
            }
            ExtractionAlgorithm::Pudlak => {
                let interp = pudlak_interpolation(&self.dag, &Partition::A, &shared_vars)?;
                (interp, None)
            }
            ExtractionAlgorithm::Both => {
                let mcm = extract_mcmillan_interpolant(&self.dag);
                let pud = pudlak_interpolation(&self.dag, &Partition::A, &shared_vars)?;
                (mcm, Some(pud))
            }
        };

        // Verify shared-variable property on the primary interpolant.
        verify_shared_variable_property(&self.dag, &mcmillan_interp)
            .map_err(ExtractionError::SharedVariableViolation)?;

        Ok(ExtractionResult {
            interpolant: mcmillan_interp,
            pudlak_interpolant: pudlak_interp,
            shared_vars,
            a_local_vars,
            b_local_vars,
            resolution_step_count: self.res_count,
            a_clause_count: self.a_count,
            b_clause_count: self.b_count,
        })
    }
}

impl Default for InterpolantExtractor {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function: build a DAG from A-clauses, B-clauses, and resolution
/// steps, then extract with McMillan's algorithm.
///
/// `steps` is a slice of `(left_index, right_index, pivot_literal)` triples.
///
/// # Errors
///
/// Propagates any error from [`InterpolantExtractor::extract`].
pub fn extract_interpolant_from_parts(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    steps: &[(usize, usize, i32)],
) -> Result<ExtractionResult, ExtractionError> {
    let mut ext = InterpolantExtractor::new();
    for clause in a_clauses {
        ext.add_a_clause(clause.clone());
    }
    for clause in b_clauses {
        ext.add_b_clause(clause.clone());
    }
    for &(left, right, pivot) in steps {
        ext.add_resolution(left, right, pivot);
    }
    ext.extract(ExtractionAlgorithm::McMillan)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extractor_empty_dag_returns_error() {
        let ext = InterpolantExtractor::new();
        let result = ext.extract(ExtractionAlgorithm::McMillan);
        assert!(matches!(result, Err(ExtractionError::EmptyDag)));
    }

    #[test]
    fn test_extractor_not_a_refutation() {
        let mut ext = InterpolantExtractor::new();
        ext.add_a_clause(vec![1, 2]);
        ext.add_b_clause(vec![-2, 3]);
        // No resolution step to derive empty clause.
        let result = ext.extract(ExtractionAlgorithm::McMillan);
        assert!(matches!(result, Err(ExtractionError::NotARefutation)));
    }

    #[test]
    fn test_extractor_simple_two_clause() {
        let mut ext = InterpolantExtractor::new();
        let a = ext.add_a_clause(vec![1, 2]);
        let b = ext.add_b_clause(vec![-2, 3]);
        ext.add_resolution(a, b, 2);
        // Root is {1, 3} -- not empty, so this should fail as not-a-refutation.
        let result = ext.extract(ExtractionAlgorithm::McMillan);
        assert!(matches!(result, Err(ExtractionError::NotARefutation)));
    }

    #[test]
    fn test_extractor_valid_refutation() {
        // A = {x}, B = {!x}  -> resolve on x -> empty clause
        let mut ext = InterpolantExtractor::new();
        let a = ext.add_a_clause(vec![1]);
        let b = ext.add_b_clause(vec![-1]);
        ext.add_resolution(a, b, 1);

        let result = ext
            .extract(ExtractionAlgorithm::McMillan)
            .expect("valid refutation should succeed");
        assert!(result.shared_vars.contains(&1));
        assert!(result.a_local_vars.is_empty());
        assert!(result.b_local_vars.is_empty());
        assert_eq!(result.a_clause_count, 1);
        assert_eq!(result.b_clause_count, 1);
        assert_eq!(result.resolution_step_count, 1);
    }

    #[test]
    fn test_extractor_pudlak_algorithm() {
        let mut ext = InterpolantExtractor::new();
        let a = ext.add_a_clause(vec![1]);
        let b = ext.add_b_clause(vec![-1]);
        ext.add_resolution(a, b, 1);

        let result = ext
            .extract(ExtractionAlgorithm::Pudlak)
            .expect("Pudlak extraction should succeed");
        assert!(result.shared_vars.contains(&1));
    }

    #[test]
    fn test_extractor_both_algorithms() {
        let mut ext = InterpolantExtractor::new();
        let a = ext.add_a_clause(vec![1]);
        let b = ext.add_b_clause(vec![-1]);
        ext.add_resolution(a, b, 1);

        let result = ext
            .extract(ExtractionAlgorithm::Both)
            .expect("both-algorithm extraction should succeed");
        assert!(result.pudlak_interpolant.is_some());
    }

    #[test]
    fn test_extractor_multi_step_dag() {
        // A = {x1, x2}, {x1, !x2}
        // B = {!x1, x3}, {!x1, !x3}
        // Resolve A-clauses on x2 -> {x1}
        // Resolve B-clauses on x3 -> {!x1}
        // Resolve {x1} and {!x1} on x1 -> empty
        let mut ext = InterpolantExtractor::new();
        let a0 = ext.add_a_clause(vec![1, 2]);
        let a1 = ext.add_a_clause(vec![1, -2]);
        let b0 = ext.add_b_clause(vec![-1, 3]);
        let b1 = ext.add_b_clause(vec![-1, -3]);
        let r0 = ext.add_resolution(a0, a1, 2); // {x1}
        let r1 = ext.add_resolution(b0, b1, 3); // {!x1}
        ext.add_resolution(r0, r1, 1); // empty

        let result = ext
            .extract(ExtractionAlgorithm::McMillan)
            .expect("multi-step DAG should succeed");

        // x1 is shared, x2 is A-local, x3 is B-local
        assert!(result.shared_vars.contains(&1));
        assert!(result.a_local_vars.contains(&2));
        assert!(result.b_local_vars.contains(&3));

        // The interpolant should only use shared variables
        let interp_vars = result.interpolant.variables();
        for v in &interp_vars {
            assert!(
                result.shared_vars.contains(v),
                "variable {v} in interpolant but not in shared vars"
            );
        }
    }

    #[test]
    fn test_extract_interpolant_from_parts() {
        // Same as test_extractor_valid_refutation but using the convenience function.
        let result = extract_interpolant_from_parts(&[vec![1]], &[vec![-1]], &[(0, 1, 1)])
            .expect("parts extraction should succeed");
        assert!(result.shared_vars.contains(&1));
    }

    #[test]
    fn test_extractor_default_trait() {
        let ext = InterpolantExtractor::default();
        assert!(ext.dag().nodes.is_empty());
    }

    #[test]
    fn test_extraction_result_variable_classification() {
        let mut ext = InterpolantExtractor::new();
        let a0 = ext.add_a_clause(vec![1, 2]);
        let a1 = ext.add_a_clause(vec![1, -2]);
        let b0 = ext.add_b_clause(vec![-1, 3]);
        let b1 = ext.add_b_clause(vec![-1, -3]);
        let r0 = ext.add_resolution(a0, a1, 2);
        let r1 = ext.add_resolution(b0, b1, 3);
        ext.add_resolution(r0, r1, 1);

        let result = ext
            .extract(ExtractionAlgorithm::Both)
            .expect("extraction should succeed");

        // Verify partition sizes
        assert_eq!(result.a_clause_count, 2);
        assert_eq!(result.b_clause_count, 2);
        assert_eq!(result.resolution_step_count, 3);

        // Verify variable classification is a partition
        assert!(result.shared_vars.is_disjoint(&result.a_local_vars));
        assert!(result.shared_vars.is_disjoint(&result.b_local_vars));
        assert!(result.a_local_vars.is_disjoint(&result.b_local_vars));
    }
}
