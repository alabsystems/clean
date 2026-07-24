// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified proof checker trait and implementations.
//!
//! Provides a [`ProofChecker`] trait that gives a uniform interface for
//! verifying proofs across different proof systems: resolution,
//! tree resolution, cutting planes, and polynomial calculus.

use std::fmt;

use super::frontier::polynomial_calculus::{verify_pc_proof, GF2Polynomial, PCStep};
use super::proof_complexity::cutting_planes::CuttingPlanesProof;
use super::proof_complexity::resolution::ResolutionProof;
use super::proof_complexity::tree_resolution::{verify_tree_resolution, TreeResolutionProof};
use crate::sat_verify::cdcl::Clause;

/// Error type for proof checker failures.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofCheckError {
    /// The proof does not derive a contradiction.
    NotRefutation,
    /// A tree resolution proof has an invalid structure.
    TreeResolutionError(String),
    /// Axiom clauses were not provided for tree resolution.
    MissingAxioms,
}

impl fmt::Display for ProofCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofCheckError::NotRefutation => {
                write!(f, "proof does not derive a contradiction")
            }
            ProofCheckError::TreeResolutionError(msg) => {
                write!(f, "tree resolution error: {msg}")
            }
            ProofCheckError::MissingAxioms => {
                write!(f, "axiom clauses required but not provided")
            }
        }
    }
}

impl std::error::Error for ProofCheckError {}

/// A unified trait for proof checkers across different proof systems.
///
/// Every proof system can be checked for validity and has a measurable
/// size (number of proof steps/nodes).
pub trait ProofChecker {
    /// The error type returned on check failure.
    type Error;

    /// Verify that the proof is a valid refutation.
    ///
    /// Returns `Ok(())` if the proof derives a contradiction from
    /// the input axioms. Returns `Err(...)` describing the failure.
    fn check(&self) -> Result<(), Self::Error>;

    /// The size of the proof (number of steps, nodes, or lines).
    fn proof_size(&self) -> usize;
}

// ---------------------------------------------------------------------------
// Implementation for ResolutionProof
// ---------------------------------------------------------------------------

impl ProofChecker for ResolutionProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), ProofCheckError> {
        if self.verify() {
            Ok(())
        } else {
            Err(ProofCheckError::NotRefutation)
        }
    }

    fn proof_size(&self) -> usize {
        self.len()
    }
}

// ---------------------------------------------------------------------------
// Implementation for CuttingPlanesProof
// ---------------------------------------------------------------------------

impl ProofChecker for CuttingPlanesProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), ProofCheckError> {
        if self.verify() {
            Ok(())
        } else {
            Err(ProofCheckError::NotRefutation)
        }
    }

    fn proof_size(&self) -> usize {
        self.len()
    }
}

// ---------------------------------------------------------------------------
// Wrapper for TreeResolutionProof (needs axioms for verification)
// ---------------------------------------------------------------------------

/// A tree resolution proof bundled with its axiom clauses, so it can
/// implement [`ProofChecker`] without external context.
#[derive(Debug, Clone)]
pub struct CheckableTreeProof {
    /// The tree resolution proof.
    pub proof: TreeResolutionProof,
    /// The input formula (axiom clauses).
    pub axioms: Vec<Clause>,
}

impl ProofChecker for CheckableTreeProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), ProofCheckError> {
        verify_tree_resolution(&self.proof, &self.axioms)
            .map_err(ProofCheckError::TreeResolutionError)
    }

    fn proof_size(&self) -> usize {
        self.proof.root.size()
    }
}

// ---------------------------------------------------------------------------
// Wrapper for Polynomial Calculus proof (needs axioms and steps)
// ---------------------------------------------------------------------------

/// A polynomial calculus proof bundled with its axioms and steps, so it
/// can implement [`ProofChecker`].
#[derive(Debug, Clone)]
pub struct CheckablePCProof {
    /// Axiom polynomials (from clause encoding).
    pub axioms: Vec<GF2Polynomial>,
    /// Proof steps.
    pub steps: Vec<PCStep>,
}

impl ProofChecker for CheckablePCProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), ProofCheckError> {
        if verify_pc_proof(&self.axioms, &self.steps) {
            Ok(())
        } else {
            Err(ProofCheckError::NotRefutation)
        }
    }

    fn proof_size(&self) -> usize {
        self.steps.len()
    }
}

// ---------------------------------------------------------------------------
// Wrapper for Gf2-based Polynomial Calculus proof (newer, enhanced system)
// ---------------------------------------------------------------------------

/// A GF(2) Polynomial Calculus proof bundled with its clauses, so it can
/// implement [`ProofChecker`] using the enhanced [`gf2_algebra`] system.
///
/// This is the preferred wrapper for new code. It uses `Gf2Poly` (sparse
/// multilinear representation with `u32` variable indices) and provides
/// soundness verification via [`pc_soundness_gf2`].
///
/// [`gf2_algebra`]: super::frontier::gf2_algebra
/// [`pc_soundness_gf2`]: super::frontier::gf2_algebra::pc_soundness_gf2
#[derive(Debug, Clone)]
pub struct CheckableGf2PcProof {
    /// The input clauses in DIMACS format.
    pub clauses: Vec<Vec<i32>>,
    /// The proof steps.
    pub steps: Vec<super::frontier::gf2_algebra::PcStepTracked>,
}

impl ProofChecker for CheckableGf2PcProof {
    type Error = ProofCheckError;

    fn check(&self) -> Result<(), ProofCheckError> {
        let proof = super::frontier::gf2_algebra::PcProof::build(&self.clauses, self.steps.clone())
            .map_err(|e| ProofCheckError::TreeResolutionError(e.to_string()))?;

        super::frontier::gf2_algebra::pc_soundness_gf2(&self.clauses, &proof)
            .map_err(|e| ProofCheckError::TreeResolutionError(e.to_string()))
    }

    fn proof_size(&self) -> usize {
        self.steps.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::proof_complexity::cutting_planes::CpInequality;
    use crate::sat_verify::proof_complexity::tree_resolution::TreeNode;

    // ---- ResolutionProof ----

    #[test]
    fn test_resolution_proof_checker_valid() {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");
        assert!(proof.check().is_ok());
        assert_eq!(proof.proof_size(), 3);
    }

    #[test]
    fn test_resolution_proof_checker_not_refutation() {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1, 2]);
        assert!(proof.check().is_err());
    }

    // ---- CuttingPlanesProof ----

    #[test]
    fn test_cp_proof_checker_valid() {
        let mut proof = CuttingPlanesProof::new();
        let a = proof.add_input(CpInequality::new(vec![1], 1));
        let b = proof.add_input(CpInequality::new(vec![-1], 0));
        proof.add(a, b).expect("add");
        assert!(proof.check().is_ok());
        assert_eq!(proof.proof_size(), 3);
    }

    #[test]
    fn test_cp_proof_checker_not_refutation() {
        let mut proof = CuttingPlanesProof::new();
        proof.add_input(CpInequality::new(vec![1], 1));
        assert!(proof.check().is_err());
    }

    // ---- TreeResolutionProof ----

    #[test]
    fn test_tree_proof_checker_valid() {
        let axioms = vec![vec![1], vec![-1]];
        let proof = TreeResolutionProof {
            root: TreeNode::Resolve {
                left: Box::new(TreeNode::Axiom(vec![1])),
                right: Box::new(TreeNode::Axiom(vec![-1])),
                pivot: 1,
                result: vec![],
            },
        };
        let checkable = CheckableTreeProof { proof, axioms };
        assert!(checkable.check().is_ok());
        assert_eq!(checkable.proof_size(), 3);
    }

    #[test]
    fn test_tree_proof_checker_bad_axiom() {
        let axioms = vec![vec![1]];
        let proof = TreeResolutionProof {
            root: TreeNode::Axiom(vec![99]),
        };
        let checkable = CheckableTreeProof { proof, axioms };
        assert!(checkable.check().is_err());
    }

    // ---- PCProof ----

    #[test]
    fn test_pc_proof_checker_valid() {
        use crate::sat_verify::frontier::polynomial_calculus::clause_to_polynomial;

        // (x1) AND (-x1) => derive 1 (contradiction)
        let axioms = vec![clause_to_polynomial(&[1]), clause_to_polynomial(&[-1])];
        // x1 * (1+x1) = x1 + x1^2 = x1 + x1 = 0 in GF(2)
        // We need: add axiom0 + axiom1 = (1-x0) + x0 = 1
        let steps = vec![PCStep::Axiom(0), PCStep::Axiom(1), PCStep::Add(0, 1)];
        let checkable = CheckablePCProof { axioms, steps };
        assert!(checkable.check().is_ok());
        assert_eq!(checkable.proof_size(), 3);
    }

    #[test]
    fn test_pc_proof_checker_not_refutation() {
        let axioms = vec![GF2Polynomial::zero()];
        let steps = vec![PCStep::Axiom(0)];
        let checkable = CheckablePCProof { axioms, steps };
        assert!(checkable.check().is_err());
    }
}
