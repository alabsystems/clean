// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interactive Polynomial Calculus proof system builder.
//!
//! Provides [`PcProofSystem`], a stateful builder for constructing PC
//! proofs over GF(2) step by step. Unlike [`super::gf2_algebra::PcProof`]
//! which takes a complete list of steps, the proof system allows
//! interactive derivation with immediate feedback.
//!
//! ## Usage
//!
//! ```text
//! let mut pc = PcProofSystem::new(clauses);
//! let a0 = pc.axiom_download(0)?;    // introduce clause 0
//! let a1 = pc.axiom_download(1)?;    // introduce clause 1
//! let sum = pc.add(a0, a1)?;         // add the two
//! assert!(pc.is_contradiction(sum));  // check if we derived 1
//! let proof = pc.finalize()?;        // extract verified proof
//! ```
//!
//! ## References
//!
//! - Clegg, Edmonds, Impagliazzo (1996). Using the Groebner basis
//!   algorithm to find proofs of unsatisfiability. STOC'96.

use std::collections::BTreeSet;

use super::gf2_algebra::{Gf2Poly, PcError, PcProof, PcStepTracked};

use thiserror::Error;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors from the interactive proof system.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum ProofSystemError {
    /// Referenced a derived polynomial that does not exist.
    #[error("line {0} does not exist (only {1} lines derived so far)")]
    InvalidLineRef(usize, usize),

    /// Referenced a clause that does not exist.
    #[error("clause {0} does not exist (only {1} clauses)")]
    InvalidClauseRef(usize, usize),

    /// Attempted to weaken with the constant monomial (unsound).
    #[error("cannot weaken with constant monomial 1 (degree must be >= 1)")]
    WeakenConstantMonomial,

    /// The proof does not end with a contradiction.
    #[error("proof does not derive contradiction: last polynomial is not constant 1")]
    NotContradiction,

    /// The proof has no derivation steps.
    #[error("proof system has no derived polynomials")]
    EmptyDerivation,

    /// Error from the underlying proof builder.
    #[error("underlying proof error: {0}")]
    PcError(#[from] PcError),
}

// ---------------------------------------------------------------------------
// PcProofSystem
// ---------------------------------------------------------------------------

/// Interactive Polynomial Calculus proof system over GF(2).
///
/// Manages a derivation sequence where each step immediately computes
/// the resulting polynomial. Provides feedback about the current state
/// of the derivation, enabling proof search.
#[derive(Debug, Clone)]
pub struct PcProofSystem {
    /// The clause polynomials (axiom pool).
    clause_polys: Vec<Gf2Poly>,
    /// The original clauses in DIMACS format.
    clauses: Vec<Vec<i32>>,
    /// Derived polynomials, one per step.
    derived: Vec<Gf2Poly>,
    /// The proof steps corresponding to each derived polynomial.
    steps: Vec<PcStepTracked>,
    /// Maximum degree seen so far.
    max_degree: usize,
}

impl PcProofSystem {
    /// Create a new proof system from DIMACS clauses.
    #[must_use]
    pub fn new(clauses: Vec<Vec<i32>>) -> Self {
        let clause_polys: Vec<Gf2Poly> = clauses.iter().map(|c| Gf2Poly::from_clause(c)).collect();
        Self {
            clause_polys,
            clauses,
            derived: Vec::new(),
            steps: Vec::new(),
            max_degree: 0,
        }
    }

    /// Number of derived polynomials so far.
    #[must_use]
    pub fn num_derived(&self) -> usize {
        self.derived.len()
    }

    /// Number of clauses in the axiom pool.
    #[must_use]
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Maximum degree across all derived polynomials.
    #[must_use]
    pub fn max_degree(&self) -> usize {
        self.max_degree
    }

    /// Get a reference to a derived polynomial by line index.
    #[must_use]
    pub fn get_derived(&self, line: usize) -> Option<&Gf2Poly> {
        self.derived.get(line)
    }

    /// Check if a derived polynomial is the contradiction (constant 1).
    #[must_use]
    pub fn is_contradiction(&self, line: usize) -> bool {
        self.derived.get(line).is_some_and(Gf2Poly::is_one)
    }

    /// Check if any derived polynomial is the contradiction.
    #[must_use]
    pub fn has_contradiction(&self) -> bool {
        self.derived.iter().any(Gf2Poly::is_one)
    }

    // -- Derivation rules ---------------------------------------------------

    /// Axiom download: introduce a clause polynomial.
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::InvalidClauseRef` if `clause_idx` is
    /// out of range.
    pub fn axiom_download(&mut self, clause_idx: usize) -> Result<usize, ProofSystemError> {
        if clause_idx >= self.clause_polys.len() {
            return Err(ProofSystemError::InvalidClauseRef(
                clause_idx,
                self.clause_polys.len(),
            ));
        }

        let poly = self.clause_polys[clause_idx].clone();
        self.push_derived(poly, PcStepTracked::ClauseAxiom(clause_idx))
    }

    /// Boolean axiom: derive x_i^2 - x_i = 0.
    ///
    /// Always derives the zero polynomial (multilinear representation
    /// enforces x^2 = x by construction).
    pub fn boolean_axiom(&mut self, var: u32) -> Result<usize, ProofSystemError> {
        let poly = Gf2Poly::boolean_axiom(var);
        self.push_derived(poly, PcStepTracked::BooleanAxiom(var))
    }

    /// Addition: derive p_i + p_j (XOR in GF(2)).
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::InvalidLineRef` if either index is
    /// out of range.
    pub fn add(&mut self, i: usize, j: usize) -> Result<usize, ProofSystemError> {
        self.check_line(i)?;
        self.check_line(j)?;
        let poly = self.derived[i].add(&self.derived[j]);
        self.push_derived(poly, PcStepTracked::Add(i, j))
    }

    /// Multiply by a variable: derive p_i * x_var.
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::InvalidLineRef` if `i` is out of range.
    pub fn mul_var(&mut self, i: usize, var: u32) -> Result<usize, ProofSystemError> {
        self.check_line(i)?;
        let poly = self.derived[i].mul_var(var);
        self.push_derived(poly, PcStepTracked::MulVar(i, var))
    }

    /// General polynomial multiplication: derive p_i * p_j.
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::InvalidLineRef` if either index is
    /// out of range.
    pub fn mul_poly(&mut self, i: usize, j: usize) -> Result<usize, ProofSystemError> {
        self.check_line(i)?;
        self.check_line(j)?;
        let poly = self.derived[i].mul(&self.derived[j]);
        self.push_derived(poly, PcStepTracked::MulPoly(i, j))
    }

    /// Weakening: derive p_i + monomial (add an arbitrary monomial).
    ///
    /// The monomial must have degree >= 1 (non-constant). Adding the
    /// constant monomial 1 is unsound and rejected.
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::InvalidLineRef` if `i` is out of range.
    /// Returns `ProofSystemError::WeakenConstantMonomial` if `mono_vars`
    /// is empty.
    pub fn weaken(
        &mut self,
        i: usize,
        mono_vars: BTreeSet<u32>,
    ) -> Result<usize, ProofSystemError> {
        self.check_line(i)?;
        if mono_vars.is_empty() {
            return Err(ProofSystemError::WeakenConstantMonomial);
        }
        let mono = Gf2Poly::monomial(&mono_vars.iter().copied().collect::<Vec<_>>());
        let poly = self.derived[i].add(&mono);
        self.push_derived(poly, PcStepTracked::Weaken(i, mono_vars))
    }

    // -- Finalization -------------------------------------------------------

    /// Finalize the proof, verifying it derives a contradiction.
    ///
    /// Consumes the proof system and returns a verified [`PcProof`].
    ///
    /// # Errors
    ///
    /// Returns `ProofSystemError::EmptyDerivation` if no steps were taken.
    /// Returns `ProofSystemError::NotContradiction` if the last derived
    /// polynomial is not the constant 1.
    pub fn finalize(self) -> Result<PcProof, ProofSystemError> {
        if self.derived.is_empty() {
            return Err(ProofSystemError::EmptyDerivation);
        }

        let last = self.derived.last().expect("checked non-empty");
        if !last.is_one() {
            return Err(ProofSystemError::NotContradiction);
        }

        let proof = PcProof::build(&self.clauses, self.steps)?;
        Ok(proof)
    }

    /// Extract the proof steps and derived polynomials without verification.
    ///
    /// Useful for incomplete proofs that will be continued later.
    #[must_use]
    pub fn into_parts(self) -> (Vec<PcStepTracked>, Vec<Gf2Poly>, usize) {
        (self.steps, self.derived, self.max_degree)
    }

    /// Get a snapshot of the current derivation state.
    #[must_use]
    pub fn summary(&self) -> ProofSummary {
        ProofSummary {
            num_steps: self.steps.len(),
            num_axiom_downloads: self
                .steps
                .iter()
                .filter(|s| matches!(s, PcStepTracked::ClauseAxiom(_)))
                .count(),
            num_additions: self
                .steps
                .iter()
                .filter(|s| matches!(s, PcStepTracked::Add(_, _)))
                .count(),
            num_multiplications: self
                .steps
                .iter()
                .filter(|s| {
                    matches!(
                        s,
                        PcStepTracked::MulVar(_, _) | PcStepTracked::MulPoly(_, _)
                    )
                })
                .count(),
            num_weakens: self
                .steps
                .iter()
                .filter(|s| matches!(s, PcStepTracked::Weaken(_, _)))
                .count(),
            num_boolean_axioms: self
                .steps
                .iter()
                .filter(|s| matches!(s, PcStepTracked::BooleanAxiom(_)))
                .count(),
            max_degree: self.max_degree,
            has_contradiction: self.has_contradiction(),
            last_poly_is_one: self.derived.last().is_some_and(Gf2Poly::is_one),
        }
    }

    // -- Internal helpers ---------------------------------------------------

    fn check_line(&self, idx: usize) -> Result<(), ProofSystemError> {
        if idx >= self.derived.len() {
            Err(ProofSystemError::InvalidLineRef(idx, self.derived.len()))
        } else {
            Ok(())
        }
    }

    fn push_derived(
        &mut self,
        poly: Gf2Poly,
        step: PcStepTracked,
    ) -> Result<usize, ProofSystemError> {
        let d = poly.degree();
        if d > self.max_degree {
            self.max_degree = d;
        }
        let idx = self.derived.len();
        self.derived.push(poly);
        self.steps.push(step);
        Ok(idx)
    }
}

/// Summary of the current proof state.
#[derive(Debug, Clone)]
pub struct ProofSummary {
    /// Total number of derivation steps.
    pub num_steps: usize,
    /// Number of axiom download steps.
    pub num_axiom_downloads: usize,
    /// Number of addition steps.
    pub num_additions: usize,
    /// Number of multiplication steps (var + poly).
    pub num_multiplications: usize,
    /// Number of weakening steps.
    pub num_weakens: usize,
    /// Number of boolean axiom steps.
    pub num_boolean_axioms: usize,
    /// Maximum polynomial degree encountered.
    pub max_degree: usize,
    /// Whether any derived polynomial is the constant 1.
    pub has_contradiction: bool,
    /// Whether the last derived polynomial is the constant 1.
    pub last_poly_is_one: bool,
}
