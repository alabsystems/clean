// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified proof system infrastructure for proof-complexity formalization.
//!
//! Provides [`ProofSystemKind`], [`ProofStep`], [`ProofCertificate`], and
//! [`CertificateBuilder`] as the shared types for all proof system checkers
//! (DRAT, LRAT, resolution, extended resolution, cutting planes, etc.).
//!
//! ## Design
//!
//! The [`ProofStep`] trait is the verification interface: each proof system
//! implements it with its own step type. The [`ProofCertificate`] captures
//! the result of verification together with provenance (input hash, timing,
//! proof system kind) for auditable proof artifacts.
//!
//! ## References
//!
//! - Cook & Reckhow (1979): The relative efficiency of propositional proof systems.
//! - Biere et al. (2021): Handbook of Satisfiability, Ch. 13.

use std::fmt;
use std::time::{Duration, Instant};

use super::cnf_core::ClauseDb;

/// Classification of proof systems in the Cook-Reckhow hierarchy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ProofSystemKind {
    /// Standard resolution (Davis-Putnam).
    Resolution,
    /// Extended resolution (Tseitin extension variables).
    ExtendedResolution,
    /// Reverse unit propagation (DRAT/LRAT foundation).
    ReverseUnitPropagation,
    /// Cutting planes (integer linear programming).
    CuttingPlanes,
    /// Polynomial calculus (Nullstellensatz over GF(2)).
    PolynomialCalculus,
    /// Pseudo-Boolean proof system (generalized resolution).
    PseudoBoolean,
    /// Frege / Extended Frege systems.
    Frege,
}

impl fmt::Display for ProofSystemKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Resolution => write!(f, "Resolution"),
            Self::ExtendedResolution => write!(f, "Extended Resolution"),
            Self::ReverseUnitPropagation => write!(f, "RUP (DRAT/LRAT)"),
            Self::CuttingPlanes => write!(f, "Cutting Planes"),
            Self::PolynomialCalculus => write!(f, "Polynomial Calculus"),
            Self::PseudoBoolean => write!(f, "Pseudo-Boolean"),
            Self::Frege => write!(f, "Frege"),
        }
    }
}

/// Error types for proof step verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofError {
    /// A referenced clause was not found in the database.
    MissingClause { clause_id: u32 },
    /// The proof step does not derive the claimed clause.
    InvalidDerivation { reason: String },
    /// The proof does not end in a contradiction.
    NotRefutation,
    /// An axiom clause is not present in the input formula.
    InvalidAxiom { reason: String },
    /// A proof step references an invalid variable or literal.
    InvalidLiteral { reason: String },
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingClause { clause_id } => {
                write!(f, "missing clause with id {clause_id}")
            }
            Self::InvalidDerivation { reason } => {
                write!(f, "invalid derivation: {reason}")
            }
            Self::NotRefutation => write!(f, "proof does not derive a contradiction"),
            Self::InvalidAxiom { reason } => {
                write!(f, "invalid axiom: {reason}")
            }
            Self::InvalidLiteral { reason } => {
                write!(f, "invalid literal: {reason}")
            }
        }
    }
}

impl std::error::Error for ProofError {}

/// A single proof step that can be verified against a clause database.
///
/// Each proof system provides its own step type implementing this trait.
/// The verification checks that the step is sound with respect to the
/// current clause database state.
pub trait ProofStep {
    /// Verify this step against the clause database.
    ///
    /// Returns `Ok(())` if the step is sound, or an error describing the
    /// failure.
    fn verify(&self, db: &ClauseDb) -> Result<(), ProofError>;

    /// A human-readable name for the type of this step.
    fn step_name(&self) -> &'static str;
}

/// Verification outcome stored in a [`ProofCertificate`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationResult {
    /// All steps verified and the proof is a valid refutation.
    ValidRefutation,
    /// All steps verified but the proof does not derive a contradiction.
    ValidNonRefutation,
    /// Verification failed at a specific step.
    Failed { step_index: usize },
}

impl fmt::Display for VerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValidRefutation => write!(f, "valid refutation"),
            Self::ValidNonRefutation => write!(f, "valid (non-refutation)"),
            Self::Failed { step_index } => {
                write!(f, "failed at step {step_index}")
            }
        }
    }
}

/// An auditable proof certificate capturing the verification result,
/// provenance, and timing information.
#[derive(Debug, Clone)]
pub struct ProofCertificate {
    /// The proof system used.
    pub proof_system: ProofSystemKind,
    /// Blake3 hash of the input formula (DIMACS encoding).
    pub input_hash: [u8; 32],
    /// Total number of proof steps.
    pub step_count: usize,
    /// Verification result.
    pub result: VerificationResult,
    /// Wall-clock time for verification.
    pub verification_time: Duration,
    /// Number of original clauses in the input formula.
    pub original_clauses: usize,
    /// Number of derived (learned) clauses.
    pub derived_clauses: usize,
}

impl ProofCertificate {
    /// Whether this certificate records a valid refutation.
    #[must_use]
    pub fn is_valid_refutation(&self) -> bool {
        self.result == VerificationResult::ValidRefutation
    }

    /// The input hash as a hex string.
    #[must_use]
    pub fn input_hash_hex(&self) -> String {
        self.input_hash.iter().map(|b| format!("{b:02x}")).collect()
    }
}

impl fmt::Display for ProofCertificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Proof Certificate")?;
        writeln!(f, "  System:          {}", self.proof_system)?;
        writeln!(f, "  Input hash:      {}", self.input_hash_hex())?;
        writeln!(f, "  Steps:           {}", self.step_count)?;
        writeln!(f, "  Original cls:    {}", self.original_clauses)?;
        writeln!(f, "  Derived cls:     {}", self.derived_clauses)?;
        writeln!(f, "  Result:          {}", self.result)?;
        writeln!(f, "  Time:            {:?}", self.verification_time)?;
        Ok(())
    }
}

/// Incremental builder for constructing [`ProofCertificate`]s.
#[derive(Debug)]
#[must_use]
pub struct CertificateBuilder {
    proof_system: ProofSystemKind,
    input_hash: [u8; 32],
    step_count: usize,
    original_clauses: usize,
    derived_clauses: usize,
    start_time: Option<Instant>,
    result: Option<VerificationResult>,
}

impl CertificateBuilder {
    /// Create a new builder for the given proof system.
    pub fn new(proof_system: ProofSystemKind) -> Self {
        Self {
            proof_system,
            input_hash: [0u8; 32],
            step_count: 0,
            original_clauses: 0,
            derived_clauses: 0,
            start_time: None,
            result: None,
        }
    }

    /// Set the input formula hash.
    pub fn input_hash(mut self, hash: [u8; 32]) -> Self {
        self.input_hash = hash;
        self
    }

    /// Set the number of original clauses.
    pub fn original_clauses(mut self, count: usize) -> Self {
        self.original_clauses = count;
        self
    }

    /// Start the verification timer.
    pub fn start_timer(&mut self) {
        self.start_time = Some(Instant::now());
    }

    /// Record a verified step.
    pub fn record_step(&mut self) {
        self.step_count += 1;
    }

    /// Record a derived clause.
    pub fn record_derived(&mut self) {
        self.derived_clauses += 1;
    }

    /// Set the verification result.
    pub fn set_result(&mut self, result: VerificationResult) {
        self.result = Some(result);
    }

    /// Build the certificate. Panics if no result was set.
    pub fn build(self) -> ProofCertificate {
        let elapsed = self
            .start_time
            .map(|t| t.elapsed())
            .unwrap_or(Duration::ZERO);
        ProofCertificate {
            proof_system: self.proof_system,
            input_hash: self.input_hash,
            step_count: self.step_count,
            result: self
                .result
                .expect("invariant: result must be set before build"),
            verification_time: elapsed,
            original_clauses: self.original_clauses,
            derived_clauses: self.derived_clauses,
        }
    }
}

// ---------------------------------------------------------------------------
// Resolution step — concrete implementation of ProofStep
// ---------------------------------------------------------------------------

/// A resolution proof step: resolve two parent clauses on a pivot variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionStep {
    /// First parent clause ID.
    pub left: super::cnf_core::ClauseId,
    /// Second parent clause ID.
    pub right: super::cnf_core::ClauseId,
    /// Pivot variable (0-indexed) to resolve on.
    pub pivot_var: u32,
}

impl ProofStep for ResolutionStep {
    fn verify(&self, db: &ClauseDb) -> Result<(), ProofError> {
        let left_lits = db.get_clause(self.left).ok_or(ProofError::MissingClause {
            clause_id: self.left.0,
        })?;
        let right_lits = db.get_clause(self.right).ok_or(ProofError::MissingClause {
            clause_id: self.right.0,
        })?;

        // Check that pivot appears positive in one clause and negative in
        // the other.
        let pivot_pos = super::cnf_core::CnfLiteral::positive(self.pivot_var);
        let pivot_neg = super::cnf_core::CnfLiteral::negative(self.pivot_var);

        let left_has_pos = left_lits.contains(&pivot_pos);
        let left_has_neg = left_lits.contains(&pivot_neg);
        let right_has_pos = right_lits.contains(&pivot_pos);
        let right_has_neg = right_lits.contains(&pivot_neg);

        let valid = (left_has_pos && right_has_neg) || (left_has_neg && right_has_pos);
        if !valid {
            return Err(ProofError::InvalidDerivation {
                reason: format!(
                    "pivot variable {} not in complementary polarities across clauses {} and {}",
                    self.pivot_var, self.left, self.right
                ),
            });
        }

        Ok(())
    }

    fn step_name(&self) -> &'static str {
        "resolution"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_verify::cnf_core::{ClauseDb, ClauseId, CnfLiteral};

    // ---- ProofSystemKind ----

    #[test]
    fn test_proof_system_kind_display() {
        assert_eq!(ProofSystemKind::Resolution.to_string(), "Resolution");
        assert_eq!(
            ProofSystemKind::ExtendedResolution.to_string(),
            "Extended Resolution"
        );
        assert_eq!(
            ProofSystemKind::ReverseUnitPropagation.to_string(),
            "RUP (DRAT/LRAT)"
        );
        assert_eq!(ProofSystemKind::CuttingPlanes.to_string(), "Cutting Planes");
        assert_eq!(
            ProofSystemKind::PolynomialCalculus.to_string(),
            "Polynomial Calculus"
        );
        assert_eq!(ProofSystemKind::PseudoBoolean.to_string(), "Pseudo-Boolean");
        assert_eq!(ProofSystemKind::Frege.to_string(), "Frege");
    }

    // ---- ProofError ----

    #[test]
    fn test_proof_error_display() {
        let err = ProofError::MissingClause { clause_id: 42 };
        assert_eq!(err.to_string(), "missing clause with id 42");

        let err = ProofError::NotRefutation;
        assert_eq!(err.to_string(), "proof does not derive a contradiction");
    }

    // ---- VerificationResult ----

    #[test]
    fn test_verification_result_display() {
        assert_eq!(
            VerificationResult::ValidRefutation.to_string(),
            "valid refutation"
        );
        assert_eq!(
            VerificationResult::Failed { step_index: 5 }.to_string(),
            "failed at step 5"
        );
    }

    // ---- CertificateBuilder ----

    #[test]
    fn test_certificate_builder_basic() {
        let mut builder = CertificateBuilder::new(ProofSystemKind::Resolution)
            .input_hash([0xABu8; 32])
            .original_clauses(10);
        builder.start_timer();
        builder.record_step();
        builder.record_step();
        builder.record_derived();
        builder.set_result(VerificationResult::ValidRefutation);
        let cert = builder.build();

        assert_eq!(cert.proof_system, ProofSystemKind::Resolution);
        assert_eq!(cert.input_hash, [0xAB; 32]);
        assert_eq!(cert.step_count, 2);
        assert_eq!(cert.original_clauses, 10);
        assert_eq!(cert.derived_clauses, 1);
        assert!(cert.is_valid_refutation());
    }

    #[test]
    fn test_certificate_input_hash_hex() {
        let cert = CertificateBuilder::new(ProofSystemKind::Resolution)
            .input_hash([0u8; 32])
            .original_clauses(0);
        let mut b = cert;
        b.set_result(VerificationResult::ValidRefutation);
        let c = b.build();
        assert_eq!(c.input_hash_hex().len(), 64);
        assert!(c.input_hash_hex().chars().all(|ch| ch == '0'));
    }

    // ---- ResolutionStep (ProofStep impl) ----

    #[test]
    fn test_resolution_step_verify_valid() {
        let mut db = ClauseDb::new();
        // clause 0: {x0, x1}
        let left = db.add_clause(&[CnfLiteral::positive(0), CnfLiteral::positive(1)]);
        // clause 1: {~x0, x2}
        let right = db.add_clause(&[CnfLiteral::negative(0), CnfLiteral::positive(2)]);

        let step = ResolutionStep {
            left,
            right,
            pivot_var: 0,
        };
        step.verify(&db).expect("resolution should be valid");
        assert_eq!(step.step_name(), "resolution");
    }

    #[test]
    fn test_resolution_step_verify_missing_clause() {
        let db = ClauseDb::new();
        let step = ResolutionStep {
            left: ClauseId(0),
            right: ClauseId(1),
            pivot_var: 0,
        };
        let err = step.verify(&db).expect_err("should fail");
        matches!(err, ProofError::MissingClause { .. });
    }

    #[test]
    fn test_resolution_step_verify_invalid_pivot() {
        let mut db = ClauseDb::new();
        let left = db.add_clause(&[CnfLiteral::positive(0)]);
        let right = db.add_clause(&[CnfLiteral::positive(1)]);

        let step = ResolutionStep {
            left,
            right,
            pivot_var: 0,
        };
        let err = step.verify(&db).expect_err("should fail");
        matches!(err, ProofError::InvalidDerivation { .. });
    }
}
