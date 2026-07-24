// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Candidate theorem representation for the proof discovery loop.
//!
//! A `CandidateTheorem` packages a theorem statement (type) and optional proof
//! term with the search-space coordinates that produced it.

use crate::family::TheoremFamily;
use clean_kernel::Expr;

/// A parameterized candidate theorem to verify.
///
/// Each candidate is a point in the search space defined by a `TheoremFamily`.
/// The kernel verifies the candidate by checking that `proof` has type `statement`.
#[derive(Debug, Clone)]
pub struct CandidateTheorem {
    /// Unique identifier within the search space.
    pub id: CandidateId,
    /// The theorem family this candidate belongs to.
    pub family: TheoremFamily,
    /// Parameter values that produced this candidate.
    pub params: ParamVec,
    /// The theorem statement as a kernel Expr (the type to prove).
    pub statement: Expr,
    /// The proof term (if available). When `None`, the statement is
    /// checked for well-formedness only.
    pub proof: Option<Expr>,
}

/// Unique identifier for a candidate within a search run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CandidateId(pub u64);

/// Search-space coordinates as a flat vector of parameter values.
#[derive(Debug, Clone)]
pub struct ParamVec(pub Vec<ParamValue>);

impl ParamVec {
    /// Create an empty parameter vector.
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Create a parameter vector from natural number values.
    pub fn from_nats(values: &[u64]) -> Self {
        Self(values.iter().map(|&v| ParamValue::Nat(v)).collect())
    }
}

impl Default for ParamVec {
    fn default() -> Self {
        Self::new()
    }
}

/// A single parameter value in the search space.
#[derive(Debug, Clone)]
pub enum ParamValue {
    /// A natural number parameter (e.g., depth, width, constant C).
    Nat(u64),
    /// An index into a finite set of choices (e.g., bound function variant).
    Choice(usize),
}

impl std::fmt::Display for ParamValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nat(n) => write!(f, "{n}"),
            Self::Choice(i) => write!(f, "choice({i})"),
        }
    }
}

/// Result of verifying a single candidate.
#[derive(Debug, Clone)]
pub struct VerificationOutcome {
    /// The candidate that was verified.
    pub candidate_id: CandidateId,
    /// Whether the proof term type-checked against the statement.
    pub verified: bool,
    /// The inferred type (if verification succeeded).
    pub inferred_type: Option<Expr>,
    /// Error message (if verification failed).
    pub error: Option<String>,
    /// Verification time in nanoseconds.
    pub time_ns: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::family::TheoremFamily;

    #[test]
    fn test_candidate_id_equality() {
        assert_eq!(CandidateId(0), CandidateId(0));
        assert_ne!(CandidateId(0), CandidateId(1));
    }

    #[test]
    fn test_param_vec_from_nats() {
        let params = ParamVec::from_nats(&[1, 2, 3]);
        assert_eq!(params.0.len(), 3);
        match &params.0[0] {
            ParamValue::Nat(n) => assert_eq!(*n, 1),
            _ => panic!("expected Nat"),
        }
    }

    #[test]
    fn test_param_value_display() {
        assert_eq!(format!("{}", ParamValue::Nat(42)), "42");
        assert_eq!(format!("{}", ParamValue::Choice(3)), "choice(3)");
    }

    #[test]
    fn test_candidate_theorem_construction() {
        let candidate = CandidateTheorem {
            id: CandidateId(0),
            family: TheoremFamily::CertSizeBound,
            params: ParamVec::from_nats(&[2, 4, 1]),
            statement: Expr::prop(),
            proof: None,
        };
        assert_eq!(candidate.id, CandidateId(0));
        assert!(candidate.proof.is_none());
    }
}
