// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT term definitions and solver result types.
//!
//! The theory-facing control-plane traits and literals live in `theory.rs`.

use super::theory::TheoryLiteral;
use crate::cdcl::{ClauseRef, Lit};
use crate::egraph::Symbol;
use clean_kernel::expr::BigNat;

/// Term identifier in the SMT context
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermId(pub(crate) u32);

impl TermId {
    #[inline]
    pub(crate) fn new(raw: u32) -> Self {
        Self(raw)
    }

    #[inline]
    pub(crate) fn raw(self) -> u32 {
        self.0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Signed integer value used in SMT terms.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SmtInt {
    /// Non-negative integer.
    NonNegative(BigNat),
    /// Negative integer with absolute value.
    Negative(BigNat),
}

impl SmtInt {
    #[inline]
    pub(crate) fn from_nat(value: BigNat) -> Self {
        SmtInt::NonNegative(value)
    }

    #[inline]
    pub(crate) fn from_i64(value: i64) -> Self {
        if value >= 0 {
            SmtInt::NonNegative(BigNat::from_u64(value as u64))
        } else {
            let abs = value.unsigned_abs();
            SmtInt::Negative(BigNat::from_u64(abs))
        }
    }
}

impl From<i64> for SmtInt {
    fn from(value: i64) -> Self {
        SmtInt::from_i64(value)
    }
}

impl From<BigNat> for SmtInt {
    fn from(value: BigNat) -> Self {
        SmtInt::from_nat(value)
    }
}

impl std::fmt::Display for SmtInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtInt::NonNegative(value) => write!(f, "{value}"),
            SmtInt::Negative(value) => write!(f, "-{value}"),
        }
    }
}

/// Internal term representation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SmtTerm {
    /// A constant/variable
    Const(Symbol),
    /// Function application
    App(Symbol, Vec<TermId>),
    /// Integer constant
    Int(SmtInt),
    /// Rational constant (numerator, denominator)
    #[allow(dead_code)]
    // reserved for future rational-term support
    Rat(i64, i64),
}

/// Result of SMT solving
#[derive(Clone, Debug)]
#[must_use = "SMT results should be inspected to determine satisfiability"]
pub enum SmtResult {
    /// Satisfiable with the given model
    Sat(SmtModel),
    /// Unsatisfiable, optionally with an unsat core
    Unsat(Option<UnsatCore>),
    /// Unknown (resource limit or incomplete)
    Unknown,
}

/// Unsatisfiable core - subset of input clauses sufficient for UNSAT
///
/// Used for hint-based proof reconstruction (QuerySMT-style).
/// See: Clune, Barbosa, Avigad, "Hint-Based SMT Proof Reconstruction"
#[derive(Clone, Debug, Default)]
pub struct UnsatCore {
    /// Clause references that form the unsatisfiable core
    pub(crate) clauses: Vec<ClauseRef>,
}

/// SMT model
#[derive(Clone, Debug)]
pub struct SmtModel {
    /// The underlying SAT model
    pub(crate) sat_model: Vec<bool>,
    /// Equalities that hold
    pub(crate) equalities: Vec<(TermId, TermId)>,
    /// Disequalities that hold
    pub(crate) disequalities: Vec<(TermId, TermId)>,
}

impl SmtModel {
    /// Format a human-readable summary of the counterexample model.
    ///
    /// Returns term-id based equality/disequality counts since the model
    /// does not carry expression-level names. Callers that need detailed
    /// inspection should use crate-internal field access.
    pub(crate) fn display_summary(&self) -> String {
        format!(
            "counterexample: {} equalities, {} disequalities, {} SAT assignments",
            self.equalities.len(),
            self.disequalities.len(),
            self.sat_model.len(),
        )
    }
}

/// A record of a theory-level event during DPLL(T) solving (#2442 Phase 2).
///
/// The proof trail captures the *why* behind the UNSAT result: which theory
/// events (conflicts, propagations) the SAT solver incorporated. The bridge
/// maps trail entries back to hypotheses to guide proof term construction
/// instead of blind search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofTrailEntry {
    /// Theory found a conflict: these literals are mutually inconsistent.
    /// The SAT solver added the negation as a blocking clause.
    TheoryConflict {
        /// The conflicting SAT literals (positive: the literals that clash).
        conflict_lits: Vec<Lit>,
        /// The conflicting literals resolved back to theory-level meaning.
        /// Auxiliary SAT literals without theory mappings are omitted.
        conflict_theory_lits: Vec<TheoryLiteral>,
        /// Which theory produced this conflict.
        theory_name: &'static str,
        /// The SAT clause index assigned to the blocking clause, if any.
        clause_index: Option<u32>,
    },
    /// Theory propagated a literal with explanation premises.
    /// The SAT solver added `NOT(p1) OR ... OR NOT(pn) OR implied` as a clause.
    TheoryPropagation {
        /// The propagated literal.
        implied: Lit,
        /// The propagated literal resolved to theory-level meaning, if tracked.
        implied_theory_lit: Option<TheoryLiteral>,
        /// Explanation premises (the literals that justify `implied`).
        explanation: Vec<Lit>,
        /// Explanation premises resolved to theory-level meaning.
        /// Auxiliary SAT literals without theory mappings are omitted.
        explanation_theory_lits: Vec<TheoryLiteral>,
        /// Which theory produced this propagation.
        theory_name: &'static str,
        /// The SAT clause index assigned to the propagation clause, if any.
        clause_index: Option<u32>,
    },
}

/// SMT solver statistics
#[derive(Clone, Debug, Default)]
pub struct SmtStats {
    pub(crate) num_vars: usize,
    pub(crate) num_clauses: usize,
    pub(crate) num_terms: usize,
    pub(crate) sat_conflicts: u64,
    pub(crate) sat_decisions: u64,
    pub(crate) sat_propagations: u64,
    pub(crate) sat_learned_clauses: u64,
    pub(crate) theory_check_calls: u64,
    pub(crate) theory_conflicts: u64,
    pub(crate) theory_propagated_literals: u64,
    pub(crate) theory_unknowns: u64,
    pub(crate) theory_stats: Vec<(&'static str, u64)>,
}
