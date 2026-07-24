// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL Termination Verification (S06)
//!
//! The CDCL algorithm terminates because:
//! 1. The clause space over n variables is finite (at most 3^n distinct clauses).
//! 2. Each learned clause is new (not already in the database).
//! 3. The clause database grows monotonically (in the abstract model).
//!
//! Together these imply the loop must terminate: either the empty clause is
//! derived (UNSAT) or all decisions lead to satisfying assignments (SAT).
//!
//! Reference: Handbook of Satisfiability, Ch. 4, Theorem 4.1.

use super::{var_of, CdclError, CdclState, Clause, Literal};
use crate::spec::ProofStatus;

/// S06a: The clause space is finite (3^n bound).
pub const S06A_CLAUSE_SPACE_FINITE: ProofStatus = ProofStatus::DerivedPending;

/// S06b: All clauses in the database are unique under sorted representation.
pub const S06B_CLAUSE_UNIQUENESS: ProofStatus = ProofStatus::DerivedPending;

/// S06c: The clause database grows monotonically.
pub const S06C_MONOTONE_GROWTH: ProofStatus = ProofStatus::DerivedPending;

/// Represents the finite clause space over `n` boolean variables.
///
/// Each variable can be positive, negative, or absent in a clause,
/// giving at most 3^n possible distinct clauses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClauseSpace {
    /// Number of boolean variables.
    pub num_vars: u32,
    /// Maximum number of distinct clauses (3^n), or `None` if overflow.
    pub max_clauses: Option<u128>,
}

impl ClauseSpace {
    /// Create a clause space for `n` variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            num_vars,
            max_clauses: clause_space_size(num_vars),
        }
    }

    /// Whether the space size is representable (no overflow).
    #[must_use]
    pub fn is_finite_representable(&self) -> bool {
        self.max_clauses.is_some()
    }
}

/// Compute 3^n using checked arithmetic.
///
/// Returns `None` on overflow (n too large for u128).
#[must_use]
pub fn clause_space_size(num_vars: u32) -> Option<u128> {
    let mut result: u128 = 1;
    for _ in 0..num_vars {
        result = result.checked_mul(3)?;
    }
    Some(result)
}

/// Normalize a clause to a canonical sorted, deduplicated representation.
///
/// This allows comparison of clauses regardless of literal ordering.
#[must_use]
fn normalize_clause(clause: &[Literal]) -> Vec<Literal> {
    let mut sorted = clause.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    sorted
}

/// Evidence for CDCL termination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TerminationWitness {
    /// Number of distinct clauses currently in the database.
    pub unique_clause_count: usize,
    /// Maximum possible distinct clauses (3^n), or `None` on overflow.
    pub max_clauses: Option<u128>,
    /// Whether the empty clause has been derived (UNSAT proven).
    pub has_empty_clause: bool,
    /// Whether all clauses are unique.
    pub all_unique: bool,
}

impl TerminationWitness {
    /// Progress ratio: learned / max_possible. Returns `None` on overflow.
    #[must_use]
    pub fn progress(&self) -> Option<f64> {
        self.max_clauses.map(|max| {
            if max == 0 {
                1.0
            } else {
                self.unique_clause_count as f64 / max as f64
            }
        })
    }

    /// Whether the witness constitutes a valid termination argument.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.all_unique && self.max_clauses.is_some()
    }
}

/// Verify that all clauses in the database are unique under sorted representation.
///
/// Two clauses are considered duplicates if they contain the same set of literals
/// (regardless of order). This is stronger than the basic check in `mod.rs` because
/// it also deduplicates within each clause.
pub fn verify_clause_uniqueness(clauses: &[Clause]) -> Result<(), CdclError> {
    let normalized: Vec<Vec<Literal>> = clauses.iter().map(|c| normalize_clause(c)).collect();
    for i in 0..normalized.len() {
        for j in (i + 1)..normalized.len() {
            if normalized[i] == normalized[j] {
                return Err(CdclError::UnsoundLearnedClause {
                    variable: 0,
                    clause: clauses[j].clone(),
                });
            }
        }
    }
    Ok(())
}

/// Verify monotone growth: `after` is a superset of `before`.
///
/// In the abstract CDCL model, clauses are only added, never removed.
/// This checks that every clause in `before` appears in `after`.
pub fn verify_monotone_growth(before: &[Clause], after: &[Clause]) -> Result<(), CdclError> {
    let after_normalized: Vec<Vec<Literal>> = after.iter().map(|c| normalize_clause(c)).collect();
    for clause in before {
        let needle = normalize_clause(clause);
        if !after_normalized.contains(&needle) {
            return Err(CdclError::UnsoundLearnedClause {
                variable: 0,
                clause: clause.clone(),
            });
        }
    }
    Ok(())
}

/// Compute the progress metric: |unique clauses| / 3^n.
///
/// Returns `None` if the clause space overflows u128.
/// Progress must strictly increase with each new learned clause and is
/// bounded by 1.0 (all possible clauses exhausted => UNSAT).
#[must_use]
pub fn compute_progress_metric(clauses: &[Clause], num_vars: u32) -> Option<f64> {
    let max = clause_space_size(num_vars)?;
    if max == 0 {
        return Some(1.0);
    }
    let unique_count = count_unique_clauses(clauses);
    Some(unique_count as f64 / max as f64)
}

/// Count unique clauses by normalizing and deduplicating.
#[must_use]
fn count_unique_clauses(clauses: &[Clause]) -> usize {
    let mut normalized: Vec<Vec<Literal>> = clauses.iter().map(|c| normalize_clause(c)).collect();
    normalized.sort();
    normalized.dedup();
    normalized.len()
}

/// Verify that a candidate learned clause is not already in the database.
pub fn verify_learned_clause_new(
    existing: &[Clause],
    candidate: &[Literal],
) -> Result<(), CdclError> {
    let normalized_candidate = normalize_clause(candidate);
    for clause in existing {
        if normalize_clause(clause) == normalized_candidate {
            return Err(CdclError::UnsoundLearnedClause {
                variable: 0,
                clause: candidate.to_vec(),
            });
        }
    }
    Ok(())
}

/// Verify that a clause is not tautological.
///
/// A tautological clause contains both a literal and its negation (x and -x).
/// Learned clauses should never be tautological since tautologies are always
/// satisfied and provide no information.
pub fn verify_no_tautological_learned(clause: &[Literal]) -> Result<(), CdclError> {
    for &lit in clause {
        if clause.contains(&(-lit)) {
            return Err(CdclError::UnsoundLearnedClause {
                variable: var_of(lit),
                clause: clause.to_vec(),
            });
        }
    }
    Ok(())
}

/// Check whether `shorter` subsumes `longer`.
///
/// A clause C subsumes D if every literal in C also appears in D.
/// If a learned clause subsumes an existing clause, that represents progress:
/// the subsumed clause is logically redundant.
#[must_use]
pub fn is_subsumed_by(shorter: &[Literal], longer: &[Literal]) -> bool {
    let norm_short = normalize_clause(shorter);
    let norm_long = normalize_clause(longer);
    norm_short.iter().all(|lit| norm_long.contains(lit))
}

/// Verify subsumption progress: check if any existing clause is subsumed
/// by the candidate. Returns the indices of subsumed clauses.
#[must_use]
pub fn verify_subsumption_progress(existing: &[Clause], candidate: &[Literal]) -> Vec<usize> {
    existing
        .iter()
        .enumerate()
        .filter(|(_, clause)| {
            is_subsumed_by(candidate, clause)
                && normalize_clause(candidate) != normalize_clause(clause)
        })
        .map(|(i, _)| i)
        .collect()
}

/// Build a `TerminationWitness` from a `CdclState`.
#[must_use]
pub fn build_termination_witness(state: &CdclState) -> TerminationWitness {
    let unique_clause_count = count_unique_clauses(&state.clauses);
    let max_clauses = clause_space_size(state.num_vars);
    let has_empty_clause = state.clauses.iter().any(|c| c.is_empty());
    let all_unique = verify_clause_uniqueness(&state.clauses).is_ok();
    TerminationWitness {
        unique_clause_count,
        max_clauses,
        has_empty_clause,
        all_unique,
    }
}

/// Top-level S06 termination verification.
///
/// Checks:
/// 1. All clauses are unique (S06b).
/// 2. The clause space is finite and representable (S06a).
/// 3. If two snapshots are provided, the second is a monotone superset (S06c).
///
/// This establishes that CDCL must terminate: the clause database grows
/// monotonically within a finite space, so it must eventually either derive
/// the empty clause (UNSAT) or exhaust all possible decisions (SAT).
pub fn verify_termination(
    state: &CdclState,
    previous: Option<&CdclState>,
) -> Result<TerminationWitness, CdclError> {
    // S06b: clause uniqueness
    verify_clause_uniqueness(&state.clauses)?;

    // S06a: finite clause space
    let space = ClauseSpace::new(state.num_vars);
    if !space.is_finite_representable() {
        return Err(CdclError::UnsoundLearnedClause {
            variable: 0,
            clause: vec![],
        });
    }

    // S06c: monotone growth (if previous snapshot provided)
    if let Some(prev) = previous {
        verify_monotone_growth(&prev.clauses, &state.clauses)?;
    }

    Ok(build_termination_witness(state))
}
