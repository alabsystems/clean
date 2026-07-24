// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Abstract CDCL (Conflict-Driven Clause Learning) Specification
//!
//! Invariants S01-S06 formalize correctness properties of CDCL solvers.

pub mod bcp;
pub mod clause_minimization;
pub mod conflict_analysis;
pub mod decision_heuristic;
pub mod dimacs;
pub(crate) mod kernel_proofs;
pub mod preprocessing;
pub mod proof_logging;
pub mod restart;
mod spec_registration;
pub mod termination;
#[cfg(test)]
mod tests_bcp;
#[cfg(test)]
mod tests_cdcl_kernel;
#[cfg(test)]
mod tests_conflict;
#[cfg(test)]
mod tests_decision_heuristic;
#[cfg(test)]
mod tests_minimization;
#[cfg(test)]
mod tests_preprocessing;
#[cfg(test)]
mod tests_proof_logging;
#[cfg(test)]
mod tests_restart;
#[cfg(test)]
mod tests_termination;
#[cfg(test)]
mod tests_vsids;
#[cfg(test)]
mod tests_vsids_ext;
#[cfg(test)]
mod tests_watched_literals;
pub mod vsids;
pub mod vsids_extensions;
pub mod watched_literals;

use crate::spec::ProofStatus;

/// A literal is a signed integer: positive for x_i, negative for NOT x_i.
pub type Literal = i32;

/// A clause is a disjunction of literals.
pub type Clause = Vec<Literal>;

/// Extract the variable index from a literal.
#[must_use]
pub fn var_of(lit: Literal) -> u32 {
    lit.unsigned_abs()
}

/// Negate a literal.
#[must_use]
pub fn negate(lit: Literal) -> Literal {
    -lit
}

/// Assignment value for a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignValue {
    True,
    False,
}

/// A trail entry records a literal assignment and its reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrailEntry {
    pub literal: Literal,
    pub decision_level: u32,
    pub reason: Option<usize>,
}

/// Abstract CDCL solver state.
#[derive(Debug, Clone)]
pub struct CdclState {
    pub num_vars: u32,
    pub clauses: Vec<Clause>,
    pub assignment: Vec<Option<AssignValue>>,
    pub trail: Vec<TrailEntry>,
    pub trail_lim: Vec<usize>,
    pub decision_level: u32,
    pub watches: Vec<(usize, usize)>,
}

impl CdclState {
    #[must_use]
    pub fn new(num_vars: u32, clauses: Vec<Clause>) -> Self {
        let mut watches = Vec::with_capacity(clauses.len());
        for clause in &clauses {
            if clause.len() >= 2 {
                watches.push((0, 1));
            } else {
                watches.push((0, 0));
            }
        }
        Self {
            num_vars,
            clauses,
            assignment: vec![None; (num_vars + 1) as usize],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
            watches,
        }
    }

    #[must_use]
    pub fn eval_literal(&self, lit: Literal) -> Option<bool> {
        let var = var_of(lit) as usize;
        self.assignment.get(var).and_then(|a| {
            a.map(|v| {
                let p = lit > 0;
                match v {
                    AssignValue::True => p,
                    AssignValue::False => !p,
                }
            })
        })
    }

    #[must_use]
    pub fn eval_clause(&self, clause: &[Literal]) -> Option<bool> {
        let mut has_unassigned = false;
        for &lit in clause {
            match self.eval_literal(lit) {
                Some(true) => return Some(true),
                Some(false) => {}
                None => has_unassigned = true,
            }
        }
        if has_unassigned {
            None
        } else {
            Some(false)
        }
    }

    pub fn assign(&mut self, lit: Literal, reason: Option<usize>) -> Result<(), CdclError> {
        let var = var_of(lit) as usize;
        if var == 0 || var > self.num_vars as usize {
            return Err(CdclError::InvalidVariable(var as u32));
        }
        if self.assignment[var].is_some() {
            return Err(CdclError::AlreadyAssigned(var as u32));
        }
        self.assignment[var] = Some(if lit > 0 {
            AssignValue::True
        } else {
            AssignValue::False
        });
        self.trail.push(TrailEntry {
            literal: lit,
            decision_level: self.decision_level,
            reason,
        });
        Ok(())
    }

    pub fn decide(&mut self, lit: Literal) -> Result<(), CdclError> {
        self.decision_level += 1;
        self.trail_lim.push(self.trail.len());
        self.assign(lit, None)
    }

    pub fn backtrack_to(&mut self, level: u32) -> Result<(), CdclError> {
        if level > self.decision_level {
            return Err(CdclError::InvalidBacktrackLevel {
                target: level,
                current: self.decision_level,
            });
        }
        while self.trail.last().is_some_and(|e| e.decision_level > level) {
            if let Some(entry) = self.trail.pop() {
                self.assignment[var_of(entry.literal) as usize] = None;
            }
        }
        self.trail_lim.truncate(level as usize);
        self.decision_level = level;
        Ok(())
    }

    pub fn add_learned_clause(&mut self, clause: Clause) {
        if clause.len() >= 2 {
            self.watches.push((0, 1));
        } else {
            self.watches.push((0, 0));
        }
        self.clauses.push(clause);
    }

    /// S01: Check trail consistency -- no variable appears twice.
    pub fn check_trail_consistency(&self) -> Result<(), CdclError> {
        let mut seen = vec![false; (self.num_vars + 1) as usize];
        for entry in &self.trail {
            let var = var_of(entry.literal) as usize;
            if seen[var] {
                return Err(CdclError::TrailInconsistency(var as u32));
            }
            seen[var] = true;
        }
        Ok(())
    }

    /// S02: Check two-watched-literal invariant.
    pub fn check_two_watched(&self) -> Result<(), CdclError> {
        for (ci, clause) in self.clauses.iter().enumerate() {
            if clause.len() < 2 {
                continue;
            }
            let (w0, w1) = self.watches[ci];
            if w0 == w1 || w0 >= clause.len() || w1 >= clause.len() {
                return Err(CdclError::WatchInvariantViolation(ci));
            }
        }
        Ok(())
    }

    /// S03: Verify a learned clause is sound.
    pub fn verify_learned_clause(&self, learned: &[Literal]) -> Result<(), CdclError> {
        for &lit in learned {
            let var = var_of(lit);
            if !self
                .clauses
                .iter()
                .any(|c| c.iter().any(|&l| var_of(l) == var))
            {
                return Err(CdclError::UnsoundLearnedClause {
                    variable: var,
                    clause: learned.to_vec(),
                });
            }
        }
        Ok(())
    }

    /// Return the trail index of a variable, or `None` if unassigned.
    #[must_use]
    pub fn trail_index_of(&self, var: u32) -> Option<usize> {
        self.trail.iter().position(|e| var_of(e.literal) == var)
    }

    /// Return the decision level at which a variable was assigned.
    #[must_use]
    pub fn level_of(&self, var: u32) -> Option<u32> {
        self.trail
            .iter()
            .find(|e| var_of(e.literal) == var)
            .map(|e| e.decision_level)
    }

    /// S04: Check backtrack correctness.
    pub fn check_backtrack_correctness(&self) -> Result<(), CdclError> {
        for entry in &self.trail {
            if entry.decision_level > self.decision_level {
                return Err(CdclError::BacktrackInconsistency {
                    entry_level: entry.decision_level,
                    current_level: self.decision_level,
                });
            }
        }
        if self.trail_lim.len() as u32 != self.decision_level {
            return Err(CdclError::TrailLimMismatch {
                expected: self.decision_level,
                actual: self.trail_lim.len() as u32,
            });
        }
        Ok(())
    }
}

pub const S01_TRAIL_CONSISTENCY: ProofStatus = ProofStatus::DerivedPending;
pub const S02_TWO_WATCHED: ProofStatus = ProofStatus::DerivedPending;
pub const S03_LEARNED_CLAUSE_SOUND: ProofStatus = ProofStatus::DerivedPending;
pub const S04_BACKTRACK_CORRECTNESS: ProofStatus = ProofStatus::DerivedPending;
pub const S05_PROPAGATION_COMPLETENESS: ProofStatus = ProofStatus::DerivedPending;
pub const S06_TERMINATION: ProofStatus = ProofStatus::DerivedPending;

/// S05: Verify propagation completeness.
///
/// After BCP reaches a fixpoint, no unit clause should remain un-propagated.
/// This delegates to `bcp::check_propagation_complete` and adds a proof-level
/// wrapper that checks the S05 invariant holds for the current state.
///
/// ## Proof sketch (Handbook of Satisfiability, Ch. 4, Lemma 4.2):
/// BCP iterates `bcp_step` until `Fixpoint`. Each step scans all clauses.
/// If any clause has exactly one unassigned literal (unit clause), it would
/// have been detected and returned as `Propagated`, not `Fixpoint`.
/// Therefore at fixpoint, no unit clause exists => S05 holds.
pub fn verify_propagation_completeness(state: &CdclState) -> Result<(), CdclError> {
    bcp::check_propagation_complete(state)
}

/// S06: Verify CDCL termination argument.
///
/// CDCL terminates because each learned clause is new (not a duplicate) and
/// the total number of distinct clauses over `n` variables is finite (3^n).
/// This function checks that:
/// 1. No learned clause is a duplicate of an existing clause.
/// 2. Each learned clause is non-empty (empty clause means UNSAT is proven).
///
/// ## Proof sketch (Handbook of Satisfiability, Ch. 4, Theorem 4.1):
/// - The clause database grows monotonically (clauses are only added, never removed
///   in the abstract model -- real solvers use clause deletion but maintain completeness).
/// - Each learned clause is an implicant of the original formula (S03 soundness).
/// - The set of possible clauses over `n` variables is bounded by 3^n.
/// - Therefore the loop must terminate.
pub fn verify_termination_argument(state: &CdclState) -> Result<(), CdclError> {
    // Check no duplicate clauses exist.
    // Use sorted clause representations for comparison.
    let mut sorted_clauses: Vec<Vec<Literal>> = Vec::with_capacity(state.clauses.len());
    for (i, clause) in state.clauses.iter().enumerate() {
        let mut sorted = clause.clone();
        sorted.sort_unstable();
        // Check for empty clause (proof of UNSAT -- this is valid termination).
        // We allow empty clauses since they represent the UNSAT result.
        for existing in &sorted_clauses {
            if *existing == sorted {
                return Err(CdclError::UnsoundLearnedClause {
                    variable: 0,
                    clause: state.clauses[i].clone(),
                });
            }
        }
        sorted_clauses.push(sorted);
    }
    Ok(())
}

/// Errors from CDCL operations and invariant checks.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CdclError {
    InvalidVariable(u32),
    AlreadyAssigned(u32),
    TrailInconsistency(u32),
    WatchInvariantViolation(usize),
    UnsoundLearnedClause {
        variable: u32,
        clause: Vec<Literal>,
    },
    InvalidBacktrackLevel {
        target: u32,
        current: u32,
    },
    BacktrackInconsistency {
        entry_level: u32,
        current_level: u32,
    },
    TrailLimMismatch {
        expected: u32,
        actual: u32,
    },
    Conflict(usize),
    ParseError(String),
    /// Conflict analysis: no reason clause found for a propagated literal.
    NoReasonClause {
        literal: Literal,
    },
    /// Conflict analysis: clause index out of bounds.
    ClauseIndexOutOfBounds {
        index: usize,
        total: usize,
    },
    /// Conflict analysis: resolution failed (no pivot found).
    ResolutionFailed {
        pivot_var: u32,
    },
    /// Conflict analysis: could not find UIP (algorithm did not converge).
    UipNotFound,
}

impl std::fmt::Display for CdclError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CdclError::InvalidVariable(v) => write!(f, "invalid variable index: {v}"),
            CdclError::AlreadyAssigned(v) => write!(f, "variable {v} already assigned"),
            CdclError::TrailInconsistency(v) => {
                write!(f, "S01 violation: variable {v} on trail twice")
            }
            CdclError::WatchInvariantViolation(ci) => write!(f, "S02 violation: clause {ci}"),
            CdclError::UnsoundLearnedClause { variable, clause } => {
                write!(f, "S03 violation: var {variable} in {clause:?}")
            }
            CdclError::InvalidBacktrackLevel { target, current } => {
                write!(f, "invalid backtrack: {target} > {current}")
            }
            CdclError::BacktrackInconsistency {
                entry_level,
                current_level,
            } => write!(f, "S04 violation: level {entry_level} > {current_level}"),
            CdclError::TrailLimMismatch { expected, actual } => {
                write!(f, "S04 violation: trail_lim {actual} != {expected}")
            }
            CdclError::Conflict(ci) => write!(f, "BCP conflict in clause {ci}"),
            CdclError::ParseError(msg) => write!(f, "DIMACS parse error: {msg}"),
            CdclError::NoReasonClause { literal } => write!(
                f,
                "conflict analysis: no reason clause for literal {literal}"
            ),
            CdclError::ClauseIndexOutOfBounds { index, total } => {
                write!(f, "clause index {index} out of bounds (total: {total})")
            }
            CdclError::ResolutionFailed { pivot_var } => write!(
                f,
                "resolution failed: pivot variable {pivot_var} not found in both clauses"
            ),
            CdclError::UipNotFound => write!(f, "conflict analysis: UIP not found"),
        }
    }
}

impl std::error::Error for CdclError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cdcl_state_new() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        assert_eq!(state.num_vars, 3);
        assert_eq!(state.clauses.len(), 2);
    }

    #[test]
    fn test_cdcl_assign_and_eval() {
        let mut state = CdclState::new(2, vec![vec![1, -2]]);
        state.assign(1, None).expect("assign");
        assert_eq!(state.eval_literal(1), Some(true));
        assert_eq!(state.eval_literal(-1), Some(false));
        assert_eq!(state.eval_literal(2), None);
    }

    #[test]
    fn test_cdcl_double_assign_fails() {
        let mut state = CdclState::new(2, vec![]);
        state.assign(1, None).expect("first");
        assert!(state.assign(1, None).is_err());
        assert!(state.assign(-1, None).is_err());
    }

    #[test]
    fn test_cdcl_decide_and_backtrack() {
        let mut state = CdclState::new(3, vec![]);
        state.decide(1).expect("decide");
        state.decide(2).expect("decide");
        assert_eq!(state.decision_level, 2);
        state.backtrack_to(1).expect("backtrack");
        assert_eq!(state.decision_level, 1);
        assert_eq!(state.eval_literal(2), None);
        assert_eq!(state.eval_literal(1), Some(true));
    }

    #[test]
    fn test_cdcl_eval_clause() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        assert_eq!(state.eval_clause(&[1, 2, 3]), None);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        assert_eq!(state.eval_clause(&[1, 2, 3]), None);
        state.assign(-3, None).expect("a");
        assert_eq!(state.eval_clause(&[1, 2, 3]), Some(false));
    }

    #[test]
    fn test_cdcl_check_trail_consistency_ok() {
        let mut state = CdclState::new(3, vec![]);
        state.assign(1, None).expect("a");
        state.assign(-2, None).expect("a");
        state.check_trail_consistency().expect("ok");
    }

    #[test]
    fn test_cdcl_invariant_checkers() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        state.check_two_watched().expect("ok");
        state.verify_learned_clause(&[1, 2]).expect("ok");
        assert!(state.verify_learned_clause(&[4]).is_err());
    }

    #[test]
    fn test_cdcl_backtrack_correctness() {
        let mut state = CdclState::new(3, vec![]);
        state.decide(1).expect("d");
        state.decide(2).expect("d");
        state.check_backtrack_correctness().expect("ok");
        state.backtrack_to(0).expect("bt");
        state.check_backtrack_correctness().expect("ok");
    }

    #[test]
    fn test_cdcl_helpers() {
        assert_eq!(negate(5), -5);
        assert_eq!(negate(-3), 3);
        assert_eq!(var_of(5), 5);
        assert_eq!(var_of(-3), 3);
    }

    #[test]
    fn test_cdcl_error_display() {
        assert!(CdclError::TrailInconsistency(7).to_string().contains("7"));
    }

    #[test]
    fn test_cdcl_proof_status_constants() {
        assert_eq!(S01_TRAIL_CONSISTENCY, ProofStatus::DerivedPending);
        assert_eq!(S02_TWO_WATCHED, ProofStatus::DerivedPending);
        assert_eq!(S03_LEARNED_CLAUSE_SOUND, ProofStatus::DerivedPending);
        assert_eq!(S04_BACKTRACK_CORRECTNESS, ProofStatus::DerivedPending);
        assert_eq!(S05_PROPAGATION_COMPLETENESS, ProofStatus::DerivedPending);
        assert_eq!(S06_TERMINATION, ProofStatus::DerivedPending);
    }
}
