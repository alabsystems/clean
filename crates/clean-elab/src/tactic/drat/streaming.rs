// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Streaming/incremental LRAT proof verifier.

use std::collections::HashMap;

use super::lrat_verifier::LratCheckpoint;
use super::types::{CnfFormula, DratError, LratOp, LratProof, StepResult};

/// Streaming LRAT verifier for incremental proof checking.
///
/// Processes proof steps one at a time, enabling:
/// - Progress monitoring during long verification runs
/// - Checkpoint/resume for AI proof search sessions
/// - Early termination on first error
///
/// LRAT is preferred over DRAT for incremental mode because:
/// - Linear-time checking with explicit hints (O(n) vs O(n²) for DRAT)
/// - Clause IDs enable efficient checkpoint/resume
/// - Smaller state footprint per step
///
/// # Example
///
/// ```
/// use clean_elab::tactic::drat::{CnfFormula, LratOp, StreamingLratVerifier, StepResult};
///
/// let mut formula = CnfFormula::new();
/// formula.add_clause(vec![1]);      // id=1: x1
/// formula.add_clause(vec![-1, 2]);  // id=2: ¬x1 ∨ x2
/// formula.add_clause(vec![-2]);     // id=3: ¬x2
///
/// let mut verifier = StreamingLratVerifier::new();
/// verifier.init_formula(&formula);
///
/// // Process proof steps incrementally
/// let steps = vec![
///     LratOp::Add { id: 4, clause: vec![2], hints: vec![1, 2] },
///     LratOp::Add { id: 5, clause: vec![], hints: vec![3, 4] },
/// ];
///
/// for op in &steps {
///     match verifier.process_step(op) {
///         Ok(StepResult::Continue) => continue,
///         Ok(StepResult::Complete) => break,
///         Err(_e) => break,
///     }
/// }
///
/// assert!(verifier.is_complete());
/// ```
pub struct StreamingLratVerifier {
    /// Active clauses indexed by ID
    clauses: HashMap<u64, Vec<i32>>,
    /// Next automatic clause ID
    next_id: u64,
    /// Number of variables
    num_vars: usize,
    /// Number of proof steps processed
    steps_processed: usize,
    /// Whether empty clause has been derived
    derived_empty: bool,
}

impl StreamingLratVerifier {
    /// Create a new streaming LRAT verifier
    ///
    /// ENSURES: Returns an empty verifier with no clauses, `next_id = 1`,
    ///   `num_vars = 0`, `steps_processed = 0`, and `derived_empty = false`.
    pub fn new() -> Self {
        Self {
            clauses: HashMap::new(),
            next_id: 1,
            num_vars: 0,
            steps_processed: 0,
            derived_empty: false,
        }
    }

    /// Initialize with a CNF formula
    ///
    /// REQUIRES: `formula.clauses` are in the intended initial clause-ID order.
    /// ENSURES: Resets all prior verifier state and loads the formula clauses
    ///   under clause IDs `1..=formula.clauses.len()`.
    /// ENSURES: After initialization, `steps_processed = 0`,
    ///   `derived_empty = false`, and `next_id = formula.clauses.len() + 1`.
    pub fn init_formula(&mut self, formula: &CnfFormula) {
        self.num_vars = formula.num_vars;
        self.clauses.clear();
        self.next_id = 1;
        self.steps_processed = 0;
        self.derived_empty = false;

        for clause in &formula.clauses {
            self.clauses.insert(self.next_id, clause.clone());
            self.next_id += 1;
        }
    }

    /// Process a single proof step
    ///
    /// Returns `StepResult::Complete` when empty clause is derived.
    /// Returns error if step is invalid.
    ///
    /// REQUIRES: The verifier has been initialized with the active formula.
    /// REQUIRES: On successful `Add`, hint IDs reference clauses currently active
    ///   in the verifier state.
    /// ENSURES: If `derived_empty` was already true, returns
    ///   `StepResult::Complete` without mutating state.
    /// ENSURES: On successful `Add`, validates RUP and either inserts the clause
    ///   or marks verification complete for the empty clause, then increments
    ///   `steps_processed`.
    /// ENSURES: On successful `Delete`, removes the listed clause IDs (if present)
    ///   and increments `steps_processed`.
    pub fn process_step(&mut self, op: &LratOp) -> Result<StepResult, DratError> {
        if self.derived_empty {
            return Ok(StepResult::Complete);
        }

        match op {
            LratOp::Add { id, clause, hints } => {
                // Empty clause = proof complete, but must still verify RUP
                if clause.is_empty() {
                    // Empty clause must be derived via hints (RUP check with no literals to negate)
                    if !self.is_rup_with_hints(clause, hints)? {
                        return Err(DratError::RupCheckFailed {
                            clause: clause.clone(),
                            step: self.steps_processed,
                        });
                    }
                    self.derived_empty = true;
                    self.steps_processed += 1;
                    return Ok(StepResult::Complete);
                }

                // Verify RUP with hints
                if !self.is_rup_with_hints(clause, hints)? {
                    return Err(DratError::RupCheckFailed {
                        clause: clause.clone(),
                        step: self.steps_processed,
                    });
                }

                self.clauses.insert(*id, clause.clone());
                self.steps_processed += 1;
                Ok(StepResult::Continue)
            }
            LratOp::Delete { clause_ids, .. } => {
                for &del_id in clause_ids {
                    self.clauses.remove(&del_id);
                }
                self.steps_processed += 1;
                Ok(StepResult::Continue)
            }
        }
    }

    /// Create a checkpoint of current verifier state
    ///
    /// ENSURES: Returns a deep copy of the current verifier state.
    /// ENSURES: `StreamingLratVerifier::resume(self.checkpoint())` reconstructs an
    ///   observationally equivalent verifier.
    pub fn checkpoint(&self) -> LratCheckpoint {
        LratCheckpoint {
            clauses: self.clauses.clone(),
            next_id: self.next_id,
            num_vars: self.num_vars,
            steps_processed: self.steps_processed,
            derived_empty: self.derived_empty,
        }
    }

    /// Resume from a checkpoint
    ///
    /// REQUIRES: `checkpoint` was created from a compatible
    ///   `StreamingLratVerifier` state.
    /// ENSURES: The returned verifier fields exactly match the checkpoint.
    pub fn resume(checkpoint: LratCheckpoint) -> Self {
        Self {
            clauses: checkpoint.clauses,
            next_id: checkpoint.next_id,
            num_vars: checkpoint.num_vars,
            steps_processed: checkpoint.steps_processed,
            derived_empty: checkpoint.derived_empty,
        }
    }

    /// Get number of steps processed
    ///
    /// ENSURES: Returns the number of proof operations successfully processed so far.
    pub fn steps_processed(&self) -> usize {
        self.steps_processed
    }

    /// Check if proof is complete (empty clause derived)
    ///
    /// ENSURES: Returns `true` iff an empty clause has been derived.
    pub fn is_complete(&self) -> bool {
        self.derived_empty
    }

    /// Get current clause count (for progress reporting)
    ///
    /// ENSURES: Returns the number of currently active clauses in the verifier.
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Finalize verification - check that empty clause was derived
    ///
    /// ENSURES: Returns `Ok(true)` iff an empty clause has been derived.
    /// ENSURES: Returns `Err(DratError::NoEmptyClause)` otherwise.
    pub fn finalize(&self) -> Result<bool, DratError> {
        if !self.derived_empty {
            return Err(DratError::NoEmptyClause);
        }
        Ok(true)
    }

    /// Check RUP with specific hints (internal)
    fn is_rup_with_hints(&self, clause: &[i32], hints: &[u64]) -> Result<bool, DratError> {
        // Compute max variable across clause, hints, and all formula clauses
        // This handles cases where learned clauses introduce new variables
        // and ensures we can check conflicts against any clause
        let max_var_in_clause = clause
            .iter()
            .map(|&l| l.unsigned_abs() as usize)
            .max()
            .unwrap_or(0);

        let max_var_in_formula = self
            .clauses
            .values()
            .flat_map(|c| c.iter())
            .map(|&l| l.unsigned_abs() as usize)
            .max()
            .unwrap_or(0);

        let max_var = self.num_vars.max(max_var_in_clause).max(max_var_in_formula);
        let mut assignment: Vec<Option<bool>> = vec![None; max_var + 1];

        // Set all literals in clause to false (negate the clause)
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            assignment[var] = Some(lit < 0);
        }

        // Propagate using only the hint clauses
        for &hint_id in hints {
            let hint_clause = self.clauses.get(&hint_id).ok_or(DratError::InvalidHint {
                hint_id,
                step: self.steps_processed,
            })?;

            let mut unassigned_lit = None;
            let mut num_false = 0;
            let mut satisfied = false;

            for &lit in hint_clause {
                let var = lit.unsigned_abs() as usize;
                // Note: assignment is sized to cover all variables in formula + clause
                match assignment[var] {
                    Some(val) => {
                        let lit_true = (lit > 0) == val;
                        if lit_true {
                            satisfied = true;
                            break;
                        } else {
                            num_false += 1;
                        }
                    }
                    None => {
                        if unassigned_lit.is_some() {
                            // More than one unassigned - not unit
                            break;
                        }
                        unassigned_lit = Some(lit);
                    }
                }
            }

            if satisfied {
                continue;
            }

            // Conflict found!
            if num_false == hint_clause.len() {
                return Ok(true);
            }

            // Unit propagation
            if num_false == hint_clause.len() - 1 {
                if let Some(lit) = unassigned_lit {
                    let var = lit.unsigned_abs() as usize;
                    // assignment is sized to cover all variables
                    if assignment[var].is_none() {
                        assignment[var] = Some(lit > 0);
                    }
                }
            }
        }

        // Check if we have a conflict with any clause
        for clause in self.clauses.values() {
            let all_false = clause.iter().all(|&lit| {
                let var = lit.unsigned_abs() as usize;
                // assignment is sized to cover all variables in formula
                match assignment[var] {
                    Some(val) => (lit > 0) != val,
                    None => false,
                }
            });
            if all_false {
                return Ok(true);
            }
        }

        Ok(false)
    }
}

impl Default for StreamingLratVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function: verify LRAT proof with streaming API
///
/// Processes proof incrementally and returns progress updates via callback.
/// Useful for long-running verifications with progress reporting.
///
/// REQUIRES: `formula` and `proof` form a well-typed LRAT verification task.
/// REQUIRES: `progress_callback` may be invoked once per successfully processed
///   proof step with `(steps_done, total_steps)`.
/// ENSURES: Initializes a fresh verifier, processes proof operations in order,
///   and calls the callback after each successful step.
/// ENSURES: Returns `Ok(true)` on early empty-clause completion or successful
///   `finalize()`, and propagates the first `DratError`.
pub fn verify_lrat_streaming<F>(
    formula: &CnfFormula,
    proof: &LratProof,
    mut progress_callback: F,
) -> Result<bool, DratError>
where
    F: FnMut(usize, usize), // (steps_done, total_steps)
{
    let total_steps = proof.operations.len();
    let mut verifier = StreamingLratVerifier::new();
    verifier.init_formula(formula);

    for (i, op) in proof.operations.iter().enumerate() {
        match verifier.process_step(op)? {
            StepResult::Complete => {
                progress_callback(i + 1, total_steps);
                return Ok(true);
            }
            StepResult::Continue => {
                progress_callback(i + 1, total_steps);
            }
        }
    }

    verifier.finalize()
}
