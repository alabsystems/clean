// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DRAT (Deletion Resolution Asymmetric Tautology) proof verifier.

use std::collections::{HashMap, HashSet};

use super::types::{CnfFormula, DratError, DratOp, DratProof};

/// DRAT proof verifier
///
/// Uses HashMap-based clause storage with stable IDs for O(1) deletion,
/// matching the LRAT verifier pattern. A reverse content index maps clause
/// literals to their IDs, making content-based removal O(clause_len)
/// amortized instead of O(C * L) linear scan (#2041).
pub struct DratVerifier {
    /// Active clauses indexed by stable ID
    clauses: HashMap<u64, Vec<i32>>,
    /// Reverse index: clause content → clause IDs with that content.
    /// DRAT identifies clauses by content, so this avoids scanning all clauses.
    content_index: HashMap<Vec<i32>, Vec<u64>>,
    /// Next clause ID to assign
    next_id: u64,
    /// Number of variables (maintained incrementally)
    num_vars: usize,
}

impl DratVerifier {
    /// Create a new DRAT verifier
    pub fn new() -> Self {
        Self {
            clauses: HashMap::new(),
            content_index: HashMap::new(),
            next_id: 1,
            num_vars: 0,
        }
    }

    /// Initialize with a CNF formula
    pub fn init_formula(&mut self, formula: &CnfFormula) {
        self.num_vars = formula.num_vars;
        self.clauses.clear();
        self.content_index.clear();
        self.next_id = 1;

        for clause in &formula.clauses {
            self.add_clause_internal(clause.clone());
        }
    }

    /// Add a clause to the verifier (internal, no RUP check)
    fn add_clause_internal(&mut self, clause: Vec<i32>) {
        // Maintain max_var incrementally
        for &lit in &clause {
            let var = lit.unsigned_abs() as usize;
            if var > self.num_vars {
                self.num_vars = var;
            }
        }

        let id = self.next_id;
        self.content_index
            .entry(clause.clone())
            .or_default()
            .push(id);
        self.clauses.insert(id, clause);
        self.next_id += 1;
    }

    /// Remove a clause from the verifier.
    ///
    /// Uses the content_index reverse map for O(clause_len) amortized lookup
    /// instead of scanning all clauses. DRAT proofs identify clauses by content
    /// (not ID), so the reverse index is essential for performance (#2041).
    fn remove_clause(&mut self, clause: &[i32]) {
        if let Some(ids) = self.content_index.get_mut(clause) {
            if let Some(id) = ids.pop() {
                self.clauses.remove(&id);
                if ids.is_empty() {
                    self.content_index.remove(clause);
                }
            }
        }
    }

    /// Check if a clause is RUP (Reverse Unit Propagation)
    ///
    /// A clause C is RUP if unit propagation on the negation of C
    /// leads to a conflict.
    pub(crate) fn is_rup(&self, clause: &[i32]) -> bool {
        // Use incrementally maintained num_vars instead of recomputing
        let max_var = clause
            .iter()
            .map(|&l| l.unsigned_abs() as usize)
            .max()
            .unwrap_or(0)
            .max(self.num_vars);

        // Assignment: None = unassigned, Some(true) = true, Some(false) = false
        let mut assignment: Vec<Option<bool>> = vec![None; max_var + 1];

        // Set all literals in clause to false (negate the clause)
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            assignment[var] = Some(lit < 0); // If lit is positive, assign false
        }

        // Unit propagation

        self.propagate(&mut assignment)
    }

    /// Perform unit propagation and return true if a conflict is found.
    ///
    /// REQUIRES: `assignment` has length >= `self.num_vars + 1`. Initial
    ///   assignments reflect the negation of the clause being checked.
    /// ENSURES: Returns true iff a conflict (all literals false in some clause)
    ///   is found via fixed-point unit propagation. `assignment` is updated
    ///   with propagated values.
    fn propagate(&self, assignment: &mut [Option<bool>]) -> bool {
        let mut changed = true;

        while changed {
            changed = false;

            for clause in self.clauses.values() {
                let mut unassigned_count = 0;
                let mut unassigned_lit = None;
                let mut satisfied = false;
                let mut num_false = 0;

                for &lit in clause {
                    let var = lit.unsigned_abs() as usize;
                    if var >= assignment.len() {
                        // Variable out of range - treat as unassigned
                        unassigned_count += 1;
                        if unassigned_lit.is_none() {
                            unassigned_lit = Some(lit);
                        }
                        continue;
                    }

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
                            unassigned_count += 1;
                            if unassigned_lit.is_none() {
                                unassigned_lit = Some(lit);
                            }
                        }
                    }
                }

                if satisfied {
                    continue;
                }

                // All literals are false - conflict!
                if unassigned_count == 0 && num_false == clause.len() {
                    return true;
                }

                // Unit clause - propagate (exactly one unassigned, rest false)
                if unassigned_count == 1 && num_false == clause.len() - 1 {
                    if let Some(lit) = unassigned_lit {
                        let var = lit.unsigned_abs() as usize;
                        if var < assignment.len() && assignment[var].is_none() {
                            assignment[var] = Some(lit > 0);
                            changed = true;
                        }
                    }
                }
            }
        }

        false
    }

    /// Check if a clause is RAT (Resolution Asymmetric Tautology)
    ///
    /// A clause C with pivot literal p is RAT if for every clause D
    /// containing ¬p, the resolvent of C and D on p is RUP.
    pub(crate) fn is_rat(&self, clause: &[i32], pivot: i32) -> bool {
        // Find all clauses containing the negation of the pivot
        let neg_pivot = -pivot;

        for other in self.clauses.values() {
            if !other.contains(&neg_pivot) {
                continue;
            }

            // Compute resolvent: (C \ {p}) ∪ (D \ {¬p}) using HashSet for O(1) dedup
            let mut resolvent: HashSet<i32> =
                clause.iter().filter(|&&l| l != pivot).copied().collect();

            for &lit in other {
                if lit != neg_pivot {
                    resolvent.insert(lit);
                }
            }

            let resolvent_vec: Vec<i32> = resolvent.into_iter().collect();

            // Check if resolvent is RUP
            if !self.is_rup(&resolvent_vec) {
                return false;
            }
        }

        true
    }

    /// Verify a DRAT proof.
    ///
    /// REQUIRES: `formula` is a valid CNF formula. `proof` contains well-formed
    ///   DRAT operations (Add/Delete with valid clauses).
    /// ENSURES: Returns Ok(true) iff the proof derives the empty clause,
    ///   certifying UNSAT. Each addition is verified via RUP or RAT check.
    ///   Returns Err(RupCheckFailed) or Err(RatCheckFailed) if a step fails
    ///   verification. Returns Err(NoEmptyClause) if proof ends without
    ///   deriving contradiction.
    pub fn verify(formula: &CnfFormula, proof: &DratProof) -> Result<bool, DratError> {
        let mut verifier = DratVerifier::new();
        verifier.init_formula(formula);

        let mut derived_empty = false;

        for (step, op) in proof.operations.iter().enumerate() {
            match op {
                DratOp::Add(clause) => {
                    // Empty clause requires RUP check (conflict with no assumptions)
                    if clause.is_empty() {
                        // Empty clause is RUP iff unit propagation on current formula
                        // leads to conflict without any initial assignments
                        if verifier.is_rup(clause) {
                            derived_empty = true;
                            break;
                        } else {
                            return Err(DratError::RupCheckFailed {
                                clause: clause.clone(),
                                step,
                            });
                        }
                    }

                    // First try RUP
                    if verifier.is_rup(clause) {
                        verifier.add_clause_internal(clause.clone());
                        continue;
                    }

                    // Try RAT with each literal as pivot
                    let mut found_rat = false;
                    for &pivot in clause {
                        if verifier.is_rat(clause, pivot) {
                            verifier.add_clause_internal(clause.clone());
                            found_rat = true;
                            break;
                        }
                    }

                    if !found_rat {
                        return Err(DratError::RatCheckFailed {
                            clause: clause.clone(),
                            pivot: clause.first().copied().unwrap_or(0),
                            step,
                        });
                    }
                }
                DratOp::Delete(clause) => {
                    verifier.remove_clause(clause);
                }
            }
        }

        if !derived_empty {
            return Err(DratError::NoEmptyClause);
        }

        Ok(true)
    }
}

impl Default for DratVerifier {
    fn default() -> Self {
        Self::new()
    }
}
