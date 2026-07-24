// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clause database management for the CDCL solver.
//!
//! Methods for adding original and theory-derived clauses, including
//! deduplication, tautology elimination, unit propagation at level 0,
//! and UNSAT core extraction.

use super::solver::CdclSolver;
use super::types::{clause_ref_at, usize_to_u32, Clause, ClauseRef, LBool, Lit, SatUnsatCore};

impl CdclSolver {
    /// Add a clause to the solver.
    ///
    /// # Contracts
    ///
    /// **REQUIRES:**
    /// - All literals reference valid variables (created via `new_var()`)
    /// - Should be called before `solve()`
    ///
    /// **ENSURES:**
    /// - Returns `None` if clause makes problem immediately UNSAT (empty clause after simplification)
    /// - Returns `Some(ClauseRef)` otherwise (clause added or tautology detected)
    /// - Tautological clauses (containing both `x` and `!x`) are ignored (return dummy ref)
    /// - Duplicate literals are removed
    /// - Unit clauses trigger immediate propagation at decision level 0
    ///
    /// # Panics
    ///
    /// Panics if literals reference variables not created via `new_var()`.
    pub fn add_clause(&mut self, mut lits: Vec<Lit>) -> Option<ClauseRef> {
        // Remove duplicates and check for tautologies
        lits.sort_by_key(|l| l.0);
        let mut j = 0;
        for i in 0..lits.len() {
            // Skip duplicates
            if j > 0 && lits[j - 1] == lits[i] {
                continue;
            }
            // Check for tautology (x and !x)
            if j > 0 && lits[j - 1].var() == lits[i].var() {
                // Tautology - clause is trivially satisfied
                return Some(clause_ref_at(self.clauses.len())); // Dummy ref
            }
            lits[j] = lits[i];
            j += 1;
        }
        lits.truncate(j);

        // Handle special cases
        if lits.is_empty() {
            self.is_unsat = true;
            return None; // Empty clause = UNSAT
        }

        if lits.len() == 1 {
            // Unit clause - must be true at level 0
            let lit = lits[0];
            let current_clause_idx = usize_to_u32(self.clauses.len(), "clause index");
            // Store unit clause for proper indexing in unsat cores
            let cref = clause_ref_at(self.clauses.len());
            self.clauses.push(Clause::new(lits.clone(), false));
            self.num_original_clauses += 1;

            match self.lit_value(lit) {
                LBool::True => {
                    // Already satisfied - just return the clause ref
                    return Some(cref);
                }
                LBool::False => {
                    // Conflict - record the conflicting clauses for unsat core
                    self.is_unsat = true;
                    // Find the clause that set this variable to the opposite value
                    let var = lit.var();
                    if let Some(prev_clause) = self.unit_clause_origins[var.index()] {
                        self.unsat_core_indices = vec![prev_clause, current_clause_idx];
                    } else {
                        self.unsat_core_indices = vec![current_clause_idx];
                    }
                    return None; // Conflict at level 0
                }
                LBool::Undef => {
                    // Record this unit clause as the origin for this variable
                    self.unit_clause_origins[lit.var().index()] = Some(current_clause_idx);
                    self.set_lit(lit, cref);
                    return Some(cref);
                }
            }
        }

        // Add clause and set up watches
        let cref = clause_ref_at(self.clauses.len());
        let clause = Clause::new(lits.clone(), false);

        // Watch first two literals
        self.watches[lits[0].not().index()].push(cref);
        self.watches[lits[1].not().index()].push(cref);

        self.clauses.push(clause);
        self.num_original_clauses += 1;
        Some(cref)
    }

    /// Extract the unsat core after `add_clause` returned None.
    /// This returns the clause indices that contributed to the conflict.
    /// After calling this method, the internal core is cleared.
    pub(crate) fn take_unsat_core(&mut self) -> Option<SatUnsatCore> {
        if self.unsat_core_indices.is_empty() {
            None
        } else {
            Some(SatUnsatCore {
                clause_indices: std::mem::take(&mut self.unsat_core_indices),
            })
        }
    }

    /// Add a theory-derived clause as learned (not original).
    ///
    /// Used by DPLL(T): theory conflicts and propagations produce clauses
    /// that are logical consequences of the theory axioms, not part of the
    /// original problem. Unlike [`Self::add_clause`], this marks clauses as learned,
    /// computes LBD, and does **not** increment `num_original_clauses`.
    ///
    /// Returns `None` if the clause (after simplification) makes the formula UNSAT.
    pub(crate) fn add_theory_clause(&mut self, mut lits: Vec<Lit>) -> Option<ClauseRef> {
        // Same dedup/tautology logic as add_clause
        lits.sort_by_key(|l| l.0);
        let mut j = 0;
        for i in 0..lits.len() {
            if j > 0 && lits[j - 1] == lits[i] {
                continue;
            }
            if j > 0 && lits[j - 1].var() == lits[i].var() {
                return Some(clause_ref_at(self.clauses.len())); // Tautology
            }
            lits[j] = lits[i];
            j += 1;
        }
        lits.truncate(j);

        if lits.is_empty() {
            self.is_unsat = true;
            return None;
        }

        if lits.len() == 1 {
            let lit = lits[0];
            let cref = clause_ref_at(self.clauses.len());
            self.clauses.push(Clause::new(lits.clone(), true));

            match self.lit_value(lit) {
                LBool::True => {
                    return Some(cref);
                }
                LBool::False => {
                    self.is_unsat = true;
                    // Only include original clause indices in the unsat core.
                    // The theory clause itself is learned (not original), so we
                    // trace only the original clause that set the conflicting
                    // literal via unit_clause_origins.
                    let var = lit.var();
                    if let Some(prev_clause) = self.unit_clause_origins[var.index()] {
                        self.unsat_core_indices = vec![prev_clause];
                    }
                    // If no prev_clause, the variable was set by propagation
                    // (not a unit original clause), and collect_unsat_core_level0
                    // will trace origins through the reason clause chain.
                    return None;
                }
                LBool::Undef => {
                    // Do NOT store in unit_clause_origins: this is a learned
                    // theory clause, not an original clause. The literal's reason
                    // is stored via set_lit(lit, cref), so collect_unsat_core_level0
                    // will find it through var_data[var].reason and handle it via
                    // add_clause_origins (which correctly treats learned clauses
                    // as transparent for unsat core extraction).
                    self.set_lit(lit, cref);
                    return Some(cref);
                }
            }
        }

        // Multi-literal: store as learned with LBD
        let cref = clause_ref_at(self.clauses.len());
        let mut clause = Clause::new(lits.clone(), true);
        // LBD from stale var_data levels is a valid estimate for theory clauses
        // (levels represent when each literal was last assigned).
        clause.lbd = self.compute_lbd(&lits);

        // Watch first two literals
        self.watches[lits[0].not().index()].push(cref);
        self.watches[lits[1].not().index()].push(cref);

        self.clauses.push(clause);
        self.active_learned += 1;
        Some(cref)
    }
}
