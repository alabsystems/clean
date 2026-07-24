// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CDCL solver internals: BCP, conflict analysis, and UNSAT core extraction.
//!
//! These methods are part of `CdclSolver` but separated for file size
//! management. They implement the core CDCL algorithms:
//! - Boolean Constraint Propagation (BCP)
//! - 1UIP conflict analysis with origin tracking
//! - Learned clause management with LBD computation
//! - Level-0 UNSAT core collection

use hashbrown::HashSet;

use super::solver::{CdclSolver, CORE_LBD};
use super::types::{clause_ref_at, usize_to_u32, Clause, ClauseRef, LBool, Lit};

impl CdclSolver {
    /// Add a learned clause (during conflict analysis) with origin tracking
    pub(super) fn add_learned_clause(&mut self, lits: Vec<Lit>, origins: Vec<u32>) -> ClauseRef {
        debug_assert!(!lits.is_empty());

        if lits.len() == 1 {
            // Unit learned clause - store it for origin tracking but no watches needed.
            // This can happen when conflict analysis produces a clause with only one
            // literal (asserting at level 0).
            let cref = clause_ref_at(self.clauses.len());
            self.clauses.push(Clause::new_learned(lits, origins));
            self.active_learned += 1;
            return cref;
        }

        let cref = clause_ref_at(self.clauses.len());
        let mut clause = Clause::new_learned(lits.clone(), origins);

        clause.lbd = self.compute_lbd(&lits);

        // Watch first two literals
        self.watches[lits[0].not().index()].push(cref);
        self.watches[lits[1].not().index()].push(cref);

        self.clauses.push(clause);
        self.active_learned += 1;
        cref
    }

    /// Propagate unit clauses (BCP - Boolean Constraint Propagation)
    /// Returns the conflicting clause if a conflict occurs
    pub(super) fn propagate(&mut self) -> Option<ClauseRef> {
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;

            // Look at clauses watching !lit (they may become unit or conflict)
            // When lit is assigned TRUE, lit.not() becomes FALSE.
            // Clauses watching lit.not() were added to watches[lit.not().not().index()] = watches[lit.index()]
            // So we check watches[lit.index()] to find clauses where lit.not() is a watched literal.
            let watch_lit = lit.not(); // The literal that just became FALSE
            let watch_idx = lit.index(); // Index where we stored clauses watching lit.not()

            // Take ownership of watch list to avoid borrow issues
            let watches = std::mem::take(&mut self.watches[watch_idx]);
            let mut new_watches = Vec::with_capacity(watches.len());

            let mut conflict = None;

            for (watch_pos, &cref) in watches.iter().enumerate() {
                // Skip deleted clauses (lazily cleaned from watch lists)
                if self.clauses[cref.index()].deleted {
                    continue;
                }

                // Make sure the false literal (watch_lit) is in position 1
                if self.clauses[cref.index()].lits[0] == watch_lit {
                    self.clauses[cref.index()].lits.swap(0, 1);
                }
                debug_assert!(self.clauses[cref.index()].lits[1] == watch_lit);

                let first = self.clauses[cref.index()].lits[0];

                // If first literal is true, clause is satisfied
                if self.lit_value(first) == LBool::True {
                    new_watches.push(cref);
                    continue;
                }

                // Look for a new literal to watch
                let mut found_new_watch = false;
                let clause_len = self.clauses[cref.index()].lits.len();
                for i in 2..clause_len {
                    let lit_i = self.clauses[cref.index()].lits[i];
                    if self.lit_value(lit_i) != LBool::False {
                        // Found a non-false literal, swap it to position 1
                        self.clauses[cref.index()].lits.swap(1, i);
                        // Add to watch list of new watched literal
                        let new_watch_lit = self.clauses[cref.index()].lits[1];
                        self.watches[new_watch_lit.not().index()].push(cref);
                        found_new_watch = true;
                        break;
                    }
                }

                if found_new_watch {
                    continue;
                }

                // No new watch found - clause is unit or conflict
                new_watches.push(cref);

                if self.lit_value(first) == LBool::False {
                    // Conflict!
                    conflict = Some(cref);
                    // Copy remaining watches unconditionally (no duplicates in
                    // watch lists — each clause watches exactly two literals).
                    new_watches.extend_from_slice(&watches[watch_pos + 1..]);
                    break;
                }
                // Unit propagation
                self.set_lit(first, cref);
            }

            self.watches[watch_idx] = new_watches;

            if conflict.is_some() {
                return conflict;
            }
        }

        None
    }

    /// Analyze a conflict and learn a new clause
    /// Returns the learned clause, backtrack level, and origin clause indices
    pub(super) fn analyze(&mut self, conflict: ClauseRef) -> (Vec<Lit>, u32, Vec<u32>) {
        self.learnt_clause.clear();
        self.analyze_stack.clear();
        self.learnt_origins.clear();
        self.seen_origins.clear();

        // Start with the conflict clause
        let mut p = Lit(u32::MAX); // Sentinel value
        let mut counter = 0;
        let mut cref = conflict;

        // Use an index to traverse the trail backwards (don't pop - backtrack needs the trail)
        let mut trail_idx = self.trail.len();

        // First UIP (1UIP) scheme
        loop {
            // Collect origins from this clause using HashSet for O(1) deduplication
            let clause = &self.clauses[cref.index()];
            if clause.learned {
                // Learned clause: inherit its origins
                for &origin in &clause.origins {
                    if self.seen_origins.insert(origin) {
                        self.learnt_origins.push(origin);
                    }
                }
            } else {
                // Original clause: add its index as an origin
                let idx = cref.index();
                if idx < self.num_original_clauses {
                    let origin = usize_to_u32(idx, "clause origin index");
                    if self.seen_origins.insert(origin) {
                        self.learnt_origins.push(origin);
                    }
                }
            }

            // Bump clause activity if learned
            if self.clauses[cref.index()].learned {
                let clause_inc = self.clause_inc;
                self.clauses[cref.index()].activity += clause_inc;
            }

            // Process the reason clause
            let start = usize::from(p != Lit(u32::MAX));
            let clause_lits: Vec<Lit> = self.clauses[cref.index()].lits[start..].to_vec();

            for lit in clause_lits {
                let var = lit.var();
                let idx = var.index();

                if self.seen[idx] {
                    continue;
                }
                self.seen[idx] = true;

                let level = self.var_data[idx].level;

                if level == self.decision_level {
                    // This variable was assigned at the current level
                    counter += 1;
                } else if level > 0 {
                    // This variable was assigned at a previous level.
                    // Add the literal directly (it is FALSE at `level`). After
                    // backtracking, it stays FALSE, making the learned clause
                    // unit so BCP can propagate the asserting literal and
                    // reuse the clause in future search.
                    self.learnt_clause.push(lit);
                    self.vsids.bump(var);
                }
            }

            // Find the next literal to process (most recent on trail at current level)
            loop {
                trail_idx -= 1;
                p = self.trail[trail_idx];
                let var = p.var();
                if self.seen[var.index()] {
                    break;
                }
            }

            counter -= 1;
            self.seen[p.var().index()] = false;

            if counter == 0 {
                break;
            }

            // Get the reason for this assignment
            cref = self.var_data[p.var().index()].reason;

            // If we encounter a decision variable (invalid reason) before finding the UIP,
            // it means the decision variable must be the UIP (all conflict paths go through it).
            // This can happen when the decision variable is directly in the conflict clause
            // along with other current-level variables that were propagated from it.
            if !cref.is_valid() {
                // The decision variable is the UIP
                break;
            }
        }

        // The first literal is the asserting literal (negation of 1UIP)
        self.learnt_clause.insert(0, p.not());

        // Clear seen flags
        for lit in &self.learnt_clause {
            self.seen[lit.var().index()] = false;
        }

        // Bump activity of the asserting variable
        self.vsids.bump(p.var());

        // Find the backtrack level (second highest level in learned clause)
        let mut backtrack_level = 0u32;
        if self.learnt_clause.len() > 1 {
            let mut max_idx = 1;
            for i in 2..self.learnt_clause.len() {
                let level = self.var_data[self.learnt_clause[i].var().index()].level;
                if level > self.var_data[self.learnt_clause[max_idx].var().index()].level {
                    max_idx = i;
                }
            }
            // Swap to position 1 (second watched literal)
            self.learnt_clause.swap(1, max_idx);
            backtrack_level = self.var_data[self.learnt_clause[1].var().index()].level;
        }

        (
            self.learnt_clause.clone(),
            backtrack_level,
            self.learnt_origins.clone(),
        )
    }

    /// Collect unsat core for a conflict at decision level 0
    ///
    /// At level 0, all assignments come from unit clauses or unit propagation.
    /// We trace back all the reason clauses to collect the original clauses
    /// that contribute to the unsatisfiability.
    pub(super) fn collect_unsat_core_level0(&mut self, conflict: ClauseRef) -> Vec<u32> {
        let mut origins = Vec::new();
        let mut worklist = Vec::new();

        // Reuse self.seen_origins for O(1) deduplication (avoids per-call allocation)
        self.seen_origins.clear();

        // Helper function to add clause origins with O(1) HashSet deduplication
        fn add_clause_origins(
            cref: ClauseRef,
            origins: &mut Vec<u32>,
            seen_origins: &mut HashSet<u32>,
            clauses: &[Clause],
            num_orig: usize,
        ) {
            let clause = &clauses[cref.index()];
            if clause.learned {
                // Learned clause: inherit its origins
                for &origin in &clause.origins {
                    if seen_origins.insert(origin) {
                        origins.push(origin);
                    }
                }
            } else {
                // Original clause: add its index
                let idx = cref.index();
                if idx < num_orig {
                    let origin = usize_to_u32(idx, "clause origin index");
                    if seen_origins.insert(origin) {
                        origins.push(origin);
                    }
                }
            }
        }

        // Start with the conflict clause
        add_clause_origins(
            conflict,
            &mut origins,
            &mut self.seen_origins,
            &self.clauses,
            self.num_original_clauses,
        );

        // Add all literals from the conflict clause to the worklist
        // Mark them as seen to avoid duplicate processing
        for &lit in &self.clauses[conflict.index()].lits {
            let var = lit.var();
            if !self.seen[var.index()] {
                self.seen[var.index()] = true;
                worklist.push(var);
            }
        }

        // BFS: trace back through reason clauses
        while let Some(var) = worklist.pop() {
            // Check if this variable came from a unit clause during add_clause
            if let Some(unit_origin) = self.unit_clause_origins[var.index()] {
                if self.seen_origins.insert(unit_origin) {
                    origins.push(unit_origin);
                }
                // Unit clause variables have no reason clause to trace
                continue;
            }

            // Otherwise, check the reason clause from propagation
            let reason = self.var_data[var.index()].reason;
            if reason.is_valid() {
                add_clause_origins(
                    reason,
                    &mut origins,
                    &mut self.seen_origins,
                    &self.clauses,
                    self.num_original_clauses,
                );
                // Add literals from the reason clause (except the propagated one)
                for &lit in &self.clauses[reason.index()].lits {
                    let lit_var = lit.var();
                    if lit_var != var && !self.seen[lit_var.index()] {
                        self.seen[lit_var.index()] = true;
                        worklist.push(lit_var);
                    }
                }
            }
            // Note: If reason is invalid and no unit_clause_origin, the variable was
            // either a decision (shouldn't happen at level 0) or is the conflict literal
            // itself. In either case, we've already added the conflict clause origins.
        }

        // Clear seen flags
        for var in 0..self.num_vars {
            self.seen[var] = false;
        }

        origins
    }

    /// Delete low-quality learned clauses to bound memory usage.
    ///
    /// Keeps original clauses, locked clauses (current reasons for trail
    /// assignments), core clauses (LBD ≤ [`CORE_LBD`]), and unit learned
    /// clauses. Deletes the worst half of remaining candidates ranked by
    /// clause activity (lowest activity deleted first).
    ///
    /// After marking deletions, sweeps all watch lists to remove stale refs.
    pub(super) fn reduce_db(&mut self) {
        // Collect locked clause indices (reasons for current trail assignments)
        let locked: HashSet<u32> = self
            .trail
            .iter()
            .map(|lit| self.var_data[lit.var().index()].reason)
            .filter(|r| r.is_valid())
            .map(|r| r.raw())
            .collect();

        // Collect eligible candidates: learned, not deleted, not locked,
        // not core (LBD ≤ CORE_LBD), and multi-literal
        let mut candidates: Vec<usize> = self
            .clauses
            .iter()
            .enumerate()
            .filter(|(i, c)| {
                c.learned
                    && !c.deleted
                    && c.lits.len() > 1
                    && !locked.contains(&usize_to_u32(*i, "reduce_db clause index"))
                    && c.lbd > CORE_LBD
            })
            .map(|(i, _)| i)
            .collect();

        if candidates.is_empty() {
            self.reduce_db_count += 1;
            return;
        }

        // Sort by activity ascending (worst clauses first)
        candidates.sort_by(|&a, &b| {
            self.clauses[a]
                .activity
                .partial_cmp(&self.clauses[b].activity)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Delete bottom half
        let num_delete = candidates.len() / 2;
        let to_delete: HashSet<u32> = candidates[..num_delete]
            .iter()
            .map(|&i| usize_to_u32(i, "reduce_db delete index"))
            .collect();

        for &idx in &candidates[..num_delete] {
            self.clauses[idx].deleted = true;
        }
        self.active_learned -= num_delete;

        // Sweep watch lists to remove references to deleted clauses
        for wl in &mut self.watches {
            wl.retain(|cref| !to_delete.contains(&cref.raw()));
        }

        self.reduce_db_count += 1;
    }
}
