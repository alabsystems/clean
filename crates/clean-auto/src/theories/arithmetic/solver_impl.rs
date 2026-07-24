// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::ArithmeticTheory;
use crate::cdcl::Lit;
use crate::smt::{SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};
use std::sync::Arc;

impl Default for ArithmeticTheory {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for ArithmeticTheory {
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        match theory_lit {
            TheoryLiteral::Lt(t1, t2) => self.handle_comparison(*t1, *t2, false, lit),
            TheoryLiteral::Le(t1, t2) => self.handle_comparison(*t1, *t2, true, lit),
            TheoryLiteral::Eq(t1, t2) => {
                // t1 = t2 ≡ t1 ≤ t2 ∧ t2 ≤ t1 (#2311)
                let upper = self.handle_comparison(*t1, *t2, true, lit);
                if matches!(upper, TheoryCheckResult::Conflict(_)) {
                    return upper;
                }
                self.handle_comparison(*t2, *t1, true, lit)
            }
            // Neq requires disjunctive reasoning (t1 < t2 ∨ t2 < t1),
            // handled by EqualityTheory via disequalities
            _ => TheoryCheckResult::Consistent,
        }
    }

    fn check(&self) -> TheoryCheckResult {
        // Incrementally complete: check_and_repair() runs in assert_literal,
        // so the assignment is already consistent here. Returning Conflict(vec![])
        // would cause false UNSAT (#2292). check_and_repair() needs &mut self.
        //
        // Return Unknown when overflow_corrupted (#2384, #2399): the tableau
        // has partially-modified rows so we cannot claim Consistent.
        if self.overflow_corrupted {
            return TheoryCheckResult::Unknown;
        }
        debug_assert!(
            self.is_consistent(),
            "incremental checker missed a bound violation (bug in check_and_repair)"
        );
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, level: u32) {
        if level >= self.level {
            return;
        }

        // Undo bounds added after target level
        while let Some(&(bound_level, var, is_lower, ref old_bound)) = self.bound_trail.last() {
            if bound_level <= level {
                break;
            }

            if is_lower {
                match old_bound {
                    Some(b) => {
                        self.lower_bounds.insert(var, b.clone());
                    }
                    None => {
                        self.lower_bounds.remove(&var);
                    }
                }
            } else {
                match old_bound {
                    Some(b) => {
                        self.upper_bounds.insert(var, b.clone());
                    }
                    None => {
                        self.upper_bounds.remove(&var);
                    }
                }
            }

            self.bound_trail.pop();
        }

        // Restore tableau, assignment, variable counter, and term_to_var (#2296, #2312)
        if let Some(tableau) = self.tableau_trail.get(level as usize).cloned() {
            self.tableau = tableau;
            self.rebuild_basic_var_index();
        }
        if let Some(assignment) = self.assignment_trail.get(level as usize).cloned() {
            self.assignment = assignment;
        }
        if let Some(&next_id) = self.next_id_trail.get(level as usize) {
            self.next_id = next_id;
        }
        // Restore term_to_var by removing entries added after the saved next_id (#2406).
        // This is O(added_entries) instead of O(total) from full HashMap clone.
        if let Some(&saved_next_id) = self.term_to_var_trail.get(level as usize) {
            self.term_to_var.retain(|_, var| var.raw() < saved_next_id);
        }
        self.tableau_trail.truncate(level as usize);
        self.assignment_trail.truncate(level as usize);
        self.next_id_trail.truncate(level as usize);
        self.term_to_var_trail.truncate(level as usize);

        // Restore overflow_corrupted flag (#2399)
        if let Some(&oc) = self.overflow_corrupted_trail.get(level as usize) {
            self.overflow_corrupted = oc;
        }
        self.overflow_corrupted_trail.truncate(level as usize);

        // Pending deductions are invalid after backtrack — model changed (#2364)
        self.pending_deduced.clear();
        self.deduced_set.clear();

        self.level = level;
    }

    fn push(&mut self) {
        // Snapshot tableau, assignment, variable counter, and overflow flag
        // (#2296, #2312, #2399). term_to_var uses trail-based undo via
        // saved next_id instead of full HashMap clone (#2406).
        self.tableau_trail.push(self.tableau.clone());
        self.assignment_trail.push(self.assignment.clone());
        self.next_id_trail.push(self.next_id);
        self.term_to_var_trail.push(self.next_id);
        self.overflow_corrupted_trail.push(self.overflow_corrupted);
        self.level += 1;
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn name(&self) -> &'static str {
        "LRA"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {
        // ArithmeticTheory uses term_to_var mapping populated via assert_literal,
        // not the shared terms array. No-op is correct (#2391).
    }

    fn internalize_atom(&mut self, theory_lit: &TheoryLiteral) {
        match theory_lit {
            TheoryLiteral::Lt(t1, t2) | TheoryLiteral::Le(t1, t2) | TheoryLiteral::Eq(t1, t2) => {
                // Pre-allocate simplex variables so assert_literal skips
                // the HashMap insert path during the hot loop (#2386).
                self.get_or_create_var(*t1);
                self.get_or_create_var(*t2);
                self.record_reset_base_term(*t1);
                self.record_reset_base_term(*t2);
            }
            _ => {} // Neq handled by EUF; Bool not arithmetic
        }
    }

    fn reset(&mut self) {
        // Restore assertion state via snapshot-based backtrack if above level 0.
        // backtrack(0) restores tableau, assignment, next_id, term_to_var, and
        // overflow_corrupted from level-0 snapshots (#2296, #2312, #2399).
        if self.level > 0 {
            self.backtrack(0);
        }
        self.tableau.clear();
        self.basic_var_index.clear();
        self.assignment.clear();
        self.lower_bounds.clear();
        self.upper_bounds.clear();
        self.next_id = 0;
        self.term_to_var.clear();
        for term_id in self.reset_base_terms.clone() {
            self.get_or_create_var(term_id);
        }
        self.level = 0;
        self.overflow_corrupted = false;
        // Clear trail infrastructure for a fresh solve cycle.
        self.bound_trail.clear();
        self.tableau_trail.clear();
        self.assignment_trail.clear();
        self.next_id_trail.clear();
        self.term_to_var_trail.clear();
        self.overflow_corrupted_trail.clear();
        // Clear pending state (already cleared by backtrack, but safe from level 0).
        self.pending_deduced.clear();
        self.deduced_set.clear();
    }

    fn assert_shared_equality(&mut self, t1: TermId, t2: TermId, reason: Lit) -> TheoryCheckResult {
        // t1 = t2 ≡ t1 ≤ t2 ∧ t2 ≤ t1 (#2311)
        let upper = self.handle_comparison(t1, t2, true, reason);
        if matches!(upper, TheoryCheckResult::Conflict(_)) {
            return upper;
        }
        self.handle_comparison(t2, t1, true, reason)
    }

    fn assert_shared_disequality(
        &mut self,
        _t1: TermId,
        _t2: TermId,
        _reason: Lit,
    ) -> TheoryCheckResult {
        // Neq requires disjunctive reasoning (t1 < t2 ∨ t2 < t1),
        // handled by EqualityTheory via disequalities
        TheoryCheckResult::Consistent
    }

    fn prepare_deduced_equalities(&mut self) {
        self.detect_model_equalities();
    }

    fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        ArithmeticTheory::drain_deduced_equalities(self)
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let stats = self.stats();
        vec![
            ("arith_vars", stats.num_vars as u64),
            ("arith_rows", stats.num_rows as u64),
            ("arith_lower_bounds", stats.num_lower_bounds as u64),
            ("arith_upper_bounds", stats.num_upper_bounds as u64),
            ("arith_pending_deduced", self.pending_deduced.len() as u64),
        ]
    }

    fn suggest_phase(&self, theory_lit: &TheoryLiteral) -> Option<bool> {
        match theory_lit {
            TheoryLiteral::Lt(lhs, rhs) => self.suggest_relation_phase(*lhs, *rhs, true),
            TheoryLiteral::Le(lhs, rhs) => self.suggest_relation_phase(*lhs, *rhs, false),
            TheoryLiteral::Eq(lhs, rhs) => self
                .current_term_value(*lhs)
                .zip(self.current_term_value(*rhs))
                .map(|(lhs_value, rhs_value)| lhs_value == rhs_value),
            _ => None,
        }
    }
}
