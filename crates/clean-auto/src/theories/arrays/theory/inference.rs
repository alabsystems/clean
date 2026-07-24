// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::ArrayTheory;
use crate::cdcl::Lit;
use crate::smt::{TermId, TheoryCheckResult, TheoryLemmaRequest};

impl ArrayTheory {
    fn canonical_pair(t1: TermId, t2: TermId) -> (TermId, TermId) {
        if t1.raw() <= t2.raw() {
            (t1, t2)
        } else {
            (t2, t1)
        }
    }

    pub(super) fn recompute_array_term_closure(&mut self) {
        self.array_terms.clone_from(&self.structural_array_terms);

        loop {
            let mut changed = false;
            for &(t1, t2, _) in self.equalities.iter().chain(self.disequalities.iter()) {
                let t1_known = self.array_terms.contains(&t1);
                let t2_known = self.array_terms.contains(&t2);
                if t1_known == t2_known {
                    continue;
                }
                changed |= self.array_terms.insert(if t1_known { t2 } else { t1 });
            }
            if !changed {
                break;
            }
        }
    }

    fn queue_extensionality_request(&mut self, lhs: TermId, rhs: TermId, diseq_reason: Lit) {
        if lhs == rhs {
            return;
        }
        let pair = Self::canonical_pair(lhs, rhs);
        if self.pending_extensionality_set.insert(pair) {
            self.pending_extensionality
                .push((pair.0, pair.1, diseq_reason));
        }
    }

    pub(super) fn refresh_extensionality_requests(&mut self) {
        self.recompute_array_term_closure();

        let mut to_queue = Vec::new();
        for &(lhs, rhs, diseq_reason) in &self.disequalities {
            if self.array_terms.contains(&lhs) && self.array_terms.contains(&rhs) {
                to_queue.push((lhs, rhs, diseq_reason));
            }
        }

        for (lhs, rhs, diseq_reason) in to_queue {
            self.queue_extensionality_request(lhs, rhs, diseq_reason);
        }
    }

    /// Apply read-over-write axiom 1: select(store(a, i, v), i) = v
    ///
    /// When we have select(s, j) where s = store(a, i, v):
    /// - If i = j (indices equal), then select(s, j) = v
    pub(super) fn apply_row_same_index(&mut self) -> TheoryCheckResult {
        // Collect potential ROW-same applications
        let mut to_check = Vec::new();

        for (&(array_term, select_index), &select_result) in &self.selects {
            // Check if array_term is a store operation
            if let Some(&(_, store_index, store_value)) = self.stores.get(&array_term) {
                // select(store(a, i, v), j) with this select having index j
                // If i = j (same index), then select result should equal v
                to_check.push((select_index, store_index, select_result, store_value));
            }
        }

        // Check each potential ROW-same
        for (select_idx, store_idx, select_result, store_value) in to_check {
            // Check if indices are asserted equal
            if self.are_equal(select_idx, store_idx) {
                // Axiom 1: select(store(a, i, v), i) = v
                // Check if select_result = store_value is consistent
                if !self.are_equal(select_result, store_value) {
                    // Need to check: is select_result ≠ store_value asserted?
                    if self.are_disequal(select_result, store_value) {
                        // Conflict! ROW-same says they should be equal,
                        // but disequality is asserted.
                        // Only return if builder produced a non-empty conflict;
                        // if the #2389 guard returned Consistent, continue
                        // checking remaining entries for valid conflicts.
                        let result = self.build_row_same_conflict(
                            select_idx,
                            store_idx,
                            select_result,
                            store_value,
                        );
                        if let TheoryCheckResult::Conflict(_) = &result {
                            return result;
                        }
                    }
                    // Otherwise, we should propagate select_result = store_value.
                    // Dedup: skip if already queued at this decision level (#2330).
                    let dedup_key = Self::canonical_pair(select_result, store_value);
                    if self.pending_set.contains(&dedup_key) {
                        continue;
                    }
                    // Explanation: only the index equality literal (#2330).
                    let mut explanation = Vec::new();
                    let eq_key = Self::canonical_pair(select_idx, store_idx);
                    if let Some(&lit) = self.eq_index.get(&eq_key) {
                        explanation.push(lit);
                    }
                    self.pending_set.insert(dedup_key);
                    self.pending_equalities
                        .push((select_result, store_value, explanation));
                }
            }
        }

        TheoryCheckResult::Consistent
    }

    /// Apply read-over-write axiom 2: i ≠ j → select(store(a, i, v), j) = select(a, j)
    ///
    /// When we have select(s, j) where s = store(a, i, v) and i ≠ j:
    /// - select(s, j) should equal select(a, j)
    pub(super) fn apply_row_diff_index(&mut self) -> TheoryCheckResult {
        let mut to_check = Vec::new();

        for (&(array_term, select_index), &select_result) in &self.selects {
            if let Some(&(base_array, store_index, _)) = self.stores.get(&array_term) {
                // select(store(a, i, v), j)
                // If i ≠ j, then select(store(a, i, v), j) = select(a, j)
                to_check.push((select_index, store_index, select_result, base_array));
            }
        }

        for (select_idx, store_idx, select_result, base_array) in to_check {
            // Check if indices are asserted disequal
            if self.are_disequal(select_idx, store_idx) {
                // Axiom 2 applies: select(store(a, i, v), j) = select(a, j)
                // Look up select(base_array, select_idx)
                if let Some(&base_select) = self.selects.get(&(base_array, select_idx)) {
                    // select_result should equal base_select
                    if !self.are_equal(select_result, base_select) {
                        if self.are_disequal(select_result, base_select) {
                            // Same pattern as apply_row_same_index: only
                            // return on non-empty conflict (#2389).
                            let result = self.build_row_diff_conflict(
                                select_idx,
                                store_idx,
                                select_result,
                                base_select,
                            );
                            if let TheoryCheckResult::Conflict(_) = &result {
                                return result;
                            }
                        }
                        // Dedup: skip if already queued at this decision level (#2330).
                        let dedup_key = Self::canonical_pair(select_result, base_select);
                        if self.pending_set.contains(&dedup_key) {
                            continue;
                        }
                        // Explanation: only the index disequality literal (#2330).
                        let mut explanation = Vec::new();
                        let diseq_key = Self::canonical_pair(select_idx, store_idx);
                        if let Some(&lit) = self.diseq_index.get(&diseq_key) {
                            explanation.push(lit);
                        }
                        self.pending_set.insert(dedup_key);
                        self.pending_equalities
                            .push((select_result, base_select, explanation));
                    }
                }
            }
        }

        TheoryCheckResult::Consistent
    }

    /// Check if two terms are equal (based on asserted equalities).
    /// O(1) via HashMap lookup with canonical (min, max) pair key (#2353).
    pub(super) fn are_equal(&self, t1: TermId, t2: TermId) -> bool {
        if t1 == t2 {
            return true;
        }
        self.eq_index.contains_key(&Self::canonical_pair(t1, t2))
    }

    /// Check if two terms are disequal (based on asserted disequalities).
    /// O(1) via HashMap lookup with canonical (min, max) pair key (#2353).
    pub(super) fn are_disequal(&self, t1: TermId, t2: TermId) -> bool {
        self.diseq_index.contains_key(&Self::canonical_pair(t1, t2))
    }

    /// Build conflict clause for ROW-same violation.
    /// Returns `Conflict(lits)` or `Consistent` if no explanation literals
    /// found (#2389 guard — currently unreachable, see inline comment).
    fn build_row_same_conflict(
        &self,
        select_idx: TermId,
        store_idx: TermId,
        select_result: TermId,
        store_value: TermId,
    ) -> TheoryCheckResult {
        // Conflict: select_idx = store_idx implies select_result = store_value,
        // but select_result ≠ store_value was asserted
        let mut conflict_lits = Vec::new();

        // Find the equality literal for indices (O(1) via eq_index, #2353)
        if let Some(&lit) = self
            .eq_index
            .get(&Self::canonical_pair(select_idx, store_idx))
        {
            conflict_lits.push(lit);
        }

        // Find the disequality literal for results (O(1) via diseq_index, #2353)
        if let Some(&lit) = self
            .diseq_index
            .get(&Self::canonical_pair(select_result, store_value))
        {
            conflict_lits.push(lit);
        }

        // #2389: Never return Conflict(vec![]) — soundness > completeness.
        // Currently unreachable: the caller's `are_disequal` check guarantees
        // the diseq_index entry exists, so at least one literal is always
        // present. Guard retained defensively for future code changes.
        // See ArithmeticTheory at arithmetic/mod.rs:395 for the same pattern.
        if conflict_lits.is_empty() {
            return TheoryCheckResult::Consistent;
        }

        TheoryCheckResult::Conflict(conflict_lits)
    }

    /// Build conflict clause for ROW-diff violation.
    /// Same return contract as `build_row_same_conflict` (#2389).
    fn build_row_diff_conflict(
        &self,
        select_idx: TermId,
        store_idx: TermId,
        select_result: TermId,
        base_select: TermId,
    ) -> TheoryCheckResult {
        let mut conflict_lits = Vec::new();

        // Find disequality literal for indices (O(1) via diseq_index, #2353)
        if let Some(&lit) = self
            .diseq_index
            .get(&Self::canonical_pair(select_idx, store_idx))
        {
            conflict_lits.push(lit);
        }

        // Find disequality literal for results (O(1) via diseq_index, #2353)
        if let Some(&lit) = self
            .diseq_index
            .get(&Self::canonical_pair(select_result, base_select))
        {
            conflict_lits.push(lit);
        }

        // #2389: Never return Conflict(vec![]) — soundness > completeness.
        // Currently unreachable (see build_row_same_conflict doc comment).
        if conflict_lits.is_empty() {
            return TheoryCheckResult::Consistent;
        }

        TheoryCheckResult::Conflict(conflict_lits)
    }

    /// Drain pending equalities implied by array axioms (#2294, #2330).
    /// `pending_set` is NOT cleared here — persists until `backtrack`.
    pub fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        std::mem::take(&mut self.pending_equalities)
    }

    /// Drain pending extensionality requests discovered from asserted array
    /// disequalities. The dedup set persists until backtrack/reset.
    pub fn drain_lemma_requests(&mut self) -> Vec<TheoryLemmaRequest> {
        std::mem::take(&mut self.pending_extensionality)
            .into_iter()
            .map(
                |(lhs, rhs, diseq_reason)| TheoryLemmaRequest::ArrayExtensionality {
                    lhs,
                    rhs,
                    diseq_reason,
                },
            )
            .collect()
    }
}
