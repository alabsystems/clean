// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::ArithmeticTheory;
use crate::cdcl::Lit;
use crate::smt::TermId;
use crate::theories::rational::DeltaRational;
use std::collections::{HashMap, HashSet};

impl ArithmeticTheory {
    pub(super) fn current_term_value(&self, term_id: TermId) -> Option<DeltaRational> {
        let var = *self.term_to_var.get(&term_id)?;
        self.assignment.get(&var).copied()
    }

    pub(super) fn suggest_relation_phase(
        &self,
        lhs: TermId,
        rhs: TermId,
        strict: bool,
    ) -> Option<bool> {
        let lhs_value = self.current_term_value(lhs)?;
        let rhs_value = self.current_term_value(rhs)?;
        Some(if strict {
            lhs_value < rhs_value
        } else {
            lhs_value <= rhs_value
        })
    }

    /// Detect equalities between term variables implied by current model (#2364).
    ///
    /// After simplex produces a consistent assignment, groups term variables by
    /// their model value. For each group with 2+ terms where at least one is
    /// constrained (appears in bounds or tableau), emits pairwise equalities.
    ///
    /// This is the standard model-based Nelson-Oppen theory combination approach:
    /// report equalities that hold in the current model so EUF can check
    /// congruence consequences.
    pub(super) fn detect_model_equalities(&mut self) {
        if self.term_to_var.len() < 2 {
            return;
        }

        // Build set of constrained variables (appear in bounds or tableau rows).
        // Unconstrained variables default to 0 and would produce spurious equalities.
        let mut constrained = HashSet::new();
        for &var in self.lower_bounds.keys() {
            constrained.insert(var);
        }
        for &var in self.upper_bounds.keys() {
            constrained.insert(var);
        }
        for row in &self.tableau {
            constrained.insert(row.basic_var);
            for &var in row.coeffs.keys() {
                constrained.insert(var);
            }
        }

        // Group constrained term variables by model value
        let mut value_groups: HashMap<DeltaRational, Vec<TermId>> = HashMap::new();
        for (&term_id, &var) in &self.term_to_var {
            if !constrained.contains(&var) {
                continue;
            }
            if let Some(&val) = self.assignment.get(&var) {
                value_groups.entry(val).or_default().push(term_id);
            }
        }

        // Collect all active bound reasons for explanation (conservative over-approximation)
        let all_reasons: Vec<Lit> = self
            .lower_bounds
            .values()
            .chain(self.upper_bounds.values())
            .map(|b| b.reason)
            .collect();

        // Emit pairwise equalities for same-value groups
        for terms in value_groups.values() {
            if terms.len() < 2 {
                continue;
            }
            let mut sorted = terms.clone();
            sorted.sort_by_key(|t| t.raw());

            for i in 0..sorted.len() {
                for j in (i + 1)..sorted.len() {
                    let (t1, t2) = (sorted[i], sorted[j]);
                    // O(1) dedup via HashSet instead of O(n) linear scan (#2441).
                    // Sorted by raw ID, so (t1, t2) is already normalized for i < j.
                    let key = (t1, t2);
                    if self.deduced_set.insert(key) {
                        self.pending_deduced.push((t1, t2, all_reasons.clone()));
                    }
                }
            }
        }
    }

    /// Drain deduced equalities for Nelson-Oppen forwarding (#2364).
    ///
    /// Returns `(t1, t2, explanation)` triples where `explanation` is the
    /// set of bound assertion literals that contribute to the equality.
    ///
    /// Does NOT clear `deduced_set` — the set accumulates across
    /// prepare/drain cycles within one `check_theories_attributed` batch
    /// so the same equality pair is not re-emitted (#2366). Cleared on
    /// backtrack boundaries only.
    pub fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        std::mem::take(&mut self.pending_deduced)
    }
}
