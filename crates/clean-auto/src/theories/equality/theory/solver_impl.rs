// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::EqualityTheory;
use crate::cdcl::Lit;
use crate::egraph::EGraph;
use crate::proof::ProofTrace;
use crate::smt::{SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};
use std::sync::Arc;

impl Default for EqualityTheory {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for EqualityTheory {
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        match theory_lit {
            TheoryLiteral::Eq(t1, t2) => self.assert_equality(*t1, *t2, lit),
            TheoryLiteral::Neq(t1, t2) => self.assert_disequality(*t1, *t2, lit),
            _ => TheoryCheckResult::Consistent,
        }
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, level: u32) {
        if level >= self.level {
            return;
        }

        self.pending_deduced.clear();
        self.proof_forest.backtrack(level);
        // Canonicals change after restoring E-graph snapshot (#2406)
        self.class_members_valid = false;

        let diseq_limit = self.diseq_trail[level as usize + 1];
        self.disequalities.truncate(diseq_limit);

        let lvl = level as usize;
        self.egraph_trail.truncate(lvl + 1);
        if let Some(snapshot) = self.egraph_trail.pop() {
            self.egraph = snapshot;
        }
        self.term_to_eclass_trail.truncate(lvl + 1);
        if let Some(snapshot) = self.term_to_eclass_trail.pop() {
            self.term_to_eclass = snapshot;
        }
        self.proof_trace_len_trail.truncate(lvl + 1);
        if let Some(saved_len) = self.proof_trace_len_trail.pop() {
            self.proof_trace.truncate(saved_len);
        }

        // Restore term_to_hypothesis via trail-based undo (#2406).
        // Replay undo entries in reverse to restore overwritten values.
        self.term_to_hypothesis_trail.truncate(lvl + 1);
        if let Some(saved_undo_len) = self.term_to_hypothesis_trail.pop() {
            for (key, old_value) in self.term_to_hypothesis_undo.drain(saved_undo_len..).rev() {
                match old_value {
                    Some(v) => {
                        self.term_to_hypothesis.insert(key, v);
                    }
                    None => {
                        self.term_to_hypothesis.remove(&key);
                    }
                }
            }
        }

        self.equality_trail.truncate(level as usize + 1);
        self.diseq_trail.truncate(level as usize + 1);
        self.level = level;
    }

    fn push(&mut self) {
        self.egraph_trail.push(self.egraph.clone());
        self.term_to_eclass_trail.push(self.term_to_eclass.clone());
        self.proof_trace_len_trail.push(self.proof_trace.len());
        // Trail-based undo for term_to_hypothesis: save current undo trail
        // position instead of cloning the full HashMap (#2406).
        self.term_to_hypothesis_trail
            .push(self.term_to_hypothesis_undo.len());
        self.level += 1;
        self.equality_trail.push(Vec::new());
        self.diseq_trail.push(self.disequalities.len());
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn name(&self) -> &'static str {
        "EUF"
    }

    fn set_terms(&mut self, terms: Arc<[SmtTerm]>) {
        EqualityTheory::set_terms(self, terms);
    }

    fn internalize_atom(&mut self, theory_lit: &TheoryLiteral) {
        match theory_lit {
            TheoryLiteral::Eq(t1, t2) | TheoryLiteral::Neq(t1, t2) => {
                self.get_or_create_eclass(*t1);
                self.get_or_create_eclass(*t2);
                self.record_reset_base_term(*t1);
                self.record_reset_base_term(*t2);
            }
            _ => {}
        }
    }

    fn reset(&mut self) {
        if self.level > 0 {
            self.backtrack(0);
        }
        self.egraph = EGraph::new();
        self.term_to_eclass.clear();
        // Invalidate before replaying base terms so get_or_create_eclass
        // does not try to maintain a stale class_members_buf (#2406).
        self.class_members_valid = false;
        let reset_base_terms = self.reset_base_terms.clone();
        for term_id in reset_base_terms {
            self.get_or_create_eclass(term_id);
        }
        self.disequalities.clear();
        self.level = 0;
        self.proof_trace = ProofTrace::new();
        self.proof_forest = crate::proof::ProofForest::new();
        self.term_to_hypothesis = self.reset_base_term_to_hypothesis.clone();
        self.equality_trail.clear();
        self.equality_trail.push(Vec::new());
        self.diseq_trail.clear();
        self.diseq_trail.push(0);
        self.egraph_trail.clear();
        self.term_to_eclass_trail.clear();
        self.proof_trace_len_trail.clear();
        self.term_to_hypothesis_trail.clear();
        self.term_to_hypothesis_undo.clear();
        self.pending_deduced.clear();
    }

    fn assert_shared_equality(&mut self, t1: TermId, t2: TermId, reason: Lit) -> TheoryCheckResult {
        self.assert_equality(t1, t2, reason)
    }

    fn assert_shared_disequality(
        &mut self,
        t1: TermId,
        t2: TermId,
        reason: Lit,
    ) -> TheoryCheckResult {
        self.assert_disequality(t1, t2, reason)
    }

    fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        EqualityTheory::drain_deduced_equalities(self)
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let stats = self.stats();
        let explanation_stats = self.explanation_stats();
        vec![
            ("euf_eclasses", stats.num_eclasses as u64),
            ("euf_enodes", stats.num_enodes as u64),
            ("euf_disequalities", stats.num_disequalities as u64),
            ("euf_terms", stats.num_terms as u64),
            ("euf_explanation_precise", explanation_stats.precise_count),
            ("euf_explanation_fallback", explanation_stats.fallback_count),
        ]
    }

    fn suggest_phase(&self, theory_lit: &TheoryLiteral) -> Option<bool> {
        let TheoryLiteral::Eq(t1, t2) = theory_lit else {
            return None;
        };
        if self.are_equal(*t1, *t2) {
            return Some(true);
        }
        let has_disequality = self
            .disequalities
            .iter()
            .any(|(lhs, rhs, _)| (*lhs == *t1 && *rhs == *t2) || (*lhs == *t2 && *rhs == *t1));
        if has_disequality {
            return Some(false);
        }
        None
    }
}
