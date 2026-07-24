// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod inference;

use crate::cdcl::Lit;
use crate::smt::{
    SmtTerm, TermId, TheoryCheckResult, TheoryLemmaRequest, TheoryLiteral, TheorySolver,
};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// Array theory solver
///
/// Tracks array operations (select/store) and propagates implied equalities.
pub struct ArrayTheory {
    /// Mapping from term IDs to their structure (shared via Arc, #2308)
    terms: Arc<[SmtTerm]>,

    /// Select operations: maps (array_term, index_term) -> result_term
    pub(super) selects: BTreeMap<(TermId, TermId), TermId>,

    /// Store operations: maps store_term -> (array, index, value)
    pub(super) stores: BTreeMap<TermId, (TermId, TermId, TermId)>,

    /// Structurally known array terms from select/store syntax.
    structural_array_terms: HashSet<TermId>,

    /// Current array-typed term closure after direct Eq/Neq peer expansion.
    array_terms: HashSet<TermId>,

    /// Asserted equalities: (t1, t2, literal)
    pub(super) equalities: Vec<(TermId, TermId, Lit)>,

    /// Asserted disequalities: (t1, t2, literal)
    pub(super) disequalities: Vec<(TermId, TermId, Lit)>,

    /// O(1) equality lookup: maps canonical (min, max) pair to literal (#2353)
    eq_index: HashMap<(TermId, TermId), Lit>,

    /// O(1) disequality lookup: maps canonical (min, max) pair to literal (#2353)
    diseq_index: HashMap<(TermId, TermId), Lit>,

    /// Decision level trails for backtracking
    eq_trail: Vec<usize>,
    diseq_trail: Vec<usize>,

    /// Current decision level
    level: u32,

    /// Pending equality checks from axiom applications.
    /// Each entry: (t1, t2, explanation_lits) — the explanation contains
    /// only the specific assertion literals that triggered this axiom (#2330).
    pub(super) pending_equalities: Vec<(TermId, TermId, Vec<Lit>)>,

    /// Deduplication set for pending equalities (#2330).
    /// Prevents the same (t1, t2) equality from being queued multiple times
    /// across repeated `apply_row_same_index`/`apply_row_diff_index` calls.
    /// Uses canonical (min, max) key ordering.
    pending_set: HashSet<(TermId, TermId)>,

    /// Pending extensionality lemma requests for asserted array disequalities.
    pub(super) pending_extensionality: Vec<(TermId, TermId, Lit)>,

    /// Deduplication set for pending extensionality requests.
    pub(super) pending_extensionality_set: HashSet<(TermId, TermId)>,
}

impl ArrayTheory {
    /// Create a new array theory solver
    pub fn new() -> Self {
        ArrayTheory {
            terms: Arc::from(Vec::<SmtTerm>::new()),
            selects: BTreeMap::new(),
            stores: BTreeMap::new(),
            structural_array_terms: HashSet::new(),
            array_terms: HashSet::new(),
            equalities: Vec::new(),
            disequalities: Vec::new(),
            eq_index: HashMap::new(),
            diseq_index: HashMap::new(),
            eq_trail: vec![0],
            diseq_trail: vec![0],
            level: 0,
            pending_equalities: Vec::new(),
            pending_set: HashSet::new(),
            pending_extensionality: Vec::new(),
            pending_extensionality_set: HashSet::new(),
        }
    }

    /// Set the terms (called by SMT solver or tests).
    /// Accepts both `Vec<SmtTerm>` and `Arc<[SmtTerm]>` via `Into`.
    pub fn set_terms(&mut self, terms: impl Into<Arc<[SmtTerm]>>) {
        self.terms = terms.into();
        self.analyze_terms();
    }

    /// Analyze terms to extract select/store structure
    fn analyze_terms(&mut self) {
        self.selects.clear();
        self.stores.clear();
        self.structural_array_terms.clear();

        for (idx, term) in self.terms.iter().enumerate() {
            let term_id = TermId::new(
                u32::try_from(idx).expect("invariant: array theory term index fits in u32"),
            );

            if let SmtTerm::App(name, args) = term {
                match name.name() {
                    "select" if args.len() == 2 => {
                        // select(array, index) -> value
                        let array = args[0];
                        let index = args[1];
                        self.selects.insert((array, index), term_id);
                        self.structural_array_terms.insert(array);
                    }
                    "store" if args.len() == 3 => {
                        // store(array, index, value) -> new_array
                        let array = args[0];
                        let index = args[1];
                        let value = args[2];
                        self.stores.insert(term_id, (array, index, value));
                        self.structural_array_terms.insert(array);
                        self.structural_array_terms.insert(term_id);
                    }
                    _ => {}
                }
            }
        }
        self.recompute_array_term_closure();
    }
}

impl Default for ArrayTheory {
    fn default() -> Self {
        Self::new()
    }
}

impl TheorySolver for ArrayTheory {
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        match theory_lit {
            TheoryLiteral::Eq(t1, t2) => {
                self.equalities.push((*t1, *t2, lit));
                let key = if t1.raw() < t2.raw() {
                    (*t1, *t2)
                } else {
                    (*t2, *t1)
                };
                self.eq_index.insert(key, lit);
                self.refresh_extensionality_requests();

                // After asserting equality, check array axioms
                if let result @ TheoryCheckResult::Conflict(_) = self.apply_row_same_index() {
                    return result;
                }
                if let result @ TheoryCheckResult::Conflict(_) = self.apply_row_diff_index() {
                    return result;
                }

                TheoryCheckResult::Consistent
            }
            TheoryLiteral::Neq(t1, t2) => {
                self.disequalities.push((*t1, *t2, lit));
                let key = if t1.raw() < t2.raw() {
                    (*t1, *t2)
                } else {
                    (*t2, *t1)
                };
                self.diseq_index.insert(key, lit);
                self.refresh_extensionality_requests();

                // After asserting disequality, check array axioms
                if let result @ TheoryCheckResult::Conflict(_) = self.apply_row_same_index() {
                    return result;
                }
                if let result @ TheoryCheckResult::Conflict(_) = self.apply_row_diff_index() {
                    return result;
                }

                TheoryCheckResult::Consistent
            }
            // Other literals are not handled by array theory
            _ => TheoryCheckResult::Consistent,
        }
    }

    fn check(&self) -> TheoryCheckResult {
        // Full consistency check is already done incrementally
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, level: u32) {
        if level >= self.level {
            return;
        }

        // Restore equalities and disequalities to the state at target level
        let eq_limit = self.eq_trail.get(level as usize + 1).copied().unwrap_or(0);
        let diseq_limit = self
            .diseq_trail
            .get(level as usize + 1)
            .copied()
            .unwrap_or(0);

        self.equalities.truncate(eq_limit);
        self.disequalities.truncate(diseq_limit);

        // Rebuild O(1) lookup indices from truncated trails (#2353)
        self.eq_index.clear();
        for &(t1, t2, lit) in &self.equalities {
            let key = if t1.raw() < t2.raw() {
                (t1, t2)
            } else {
                (t2, t1)
            };
            self.eq_index.insert(key, lit);
        }
        self.diseq_index.clear();
        for &(t1, t2, lit) in &self.disequalities {
            let key = if t1.raw() < t2.raw() {
                (t1, t2)
            } else {
                (t2, t1)
            };
            self.diseq_index.insert(key, lit);
        }

        self.eq_trail.truncate(level as usize + 1);
        self.diseq_trail.truncate(level as usize + 1);
        // Clear pending equalities from reverted axiom applications (#2313, #2330)
        self.pending_equalities.clear();
        self.pending_set.clear();
        self.pending_extensionality.clear();
        self.pending_extensionality_set.clear();
        self.recompute_array_term_closure();
        self.level = level;
    }

    fn push(&mut self) {
        self.level += 1;
        self.eq_trail.push(self.equalities.len());
        self.diseq_trail.push(self.disequalities.len());
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn name(&self) -> &'static str {
        "Arrays"
    }

    fn set_terms(&mut self, terms: Arc<[SmtTerm]>) {
        // Delegate to inherent method which handles analyze_terms()
        ArrayTheory::set_terms(self, terms);
    }

    fn reset(&mut self) {
        // Clear assertion state directly (#2386). The DPLL(T) loop no longer
        // calls push() before assertions, so theories operate at level 0 and
        // reset() must clear all assertion-derived state without relying on
        // backtrack(). Structural state from set_terms/analyze_terms persists.
        self.equalities.clear();
        self.disequalities.clear();
        self.eq_index.clear();
        self.diseq_index.clear();
        self.eq_trail.clear();
        self.eq_trail.push(0);
        self.diseq_trail.clear();
        self.diseq_trail.push(0);
        self.level = 0;
        self.pending_equalities.clear();
        self.pending_set.clear();
        self.pending_extensionality.clear();
        self.pending_extensionality_set.clear();
        self.array_terms = self.structural_array_terms.clone();
    }

    // assert_shared_equality/disequality: uses default delegation to
    // assert_literal (Eq/Neq arms handle it correctly). No override needed;
    // keeps file under 500-line limit (#2386).

    fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        ArrayTheory::drain_deduced_equalities(self)
    }

    fn drain_lemma_requests(&mut self) -> Vec<TheoryLemmaRequest> {
        ArrayTheory::drain_lemma_requests(self)
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let stats = self.stats();
        vec![
            ("array_selects", stats.num_selects as u64),
            ("array_stores", stats.num_stores as u64),
            ("array_equalities", stats.num_equalities as u64),
            ("array_disequalities", stats.num_disequalities as u64),
            (
                "array_pending_equalities",
                self.pending_equalities.len() as u64,
            ),
        ]
    }
}
