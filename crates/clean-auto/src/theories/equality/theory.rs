// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! EqualityTheory struct and implementations
//!
//! This module implements the equality/uninterpreted functions (EUF) theory solver
//! using the E-graph data structure for congruence closure.
//!
//! # Theory of Equality with Uninterpreted Functions (EUF)
//!
//! EUF handles:
//! - Equality constraints: `x = y`
//! - Disequality constraints: `x ≠ y`
//! - Function congruence: `x = y → f(x) = f(y)`
//!
//! The E-graph maintains equivalence classes and performs congruence closure
//! to derive implied equalities.
//!
//! # Conflict Detection
//!
//! A conflict occurs when:
//! - We assert `x ≠ y` but the E-graph already knows `x = y`
//! - We assert `x = y` but there's a chain of disequalities making this impossible
//!
//! # Proof Reconstruction
//!
//! The theory solver tracks union reasons for proof reconstruction:
//! - Direct assertions record the hypothesis that caused the union
//! - Congruence steps record which argument equalities caused the merge
//! - The proof trace can be used to build kernel proof terms

use crate::cdcl::Lit;
use crate::egraph::{EClassId, EGraph};
use crate::proof::{ForestReason, ProofForest, ProofTrace, UnionReason};
use crate::smt::{SmtTerm, TermId, TheoryCheckResult};
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

mod explanations;
mod propagation;
mod solver_impl;
mod stats;

pub(crate) use stats::ExplanationStats;

/// Equality theory solver using E-graphs
pub struct EqualityTheory {
    /// The E-graph for congruence closure
    egraph: EGraph,
    /// Mapping from SMT term IDs to E-class IDs
    pub(super) term_to_eclass: HashMap<TermId, EClassId>,
    /// Disequalities that have been asserted: (t1, t2, literal)
    /// The literal is stored so we can report it in conflicts
    disequalities: Vec<(TermId, TermId, Lit)>,
    /// Equalities asserted at each level (for backtracking)
    pub(super) equality_trail: Vec<Vec<(TermId, TermId, Lit)>>,
    /// Disequality indices at each level (for backtracking)
    pub(super) diseq_trail: Vec<usize>,
    /// Current decision level
    level: u32,
    /// SMT terms (shared via Arc to avoid per-theory cloning, #2308)
    terms: Arc<[SmtTerm]>,
    /// Proof trace for kernel proof term reconstruction (E-class level).
    /// Kept for bridge/proof_reconstruction.rs compatibility.
    proof_trace: ProofTrace,
    /// Per-term parent pointer forest for precise CDCL explanation extraction.
    /// Immune to post-merge canonical ID changes (fixes #2352).
    proof_forest: ProofForest,
    /// Runtime monitoring for precise-vs-fallback EUF explanations (#2396).
    explanation_stats: ExplanationStats,
    /// Mapping from term ID to hypothesis FVarId (for asserted equalities)
    pub(super) term_to_hypothesis: HashMap<(TermId, TermId), FVarId>,
    /// Saved term_to_hypothesis trail positions per level for backtracking (#2406).
    /// On backtrack, undo entries after the saved position. Avoids O(N) HashMap
    /// clone in push().
    pub(super) term_to_hypothesis_trail: Vec<usize>,
    /// Trail of (key, old_value) pairs for undoing term_to_hypothesis changes.
    /// `None` old_value means the key was freshly inserted (remove on undo).
    /// `Some(v)` means the key was overwritten (restore old value on undo).
    pub(super) term_to_hypothesis_undo: Vec<((TermId, TermId), Option<FVarId>)>,
    /// Newly deduced equalities since last drain (#2344).
    /// Populated during assert_equality when congruence closure
    /// merges classes containing registered terms.
    pub(super) pending_deduced: Vec<(TermId, TermId)>,
    /// Snapshots of E-graph state per level for O(N) backtrack (#2363).
    /// Replaces the O(K×M) replay approach that called build_class_members_map()
    /// once per replayed equality.
    pub(super) egraph_trail: Vec<EGraph>,
    /// Snapshots of term_to_eclass per level for backtracking (#2363).
    pub(super) term_to_eclass_trail: Vec<HashMap<TermId, EClassId>>,
    /// Append-only proof trace checkpoints per level for backtracking (#2372).
    pub(super) proof_trace_len_trail: Vec<usize>,
    /// Structural terms registered by `internalize_atom()` that survive
    /// `reset()`. Reset rebuilds the E-graph from this list instead of
    /// cloning the entire E-graph after every internalization.
    reset_base_terms: Vec<TermId>,
    /// Dedup set for `reset_base_terms`.
    reset_base_term_set: HashSet<TermId>,
    /// Structural hypothesis registrations that survive `reset()`.
    reset_base_term_to_hypothesis: HashMap<(TermId, TermId), FVarId>,
    /// Incrementally maintained canonical E-class ID → registered TermIds map.
    /// Kept valid between `assert_equality` calls to avoid O(T) rebuild per merge.
    /// When `class_members_valid` is true, this map reflects current E-graph
    /// canonical IDs. When false, `take_class_members_snapshot` rebuilds it (#2406).
    class_members_buf: HashMap<u32, Vec<TermId>>,
    /// Whether `class_members_buf` reflects current canonical IDs.
    /// Set to false on backtrack/reset; set to true after incremental update.
    class_members_valid: bool,
}

impl EqualityTheory {
    /// Create a new equality theory solver
    pub fn new() -> Self {
        EqualityTheory {
            egraph: EGraph::new(),
            term_to_eclass: HashMap::new(),
            disequalities: Vec::new(),
            equality_trail: vec![Vec::new()],
            diseq_trail: vec![0],
            level: 0,
            terms: Arc::from(Vec::<SmtTerm>::new()),
            proof_trace: ProofTrace::new(),
            proof_forest: ProofForest::new(),
            explanation_stats: ExplanationStats::default(),
            term_to_hypothesis: HashMap::new(),
            term_to_hypothesis_trail: Vec::new(),
            term_to_hypothesis_undo: Vec::new(),
            pending_deduced: Vec::new(),
            egraph_trail: Vec::new(),
            term_to_eclass_trail: Vec::new(),
            proof_trace_len_trail: Vec::new(),
            reset_base_terms: Vec::new(),
            reset_base_term_set: HashSet::new(),
            reset_base_term_to_hypothesis: HashMap::new(),
            class_members_buf: HashMap::new(),
            class_members_valid: false,
        }
    }

    fn has_assertion_state(&self) -> bool {
        self.level > 0
            || self
                .equality_trail
                .iter()
                .any(|entries| !entries.is_empty())
            || !self.disequalities.is_empty()
    }

    pub(super) fn record_reset_base_term(&mut self, term_id: TermId) {
        if self.has_assertion_state() {
            return;
        }
        if self.reset_base_term_set.insert(term_id) {
            self.reset_base_terms.push(term_id);
        }
    }

    /// Set the terms (called by SMT solver to share term information).
    /// Accepts both `Vec<SmtTerm>` and `Arc<[SmtTerm]>` via `Into`.
    pub fn set_terms(&mut self, terms: impl Into<Arc<[SmtTerm]>>) {
        self.terms = terms.into();
    }

    /// Register a hypothesis for an equality (for proof reconstruction)
    pub fn register_hypothesis(&mut self, t1: TermId, t2: TermId, fvar: FVarId) {
        // Track undo entries for trail-based backtracking (#2406)
        if self.level > 0 {
            let old1 = self.term_to_hypothesis.get(&(t1, t2)).copied();
            let old2 = self.term_to_hypothesis.get(&(t2, t1)).copied();
            self.term_to_hypothesis_undo.push(((t1, t2), old1));
            self.term_to_hypothesis_undo.push(((t2, t1), old2));
        }
        self.term_to_hypothesis.insert((t1, t2), fvar);
        self.term_to_hypothesis.insert((t2, t1), fvar);
        if !self.has_assertion_state() {
            self.reset_base_term_to_hypothesis.insert((t1, t2), fvar);
            self.reset_base_term_to_hypothesis.insert((t2, t1), fvar);
        }
    }

    /// Get the proof trace (for proof reconstruction)
    pub fn proof_trace(&self) -> &ProofTrace {
        &self.proof_trace
    }

    /// Get or create an E-class ID for a term
    pub(super) fn get_or_create_eclass(&mut self, term_id: TermId) -> EClassId {
        if let Some(&eclass) = self.term_to_eclass.get(&term_id) {
            return eclass;
        }

        let eclass = self.build_term_in_egraph(term_id);
        self.term_to_eclass.insert(term_id, eclass);
        // Maintain incremental class_members_buf when valid (#2406)
        if self.class_members_valid {
            let canonical = self.egraph.find_const(eclass).id();
            self.class_members_buf
                .entry(canonical)
                .or_default()
                .push(term_id);
        }
        eclass
    }

    /// Build a term in the E-graph
    fn build_term_in_egraph(&mut self, term_id: TermId) -> EClassId {
        if let Some(&eclass) = self.term_to_eclass.get(&term_id) {
            return eclass;
        }

        let term = self.terms.get(term_id.index()).cloned();

        let eclass = match term {
            Some(SmtTerm::Const(ref name)) => self.egraph.add_const(name.name()),
            Some(SmtTerm::App(ref name, ref args)) => {
                let arg_eclasses: Vec<EClassId> = args
                    .iter()
                    .map(|&arg_id| self.build_term_in_egraph(arg_id))
                    .collect();
                self.egraph.add_app(name.name(), arg_eclasses)
            }
            Some(SmtTerm::Int(n)) => self.egraph.add_const(format!("int_{n}")),
            Some(SmtTerm::Rat(num, den)) => self.egraph.add_const(format!("rat_{num}_{den}")),
            None => self.egraph.add_const(format!("term_{}", term_id.raw())),
        };

        self.term_to_eclass.insert(term_id, eclass);
        eclass
    }

    /// Assert an equality: t1 = t2
    fn assert_equality(&mut self, t1: TermId, t2: TermId, lit: Lit) -> TheoryCheckResult {
        let ec1 = self.get_or_create_eclass(t1);
        let ec2 = self.get_or_create_eclass(t2);

        self.equality_trail[self.level as usize].push((t1, t2, lit));

        let hypothesis = self.term_to_hypothesis.get(&(t1, t2)).copied();
        self.proof_trace.record_union(
            ec1.id(),
            ec2.id(),
            UnionReason::Asserted {
                hypothesis,
                lhs: t1,
                rhs: t2,
            },
        );

        self.proof_forest
            .record_merge(t1, t2, ForestReason::Asserted(lit), self.level);

        let pre_union_members = self.take_class_members_snapshot();
        let canon1_pre = self.egraph.find_const(ec1).id();
        let canon2_pre = self.egraph.find_const(ec2).id();

        let history_start = self.egraph.merge_history().len();

        self.egraph.union(ec1, ec2);

        self.record_congruence_merges(history_start, &pre_union_members);

        if canon1_pre != canon2_pre {
            let class1 = pre_union_members.get(&canon1_pre);
            let class2 = pre_union_members.get(&canon2_pre);
            if let (Some(c1), Some(c2)) = (class1, class2) {
                'outer: for &ta in c1 {
                    for &tb in c2 {
                        if (ta == t1 && tb == t2) || (ta == t2 && tb == t1) {
                            continue;
                        }
                        self.pending_deduced.push((ta, tb));
                        break 'outer;
                    }
                }
            }
        }

        // Restore and incrementally update class_members_buf to reflect
        // post-union canonical IDs, avoiding O(T) full rebuild on next call (#2406).
        self.class_members_buf = pre_union_members;
        self.update_class_members_after_union(history_start);
        self.class_members_valid = true;

        self.check_disequalities()
    }

    /// Assert a disequality: t1 ≠ t2
    fn assert_disequality(&mut self, t1: TermId, t2: TermId, lit: Lit) -> TheoryCheckResult {
        let ec1 = self.get_or_create_eclass(t1);
        let ec2 = self.get_or_create_eclass(t2);

        if self.egraph.are_equal(ec1, ec2) {
            let mut conflict = self.explain_why_equal(t1, t2);
            conflict.push(lit);
            return TheoryCheckResult::Conflict(conflict);
        }

        self.disequalities.push((t1, t2, lit));

        TheoryCheckResult::Consistent
    }

    /// Check all disequalities for violations.
    ///
    /// Uses index-based iteration to avoid cloning the disequalities Vec
    /// (#2373). Safe because `get_or_create_eclass` only modifies
    /// `term_to_eclass` and `egraph`, and `explain_why_equal` only updates
    /// explanation monitoring — neither touches `self.disequalities`.
    fn check_disequalities(&mut self) -> TheoryCheckResult {
        for i in 0..self.disequalities.len() {
            let (t1, t2, lit) = self.disequalities[i];
            let ec1 = self.get_or_create_eclass(t1);
            let ec2 = self.get_or_create_eclass(t2);

            if self.egraph.are_equal(ec1, ec2) {
                let mut conflict = self.explain_why_equal(t1, t2);
                conflict.push(lit);
                return TheoryCheckResult::Conflict(conflict);
            }
        }

        TheoryCheckResult::Consistent
    }

    /// Ensure a term has an E-class in the E-graph.
    ///
    /// Idempotent: safe to call multiple times for the same term.
    /// Direct callers and tests should call this before `are_equal()`
    /// to ensure terms are registered (#2319).
    pub fn internalize_term(&mut self, term_id: TermId) {
        self.get_or_create_eclass(term_id);
    }

    /// Check if two terms are equal in the current state.
    ///
    /// Both terms must already be internalized (via `internalize_term`,
    /// `internalize_atom`, or `assert_literal`). Returns `false` if
    /// either term has not been internalized (#2319).
    pub fn are_equal(&self, t1: TermId, t2: TermId) -> bool {
        let ec1 = match self.term_to_eclass.get(&t1) {
            Some(&ec) => ec,
            None => return false,
        };
        let ec2 = match self.term_to_eclass.get(&t2) {
            Some(&ec) => ec,
            None => return false,
        };
        self.egraph.find_const(ec1) == self.egraph.find_const(ec2)
    }

    /// Get the E-graph (for debugging/inspection)
    pub fn egraph(&self) -> &EGraph {
        &self.egraph
    }

    /// Get the term to E-class mapping (for E-matching instantiation)
    pub fn term_to_eclass_map(&self) -> &HashMap<TermId, EClassId> {
        &self.term_to_eclass
    }

    /// Get the E-class ID for a term (if it exists)
    pub fn get_eclass(&self, term_id: TermId) -> Option<u32> {
        self.term_to_eclass.get(&term_id).map(|ec| ec.id())
    }

    /// Get the canonical E-class ID for a term (if it exists)
    pub fn get_canonical_eclass(&self, term_id: TermId) -> Option<u32> {
        self.term_to_eclass
            .get(&term_id)
            .map(|ec| self.egraph.find_const(*ec).id())
    }
}
