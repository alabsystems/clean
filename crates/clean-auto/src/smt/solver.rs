// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SmtSolver: DPLL(T) framework combining SAT + theory solvers
//!
//! The DPLL(T) search/check loop lives in the sibling `solver/search` module.
//! Runtime-stat helpers live in `solver/stats`.
//! Proof-trail helpers live in `solver/trail`.
//! The Nelson-Oppen theory propagation collectors (array, equality,
//! arithmetic, and cross-theory forwarding) are in the sibling `propagation`
//! module.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                         SMT Solver                               │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                  │
//! │  ┌─────────────┐        ┌─────────────────────────────────────┐ │
//! │  │    CDCL     │◄──────►│         Theory Combination          │ │
//! │  │  SAT Core   │        │                                     │ │
//! │  └─────────────┘        │  ┌─────────┐ ┌─────────┐ ┌───────┐  │ │
//! │                         │  │Equality │ │  Arith  │ │Arrays │  │ │
//! │                         │  │(E-graph)│ │  (LRA)  │ │       │  │ │
//! │                         │  └─────────┘ └─────────┘ └───────┘  │ │
//! │                         └─────────────────────────────────────┘ │
//! │                                                                  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # DPLL(T) Algorithm
//!
//! 1. SAT solver makes decisions and propagates boolean constraints
//! 2. After each propagation, theory solvers check consistency
//! 3. Theory solvers can:
//!    - Propagate theory consequences (theory propagation)
//!    - Detect conflicts (theory conflict)
//! 4. On conflict, learn a clause and backtrack
//! 5. Repeat until SAT (with theory-consistent model) or UNSAT

mod levels;
mod search;
mod stats;
mod trail;

use self::stats::TheoryRuntimeTotals;
use super::{
    ProofTrailEntry, SmtInt, SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver,
};
use crate::cdcl::{CdclSolver, ClauseRef, Lit, Var};
use crate::egraph::Symbol;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Result of the Nelson-Oppen equality fixpoint loop (#2366).
enum NelsonOppenResult {
    /// Fixpoint reached — no new equalities in the last pass.
    Converged,
    /// Forwarding detected a theory conflict with a resolved explanation
    /// (#2386). The `Vec<Lit>` contains conflict lits where dynamic
    /// forwarding-generated SAT variables have been replaced by their
    /// original explanation premises. Caller can return this directly as
    /// a `TheoryBatchResult::Conflict` — the lits reference only SAT
    /// variables the CDCL solver already knows.
    ForwardingConflict(Vec<Lit>),
    /// Forwarding detected a theory conflict but resolution failed — the
    /// conflict explanation references dynamic SAT variables that could
    /// not be resolved to original premises (for example, an unsynced
    /// opposite-polarity reference to a forwarding-created atom). Caller
    /// must skip `theory.check()` and return propagations instead (legacy
    /// fallback path).
    ForwardingConflictUnresolved,
    /// Forwarding hit an incomplete theory result.
    ///
    /// The caller must return `Unknown`: ignoring an `Unknown` from a
    /// forwarded shared equality can incorrectly claim `Sat`.
    ForwardingUnknown,
    /// Loop hit the pass cap before reaching a fixpoint.
    ///
    /// The caller must return `Unknown`: continuing as if the loop converged
    /// can miss later equalities that would have produced a conflict.
    Exhausted,
}

/// Result of forwarding one or more shared equalities to peer theories.
pub(super) enum ForwardEqualityResult {
    Consistent,
    /// A peer theory detected a conflict. The `Vec<Lit>` contains the
    /// raw conflict explanation lits from the theory (may reference
    /// dynamic SAT variables created during forwarding).
    Conflict(Vec<Lit>),
    Unknown,
}

/// Cached theory-sync baseline for `solve()` setup.
#[derive(Clone, Copy, Debug, Default)]
struct TheorySyncState {
    theory_count: usize,
    term_count: usize,
    theory_var_upper_bound: usize,
}

/// A theory propagation paired with the theory that produced it.
///
/// The DPLL(T) control plane may batch propagations from multiple theories
/// before handing them to the SAT solver. Keeping the origin on each
/// propagation preserves proof-trail attribution instead of collapsing
/// everything to a synthetic "combined" source.
#[derive(Clone, Debug)]
pub(super) struct AttributedPropagation {
    pub(super) implied: Lit,
    pub(super) explanation: Vec<Lit>,
    pub(super) theory_name: &'static str,
}

impl AttributedPropagation {
    pub(super) fn new(implied: Lit, explanation: Vec<Lit>, theory_name: &'static str) -> Self {
        Self {
            implied,
            explanation,
            theory_name,
        }
    }
}

/// SMT solver combining CDCL SAT solver with theory solvers
pub(crate) struct SmtSolver {
    /// The underlying CDCL SAT solver
    sat: CdclSolver,
    /// Theory solvers
    pub(super) theories: Vec<Box<dyn TheorySolver>>,
    /// Mapping from SAT variables to theory literals
    pub(super) var_to_theory: BTreeMap<Var, TheoryLiteral>,
    /// Mapping from theory literals to SAT variables
    theory_to_var: HashMap<TheoryLiteral, Var>,
    /// Upper bound of theory-backed SAT variable indices.
    ///
    /// `get_or_create_var()` allocates SAT variables monotonically, so newly
    /// registered theory atoms always have `var.index() >= previous_bound`.
    registered_theory_var_upper_bound: usize,
    /// Term storage
    terms: Vec<SmtTerm>,
    /// Cached shared term snapshot for theory `set_terms()` calls.
    ///
    /// Rebuilt only when a genuinely new term is interned, so repeated
    /// `solve()` calls on an unchanged term set do not reclone the full term
    /// slice into a fresh `Arc<[SmtTerm]>` every time.
    shared_terms_snapshot: Option<Arc<[SmtTerm]>>,
    /// Last fully synchronized theory setup baseline.
    theory_sync_state: TheorySyncState,
    /// Mutable theory access or theory-list edits require a full resync.
    theory_sync_dirty: bool,
    /// Hash-cons map: hash -> list of term IDs with that hash (avoids rehashing on lookup)
    hash_cons: HashMap<u64, Vec<TermId>>,
    /// Proof trail: records theory-level events during DPLL(T) solving (#2442 Phase 2).
    /// Populated during `sat_solve_with_theory()`, consumed by the bridge for
    /// proof reconstruction. Cleared at the start of each `solve()` call.
    proof_trail: Vec<ProofTrailEntry>,
    /// SAT assignments grouped by decision level for scoped theory replay.
    decision_levels: Vec<levels::DecisionLevel>,
    /// SAT trail replayed into theories, annotated with decision levels.
    assignment_trail: Vec<levels::LevelAnnotatedAssignment>,
    /// Theory assertions replayed from the SAT trail with their decision level.
    theory_assertion_trail: Vec<levels::LeveledAssertion>,
    /// Current theory scope depth during SAT-trail replay.
    theory_scope_level: u32,
    /// Canonical array pairs that already received a lazy extensionality lemma.
    emitted_extensionality_pairs: HashSet<(TermId, TermId)>,
    /// Monotonic counter for fresh extensionality witness constants.
    extensionality_witness_counter: u64,
    /// Reusable buffer for Nelson-Oppen equality dedup in `nelson_oppen_fixpoint`.
    ///
    /// Hoisted from a local to amortize allocation across DPLL(T) iterations.
    /// Cleared at the start of each fixpoint call (#2386).
    fixpoint_seen_deduced: HashSet<(TermId, TermId)>,
    /// Reusable buffer for deduction-source tracking in `nelson_oppen_fixpoint`.
    ///
    /// Maps SAT variable → originating theory index so forwarding skips the
    /// originator. Hoisted from a local to amortize allocation (#2386).
    fixpoint_deduction_source: HashMap<Var, usize>,
    /// Cumulative theory-side runtime totals surfaced through `SmtStats`.
    theory_runtime_totals: TheoryRuntimeTotals,
}

impl SmtSolver {
    /// Create a new SMT solver
    pub(crate) fn new() -> Self {
        SmtSolver {
            sat: CdclSolver::new(0),
            theories: Vec::new(),
            var_to_theory: BTreeMap::new(),
            theory_to_var: HashMap::new(),
            registered_theory_var_upper_bound: 0,
            terms: Vec::new(),
            shared_terms_snapshot: None,
            theory_sync_state: TheorySyncState::default(),
            theory_sync_dirty: false,
            hash_cons: HashMap::new(),
            proof_trail: Vec::new(),
            decision_levels: vec![levels::DecisionLevel::new(0)],
            assignment_trail: Vec::new(),
            theory_assertion_trail: Vec::new(),
            theory_scope_level: 0,
            emitted_extensionality_pairs: HashSet::new(),
            extensionality_witness_counter: 0,
            fixpoint_seen_deduced: HashSet::new(),
            fixpoint_deduction_source: HashMap::new(),
            theory_runtime_totals: TheoryRuntimeTotals::default(),
        }
    }

    /// Add a theory solver, returns its index
    pub(crate) fn add_theory(&mut self, theory: Box<dyn TheorySolver>) -> usize {
        let idx = self.theories.len();
        self.theories.push(theory);
        self.mark_theory_sync_dirty();
        idx
    }

    /// Get a typed reference to a theory solver by index
    pub(crate) fn get_theory_typed<T: 'static>(&self, idx: usize) -> Option<&T> {
        self.theories
            .get(idx)
            .and_then(|t| t.as_any().downcast_ref::<T>())
    }

    /// Get a typed mutable reference to a theory solver by index
    pub(crate) fn get_theory_typed_mut<T: 'static>(&mut self, idx: usize) -> Option<&mut T> {
        if self.theories.get(idx).is_some_and(|t| t.as_any().is::<T>()) {
            self.mark_theory_sync_dirty();
        }
        self.theories
            .get_mut(idx)
            .and_then(|t| t.as_any_mut().downcast_mut::<T>())
    }

    pub(super) fn set_sat_phase_hint(&mut self, var: Var, phase: bool) {
        self.sat.set_phase_hint(var, phase);
    }

    #[cfg(test)]
    pub(super) fn sat_phase_hint(&self, var: Var) -> bool {
        self.sat.phase_hint(var)
    }

    /// Create a new constant term
    pub(crate) fn const_term(&mut self, name: impl Into<Symbol>) -> TermId {
        let term = SmtTerm::Const(name.into());
        self.intern_term(term)
    }

    /// Create a function application term
    pub(crate) fn app_term(&mut self, name: impl Into<Symbol>, args: Vec<TermId>) -> TermId {
        let term = SmtTerm::App(name.into(), args);
        self.intern_term(term)
    }

    /// Create an integer constant term
    pub(crate) fn int_term(&mut self, value: impl Into<SmtInt>) -> TermId {
        let term = SmtTerm::Int(value.into());
        self.intern_term(term)
    }

    /// Create a select (array read) term: select(array, index) → value
    pub(crate) fn select_term(&mut self, array: TermId, index: TermId) -> TermId {
        self.app_term("select", vec![array, index])
    }

    /// Create a store (array write) term: store(array, index, value) → new_array
    pub(crate) fn store_term(&mut self, array: TermId, index: TermId, value: TermId) -> TermId {
        self.app_term("store", vec![array, index, value])
    }

    /// Compute hash for a term (used for hash-consing)
    fn compute_term_hash(term: &SmtTerm) -> u64 {
        let mut hasher = DefaultHasher::new();
        term.hash(&mut hasher);
        hasher.finish()
    }

    pub(super) fn mark_theory_sync_dirty(&mut self) {
        self.theory_sync_dirty = true;
    }

    /// Intern a term (deduplicate using hash-consing)
    ///
    /// Uses hash-consing: pre-computes hash once, then only compares full terms
    /// when there's a hash collision. This avoids rehashing on every lookup.
    fn intern_term(&mut self, term: SmtTerm) -> TermId {
        let hash = Self::compute_term_hash(&term);

        // Check if we already have this term (compare only on hash collision)
        if let Some(ids) = self.hash_cons.get(&hash) {
            for &id in ids {
                if self.terms[id.index()] == term {
                    return id;
                }
            }
        }

        // Create new term
        let id = TermId::new(
            u32::try_from(self.terms.len()).expect("invariant: interned term count fits in u32"),
        );
        self.terms.push(term);
        self.shared_terms_snapshot = None;
        self.hash_cons.entry(hash).or_default().push(id);
        id
    }

    pub(super) fn shared_terms_for_theories(&mut self) -> Arc<[SmtTerm]> {
        if let Some(shared_terms) = &self.shared_terms_snapshot {
            return Arc::clone(shared_terms);
        }

        let shared_terms = Arc::<[SmtTerm]>::from(self.terms.clone());
        self.shared_terms_snapshot = Some(Arc::clone(&shared_terms));
        shared_terms
    }

    /// Get or create a SAT variable for a theory literal
    pub(super) fn get_or_create_var(&mut self, lit: TheoryLiteral) -> Var {
        if let Some(&var) = self.theory_to_var.get(&lit) {
            return var;
        }
        let var = self.sat.new_var();
        self.var_to_theory.insert(var, lit.clone());
        self.theory_to_var.insert(lit, var);
        self.registered_theory_var_upper_bound =
            self.registered_theory_var_upper_bound.max(var.index() + 1);
        var
    }

    pub(super) fn is_theory_var_synced(&self, var: Var) -> bool {
        var.index() < self.theory_sync_state.theory_var_upper_bound
    }

    pub(super) fn theory_var_for_literal(&self, theory_lit: &TheoryLiteral) -> Option<Var> {
        self.theory_to_var.get(theory_lit).copied()
    }

    pub(super) fn theory_literal_for_var(&self, var: Var) -> Option<&TheoryLiteral> {
        self.var_to_theory.get(&var)
    }

    pub(super) fn equality_var(&self, lhs: TermId, rhs: TermId) -> Option<Var> {
        self.theory_var_for_literal(&TheoryLiteral::Eq(lhs, rhs))
            .or_else(|| self.theory_var_for_literal(&TheoryLiteral::Eq(rhs, lhs)))
    }

    pub(super) fn record_theory_runtime_result(&mut self, result: &TheoryCheckResult) {
        self.theory_runtime_totals.record_result(result);
    }

    pub(super) fn clear_fixpoint_scratch(&mut self) {
        self.fixpoint_seen_deduced.clear();
        self.fixpoint_deduction_source.clear();
    }

    pub(super) fn mark_fixpoint_equality_seen(&mut self, lhs: TermId, rhs: TermId) -> bool {
        let key = if lhs.raw() <= rhs.raw() {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        self.fixpoint_seen_deduced.insert(key)
    }

    pub(super) fn record_fixpoint_deduction_source(&mut self, var: Var, source_idx: usize) {
        self.fixpoint_deduction_source.insert(var, source_idx);
    }

    pub(super) fn fixpoint_deduction_source(&self, var: Var) -> Option<usize> {
        self.fixpoint_deduction_source.get(&var).copied()
    }

    fn lower_theory_literal(&mut self, theory_lit: TheoryLiteral) -> Lit {
        let (base_lit, positive) = match theory_lit {
            TheoryLiteral::Eq(a, b) => (TheoryLiteral::Eq(a, b), true),
            TheoryLiteral::Neq(a, b) => (TheoryLiteral::Eq(a, b), false),
            TheoryLiteral::Lt(a, b) => (TheoryLiteral::Lt(a, b), true),
            TheoryLiteral::Le(a, b) => (TheoryLiteral::Le(a, b), true),
            TheoryLiteral::Bool(v) => (TheoryLiteral::Bool(v), true),
            TheoryLiteral::NegBool(v) => (TheoryLiteral::Bool(v), false),
        };
        let var = self.get_or_create_var(base_lit);
        if positive {
            Lit::pos(var)
        } else {
            Lit::neg(var)
        }
    }

    pub(super) fn add_derived_theory_clause(
        &mut self,
        theory_lits: Vec<TheoryLiteral>,
    ) -> Option<ClauseRef> {
        let sat_lits = theory_lits
            .into_iter()
            .map(|theory_lit| self.lower_theory_literal(theory_lit))
            .collect();
        self.sat.add_theory_clause(sat_lits)
    }

    /// Assert an equality constraint: t1 = t2.
    ///
    /// Returns the clause reference for the unit clause, or `None` if the
    /// assertion immediately conflicts with an existing opposite literal
    /// (#2319).
    pub(crate) fn assert_eq(&mut self, t1: TermId, t2: TermId) -> Option<ClauseRef> {
        let lit = TheoryLiteral::Eq(t1, t2);
        let var = self.get_or_create_var(lit);
        // Add unit clause forcing this equality
        self.sat.add_clause(vec![Lit::pos(var)])
    }

    /// Assert a disequality constraint: t1 ≠ t2.
    ///
    /// Returns the clause reference for the unit clause, or `None` if the
    /// assertion immediately conflicts with an existing opposite literal
    /// (#2319).
    pub(crate) fn assert_neq(&mut self, t1: TermId, t2: TermId) -> Option<ClauseRef> {
        let var = self.get_or_create_var(TheoryLiteral::Eq(t1, t2));
        // Add unit clause forcing this disequality (negation of equality var)
        self.sat.add_clause(vec![Lit::neg(var)])
    }

    /// Add a clause over theory literals
    pub(crate) fn add_clause(&mut self, theory_lits: Vec<TheoryLiteral>) -> Option<ClauseRef> {
        let sat_lits: Vec<Lit> = theory_lits
            .into_iter()
            .map(|theory_lit| self.lower_theory_literal(theory_lit))
            .collect();
        self.sat.add_clause(sat_lits)
    }

    /// Get a term by ID
    pub(crate) fn get_term(&self, id: TermId) -> Option<&SmtTerm> {
        self.terms.get(id.index())
    }

    /// Get the number of original clauses currently in the SAT solver.
    ///
    /// Used by the bridge to track which clauses correspond to which hypotheses
    /// for UNSAT core → proof reconstruction mapping (#2442 Phase 2B).
    pub(crate) fn num_clauses(&self) -> usize {
        self.sat.num_clauses()
    }
}

#[cfg(test)]
impl SmtSolver {
    /// Get a reference to the terms (test-only, #2386).
    pub fn terms(&self) -> &[SmtTerm] {
        &self.terms
    }

    /// Get a reference to a theory solver by index (test-only, #2386).
    pub fn get_theory(&self, idx: usize) -> Option<&dyn TheorySolver> {
        self.theories.get(idx).map(AsRef::as_ref)
    }

    /// Get a mutable reference to a theory solver by index (test-only, #2386).
    pub fn get_theory_mut(&mut self, idx: usize) -> Option<&mut (dyn TheorySolver + '_)> {
        if idx >= self.theories.len() {
            return None;
        }
        self.mark_theory_sync_dirty();
        Some(self.theories[idx].as_mut())
    }
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}
