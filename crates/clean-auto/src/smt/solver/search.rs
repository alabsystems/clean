// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DPLL(T) search/check loop for `SmtSolver`.

use super::{AttributedPropagation, ForwardEqualityResult, NelsonOppenResult, SmtSolver};
use crate::cdcl::{ClauseRef, Lit, SolveResult};
use crate::smt::{
    SmtModel, SmtResult, TheoryCheckResult, TheoryLemmaRequest, TheoryLiteral, UnsatCore,
};
use std::sync::Arc;

enum TheoryBatchResult {
    Consistent,
    Conflict(Vec<Lit>, &'static str),
    Propagation(Vec<AttributedPropagation>),
    Unknown,
    Restart,
}

impl SmtSolver {
    fn sync_theories_to_solver_state(&mut self) {
        let full_resync =
            self.theory_sync_dirty || self.theory_sync_state.theory_count != self.theories.len();
        let terms_changed = full_resync || self.theory_sync_state.term_count != self.terms.len();
        let first_unsynced_var = if full_resync {
            0
        } else {
            self.theory_sync_state.theory_var_upper_bound
        };
        let has_new_atoms = self.registered_theory_var_upper_bound > first_unsynced_var;

        if !terms_changed && !has_new_atoms {
            return;
        }

        // Terms are immutable during solving, so theories can share one
        // cached Arc snapshot until term interning grows the term set (#2308).
        let shared_terms = terms_changed.then(|| self.shared_terms_for_theories());
        for theory in &mut self.theories {
            if let Some(shared_terms) = &shared_terms {
                theory.set_terms(Arc::clone(shared_terms));
            }

            // Pre-register only newly introduced theory literals when the
            // structural baseline is still valid. Full resyncs (new theories or
            // mutable theory access) intentionally replay all atoms.
            for (&var, theory_lit) in &self.var_to_theory {
                if var.index() >= first_unsynced_var {
                    theory.internalize_atom(theory_lit);
                }
            }
        }

        self.theory_sync_state.theory_count = self.theories.len();
        self.theory_sync_state.term_count = self.terms.len();
        self.theory_sync_state.theory_var_upper_bound = self.registered_theory_var_upper_bound;
        self.theory_sync_dirty = false;
    }

    fn assert_assignment_trail_to_theories(
        &mut self,
        propagations: &mut Vec<AttributedPropagation>,
        any_unknown: &mut bool,
    ) -> Option<TheoryBatchResult> {
        let assignments = self.assignment_trail.clone();
        for assignment in assignments {
            self.push_theories_to_level(assignment.level);
            let Some(theory_lit) = self.lit_to_theory_literal(assignment.lit) else {
                continue;
            };
            self.record_theory_assertion(assignment.lit, theory_lit.clone(), assignment.level);
            for idx in 0..self.theories.len() {
                let result = {
                    let theory = &mut self.theories[idx];
                    theory.assert_literal(assignment.lit, &theory_lit)
                };
                self.theory_runtime_totals.record_result(&result);
                let theory_name = self.theories[idx].name();
                match result {
                    TheoryCheckResult::Conflict(lits) => {
                        let conflict_level = self.conflict_level(&lits);
                        self.backtrack_assignment_stack_to(conflict_level);
                        return Some(TheoryBatchResult::Conflict(lits, theory_name));
                    }
                    TheoryCheckResult::Propagation(lits) => {
                        propagations.extend(lits.into_iter().map(|(implied, explanation)| {
                            AttributedPropagation::new(implied, explanation, theory_name)
                        }));
                    }
                    TheoryCheckResult::Consistent => {}
                    TheoryCheckResult::Unknown => {
                        *any_unknown = true;
                    }
                }
            }
        }
        None
    }

    fn emit_theory_lemmas(&mut self) -> bool {
        let requests: Vec<_> = self
            .theories
            .iter_mut()
            .flat_map(|theory| theory.drain_lemma_requests())
            .collect();

        let mut emitted_any = false;
        for request in requests {
            match request {
                TheoryLemmaRequest::ArrayExtensionality { lhs, rhs, .. } => {
                    let pair = if lhs.0 <= rhs.0 {
                        (lhs, rhs)
                    } else {
                        (rhs, lhs)
                    };
                    if !self.emitted_extensionality_pairs.insert(pair) {
                        continue;
                    }

                    let witness_name =
                        format!("array_ext_witness_{}", self.extensionality_witness_counter);
                    self.extensionality_witness_counter += 1;
                    let witness = self.const_term(witness_name);
                    let lhs_select = self.select_term(lhs, witness);
                    let rhs_select = self.select_term(rhs, witness);
                    let clause = vec![
                        TheoryLiteral::Eq(lhs, rhs),
                        TheoryLiteral::Neq(lhs_select, rhs_select),
                    ];
                    let _ = self
                        .add_derived_theory_clause(clause)
                        .expect("invariant: extensionality clause is a 2-literal vec");
                    emitted_any = true;
                }
            }
        }

        emitted_any
    }

    /// Solve the SMT problem
    pub(crate) fn solve(&mut self) -> SmtResult {
        // Run SAT solver with theory integration
        self.sat_solve_with_theory()
    }

    const MAX_DPLL_T_ITERATIONS: u32 = 10_000;

    /// Extract UNSAT core from the SAT solver.
    pub(super) fn take_unsat_core_result(&mut self) -> SmtResult {
        let smt_core = self.sat.take_unsat_core().map(|core| UnsatCore {
            clauses: core.clause_indices.into_iter().map(ClauseRef).collect(),
        });
        SmtResult::Unsat(smt_core)
    }

    /// Run SAT solver with theory integration (iterative DPLL(T) loop).
    ///
    /// # Sync contract (#2386)
    ///
    /// Every code path that creates new theory atoms (via `get_or_create_var`)
    /// or terms (via `intern_term`) mid-solve MUST call
    /// `sync_theories_to_solver_state()` before the next SAT iteration so
    /// `internalize_atom` runs for all newly registered literals. The current
    /// sync points:
    ///
    /// - **Entry**: once before the loop (line 159).
    /// - **Propagation arm**: after `add_propagation_clauses`, because
    ///   Nelson-Oppen `convert_deduced_to_propagations` can call
    ///   `get_or_create_var` for equalities not yet in `theory_to_var`.
    /// - **Restart arm**: after `backtrack_to_root`, because
    ///   `emit_theory_lemmas` creates new terms and SAT variables via
    ///   `add_derived_theory_clause`.
    ///
    /// The Conflict arm includes a sync because forwarding conflict
    /// resolution (#2386) can return a direct `TheoryBatchResult::Conflict`
    /// even when `convert_deduced_to_propagations` created new SAT
    /// variables during the N-O fixpoint. A `debug_assert` below guards
    /// the invariant that all new atoms are synced before the next
    /// SAT iteration.
    fn sat_solve_with_theory(&mut self) -> SmtResult {
        // Clear proof trail from any previous solve() call (#2442 Phase 2).
        self.proof_trail.clear();
        self.sync_theories_to_solver_state();
        self.reset_theory_assignment_state();

        for _ in 0..Self::MAX_DPLL_T_ITERATIONS {
            // Sync-contract guard (#2386): at the top of each iteration, all
            // theory atoms and terms created in prior iterations must have been
            // synced. If this fires, a code path created new atoms without
            // calling sync_theories_to_solver_state().
            debug_assert_eq!(
                self.registered_theory_var_upper_bound,
                self.theory_sync_state.theory_var_upper_bound,
                "sync contract violation: {} theory vars registered but only {} synced",
                self.registered_theory_var_upper_bound,
                self.theory_sync_state.theory_var_upper_bound,
            );
            debug_assert_eq!(
                self.terms.len(),
                self.theory_sync_state.term_count,
                "sync contract violation: {} terms interned but only {} synced",
                self.terms.len(),
                self.theory_sync_state.term_count,
            );
            match self.sat.solve() {
                SolveResult::Sat(model) => {
                    let result = self.check_theories_attributed(&model);
                    if matches!(
                        result,
                        TheoryBatchResult::Conflict(_, _) | TheoryBatchResult::Propagation(_)
                    ) {
                        self.apply_theory_phase_hints();
                    }
                    self.reset_theory_assignment_state();
                    match result {
                        TheoryBatchResult::Consistent => {
                            return SmtResult::Sat(self.build_model(&model));
                        }
                        TheoryBatchResult::Conflict(conflict_lits, source) => {
                            if let Some(r) = self.add_conflict_clause(&conflict_lits, source) {
                                return r;
                            }
                            // Forwarding conflict resolution (#2386) can route
                            // conflicts directly here even when the N-O fixpoint
                            // created new SAT variables. Re-sync so the next
                            // iteration's debug_assert sees all atoms as synced.
                            self.sync_theories_to_solver_state();
                        }
                        TheoryBatchResult::Propagation(props) => {
                            if let Some(r) = self.add_propagation_clauses(props) {
                                return r;
                            }
                            // Propagation batches can intern fresh theory atoms
                            // (for example, Nelson-Oppen equalities without an
                            // existing SAT variable). Re-sync before the next
                            // SAT iteration so `internalize_atom` runs for the
                            // newly registered literals before assert_literal.
                            self.sync_theories_to_solver_state();
                        }
                        TheoryBatchResult::Unknown => return SmtResult::Unknown,
                        TheoryBatchResult::Restart => {
                            self.sat.backtrack_to_root();
                            self.sat.reset_propagation_queue();
                            self.sync_theories_to_solver_state();
                        }
                    }
                }
                SolveResult::Unsat(_) => return self.take_unsat_core_result(),
                SolveResult::Unknown => return SmtResult::Unknown,
            }
        }
        SmtResult::Unknown
    }

    /// Check all theories for consistency, returning the source theory name
    /// for conflicts (#2442 Phase 2).
    ///
    /// Returns an internal batch result without widening the public SMT API.
    fn check_theories_attributed(&mut self, model: &[bool]) -> TheoryBatchResult {
        let mut propagations: Vec<AttributedPropagation> = Vec::new();
        let mut any_unknown = false;
        self.rebuild_assignment_stack_from_sat();

        if let Some(result) =
            self.assert_assignment_trail_to_theories(&mut propagations, &mut any_unknown)
        {
            return result;
        }
        // Nelson-Oppen fixpoint: collect + forward deduced equalities (#2366).
        let fixpoint_result = self.nelson_oppen_fixpoint(&mut propagations, model);
        match &fixpoint_result {
            NelsonOppenResult::Exhausted | NelsonOppenResult::ForwardingUnknown => {
                return TheoryBatchResult::Unknown;
            }
            NelsonOppenResult::ForwardingConflict(resolved_lits) => {
                // Forwarding conflict with resolved explanation (#2386):
                // dynamic SAT variables have been replaced with original
                // model-literal premises. Return as a direct conflict so the
                // CDCL solver learns in one iteration instead of two.
                let conflict_level = self.conflict_level(resolved_lits);
                self.backtrack_assignment_stack_to(conflict_level);
                return TheoryBatchResult::Conflict(resolved_lits.clone(), "forwarding");
            }
            NelsonOppenResult::Converged | NelsonOppenResult::ForwardingConflictUnresolved => {}
        }

        if !propagations.is_empty() {
            return TheoryBatchResult::Propagation(propagations);
        }
        if any_unknown {
            return TheoryBatchResult::Unknown;
        }
        if matches!(fixpoint_result, NelsonOppenResult::Converged) && self.emit_theory_lemmas() {
            return TheoryBatchResult::Restart;
        }

        // Check full consistency — skip if forwarding found a conflict,
        // since theory state may be corrupted (#2366).
        if let NelsonOppenResult::Converged = fixpoint_result {
            for idx in 0..self.theories.len() {
                self.theory_runtime_totals.record_check_call();
                let result = {
                    let theory = &self.theories[idx];
                    theory.check()
                };
                self.theory_runtime_totals.record_result(&result);
                let theory_name = self.theories[idx].name();
                match result {
                    TheoryCheckResult::Conflict(lits) => {
                        let conflict_level = self.conflict_level(&lits);
                        self.backtrack_assignment_stack_to(conflict_level);
                        return TheoryBatchResult::Conflict(lits, theory_name);
                    }
                    TheoryCheckResult::Propagation(lits) => {
                        propagations.extend(lits.into_iter().map(|(implied, explanation)| {
                            AttributedPropagation::new(implied, explanation, theory_name)
                        }));
                    }
                    TheoryCheckResult::Consistent => {}
                    TheoryCheckResult::Unknown => any_unknown = true,
                }
            }
        }

        if !propagations.is_empty() {
            TheoryBatchResult::Propagation(propagations)
        } else if any_unknown {
            TheoryBatchResult::Unknown // #2384: incomplete — cannot claim Consistent
        } else {
            TheoryBatchResult::Consistent
        }
    }

    /// Nelson-Oppen equality propagation fixpoint loop (#2366).
    ///
    /// All theories participate through the same trait hooks:
    /// `prepare_deduced_equalities()` + `drain_deduced_equalities()`.
    /// Replaces the former hard-coded array→EUF→forward→array→arithmetic
    /// sequence. Tracks deduction source to prevent circular forwarding.
    ///
    /// The `seen_deduced` and `deduction_source` temporaries are hoisted to
    /// `SmtSolver` fields (`fixpoint_seen_deduced`, `fixpoint_deduction_source`)
    /// so their heap capacity is amortized across DPLL(T) iterations (#2386).
    fn nelson_oppen_fixpoint(
        &mut self,
        propagations: &mut Vec<AttributedPropagation>,
        model: &[bool],
    ) -> NelsonOppenResult {
        const MAX_PASSES: usize = 100;
        self.clear_fixpoint_scratch();
        for _pass in 0..MAX_PASSES {
            let start = propagations.len();
            self.collect_theory_deduced_equalities(propagations, model);
            match self.forward_equality_deductions(propagations, start) {
                ForwardEqualityResult::Consistent => {}
                ForwardEqualityResult::Conflict(raw_conflict_lits) => {
                    // Try to resolve dynamic SAT variables in the conflict
                    // explanation back to their original model-literal premises
                    // (#2386). If resolution succeeds, return a direct conflict
                    // so the CDCL solver learns in one DPLL(T) iteration instead
                    // of the previous two-iteration workaround.
                    if let Some(resolved) =
                        self.resolve_forwarding_conflict(&raw_conflict_lits, propagations, start)
                    {
                        return NelsonOppenResult::ForwardingConflict(resolved);
                    }
                    // Resolution failed (for example, an unsynced
                    // opposite-polarity reference to a forwarding-created
                    // atom). Fall back to the legacy path: return
                    // propagations and let the next DPLL(T) iteration
                    // rediscover the conflict.
                    return NelsonOppenResult::ForwardingConflictUnresolved;
                }
                ForwardEqualityResult::Unknown => {
                    return NelsonOppenResult::ForwardingUnknown;
                }
            }
            if propagations.len() == start {
                return NelsonOppenResult::Converged;
            }
        }
        NelsonOppenResult::Exhausted
    }

    /// Build an SMT model from a SAT model
    fn build_model(&self, sat_model: &[bool]) -> SmtModel {
        let mut equalities = Vec::new();
        let mut disequalities = Vec::new();

        for (&var, theory_lit) in &self.var_to_theory {
            let value = sat_model[var.index()];
            if let TheoryLiteral::Eq(a, b) = theory_lit {
                if value {
                    equalities.push((*a, *b));
                } else {
                    disequalities.push((*a, *b));
                }
            }
        }

        SmtModel {
            sat_model: sat_model.to_vec(),
            equalities,
            disequalities,
        }
    }
}
