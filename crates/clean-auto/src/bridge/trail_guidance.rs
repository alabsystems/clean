// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trail-guided hypothesis filtering and proof reconstruction support.
//!
//! After an UNSAT result, the DPLL(T) proof trail records which theory
//! conflicts and propagations contributed to unsatisfiability. This module
//! maps those trail events back to the hypothesis FVarIds that introduced
//! the relevant SAT variables, enabling proof reconstruction to focus on
//! the most relevant hypotheses first.
//!
//! # Trail-Guided Iteration Order
//!
//! [`SmtBridge::iter_guided_hypotheses`] yields hypotheses in two phases:
//! 1. Trail-hinted hypotheses (those whose SAT variables appeared in the trail)
//! 2. Remaining hypotheses (fallback for complete search)

use crate::smt::{ProofTrailEntry, TheoryLiteral};
use clean_kernel::{Expr, FVarId};
use std::collections::HashSet;

use super::SmtBridge;

impl<'env> SmtBridge<'env> {
    /// Filter prop_hypotheses to only those that participated in the UNSAT core (#349, #2442).
    ///
    /// Maps UNSAT core clause indices through `clause_origins` to find which
    /// hypothesis FVarIds contributed to unsatisfiability. If a non-empty core
    /// set is found, prunes `prop_hypotheses` to just those hypotheses.
    /// This focuses proof reconstruction on the relevant subset, improving
    /// both speed and success rate.
    pub(super) fn filter_hypotheses_by_core(&mut self, core: &crate::smt::UnsatCore) {
        let core_fvars: HashSet<FVarId> = core
            .clauses
            .iter()
            .filter_map(|cref| self.clause_origins.get(cref.index()).copied().flatten())
            .collect();
        // Only filter if we found at least one core hypothesis.
        // An empty core_fvars means the core clauses had no tracked origins
        // (e.g., goal negation clauses), so keep all hypotheses as fallback.
        if !core_fvars.is_empty() {
            self.prop_hypotheses
                .retain(|(fvar, _)| core_fvars.contains(fvar));
        }
    }

    /// Get SMT solver statistics for crate-internal tests and diagnostics.
    #[allow(dead_code)] // ay API contract + test-used; waiver in .code_quality_waivers.toml
    pub(crate) fn stats(&self) -> crate::smt::SmtStats {
        self.smt.stats()
    }

    /// Get the proof trail from the last solve() call (#2442 Phase 2).
    ///
    /// Returns the sequence of theory-level events (conflicts, propagations)
    /// recorded during DPLL(T) solving. The bridge can use this to understand
    /// which theory interactions led to UNSAT and guide proof reconstruction.
    pub(crate) fn proof_trail(&self) -> &[ProofTrailEntry] {
        self.smt.proof_trail()
    }

    /// Check whether the UNSAT result involved theory-level events (#2442 Phase 2).
    ///
    /// Returns `true` if the proof trail contains any theory conflicts or
    /// propagations, meaning the UNSAT derivation required theory reasoning
    /// (not just propositional SAT). This guides proof reconstruction:
    /// - Empty trail → pure propositional contradiction → prop_reconstruction should suffice
    /// - Non-empty trail → theory-aided → may need equality or arithmetic proof paths
    pub(crate) fn has_theory_events(&self) -> bool {
        !self.smt.proof_trail().is_empty()
    }

    /// Count theory conflicts and propagations in the proof trail (#2442 Phase 2).
    pub(crate) fn trail_event_counts(&self) -> (usize, usize) {
        let mut conflicts = 0;
        let mut propagations = 0;
        for entry in self.smt.proof_trail() {
            match entry {
                ProofTrailEntry::TheoryConflict { .. } => conflicts += 1,
                ProofTrailEntry::TheoryPropagation { .. } => propagations += 1,
            }
        }
        (conflicts, propagations)
    }

    /// Resolve theory conflict literals to their theory-level meanings (#2442 Phase 2).
    ///
    /// For each `TheoryConflict` in the trail, maps the SAT conflict literals
    /// back to `TheoryLiteral` values via `SmtSolver::lit_to_theory_literal`.
    /// Returns the resolved conflicts as `(theory_name, Vec<TheoryLiteral>)`.
    /// Literals without theory mappings (auxiliary SAT variables) are skipped.
    pub(crate) fn trail_conflict_theories(&self) -> Vec<(&'static str, Vec<TheoryLiteral>)> {
        let mut result = Vec::new();
        for entry in self.smt.proof_trail() {
            if let ProofTrailEntry::TheoryConflict {
                conflict_theory_lits,
                theory_name,
                ..
            } = entry
            {
                if !conflict_theory_lits.is_empty() {
                    result.push((*theory_name, conflict_theory_lits.clone()));
                }
            }
        }
        result
    }

    /// Record that a theory literal originated from a tracked hypothesis.
    pub(super) fn record_theory_literal_origin(
        &mut self,
        theory_lit: &TheoryLiteral,
        fvar: Option<FVarId>,
    ) {
        let Some(fvar) = fvar else {
            return;
        };
        let Some(sat_lit) = self.smt.theory_literal_to_sat_literal(theory_lit) else {
            return;
        };
        self.sat_var_origins
            .entry(sat_lit.var().raw())
            .or_default()
            .insert(fvar);
    }

    /// Record the hypothesis origin for each literal in a SAT clause.
    pub(super) fn record_clause_literal_origins(
        &mut self,
        theory_lits: &[TheoryLiteral],
        fvar: Option<FVarId>,
    ) {
        for theory_lit in theory_lits {
            self.record_theory_literal_origin(theory_lit, fvar);
        }
    }

    /// Map proof-trail literals back to the hypothesis FVarIds that introduced them.
    fn collect_trail_hypothesis_hints(&self) -> HashSet<FVarId> {
        let mut hints = HashSet::new();
        let mut record_lit = |lit: crate::cdcl::Lit| {
            if self.smt.lit_to_theory_literal(lit).is_none() {
                return;
            }
            if let Some(origins) = self.sat_var_origins.get(&lit.var().raw()) {
                hints.extend(origins.iter().copied());
            }
        };

        for entry in self.smt.proof_trail() {
            match entry {
                ProofTrailEntry::TheoryConflict { conflict_lits, .. } => {
                    for lit in conflict_lits {
                        record_lit(*lit);
                    }
                }
                ProofTrailEntry::TheoryPropagation {
                    implied,
                    explanation,
                    ..
                } => {
                    record_lit(*implied);
                    for lit in explanation {
                        record_lit(*lit);
                    }
                }
            }
        }

        hints
    }

    /// Refresh trail-guided hypothesis hints after an UNSAT solve.
    pub(super) fn refresh_trail_hypothesis_hints(&mut self) {
        self.trail_hypothesis_hints = self.collect_trail_hypothesis_hints();
    }

    /// Iterate hypotheses with trail-related ones first, then fall back to the rest.
    pub(super) fn iter_guided_hypotheses(&self) -> impl Iterator<Item = (FVarId, &Expr)> + '_ {
        let hints = &self.trail_hypothesis_hints;
        let hinted = self
            .prop_hypotheses
            .iter()
            .filter(move |(fvar, _)| hints.contains(fvar))
            .map(|(fvar, expr)| (*fvar, expr));
        let hints = &self.trail_hypothesis_hints;
        let fallback = self
            .prop_hypotheses
            .iter()
            .filter(move |(fvar, _)| !hints.contains(fvar))
            .map(|(fvar, expr)| (*fvar, expr));
        hinted.chain(fallback)
    }
}
