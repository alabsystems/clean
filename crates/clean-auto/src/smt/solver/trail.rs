// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-trail helpers for `SmtSolver` (#2442 Phase 2).

use super::{AttributedPropagation, SmtSolver};
use crate::cdcl::Lit;
use crate::smt::{ProofTrailEntry, SmtResult, TheoryLiteral};

impl SmtSolver {
    fn equality_literal_to_sat_literal(
        &self,
        lhs: crate::smt::TermId,
        rhs: crate::smt::TermId,
        positive: bool,
    ) -> Option<Lit> {
        self.equality_var(lhs, rhs).map(|var| {
            if positive {
                Lit::pos(var)
            } else {
                Lit::neg(var)
            }
        })
    }

    /// Get the proof trail from the last `solve()` call (#2442 Phase 2).
    ///
    /// The trail records theory-level conflict and propagation events during
    /// DPLL(T) solving. The bridge uses this to guide proof term construction
    /// instead of blind propositional search.
    pub(crate) fn proof_trail(&self) -> &[ProofTrailEntry] {
        &self.proof_trail
    }

    /// Add a theory conflict blocking clause and record in proof trail (#2442 Phase 2).
    /// Returns `Some(SmtResult)` if UNSAT, `None` to continue the DPLL(T) loop.
    pub(super) fn add_conflict_clause(
        &mut self,
        conflict_lits: &[Lit],
        source: &'static str,
    ) -> Option<SmtResult> {
        let clause: Vec<Lit> = conflict_lits.iter().map(|lit| lit.not()).collect();
        let cref = self.sat.add_theory_clause(clause);
        let conflict_theory_lits = self.resolve_theory_literals(conflict_lits);
        self.proof_trail.push(ProofTrailEntry::TheoryConflict {
            conflict_lits: conflict_lits.to_vec(),
            conflict_theory_lits,
            theory_name: source,
            clause_index: cref.map(|clause_ref| clause_ref.raw()),
        });
        if cref.is_none() {
            return Some(self.take_unsat_core_result());
        }
        self.sat.backtrack_to_root();
        self.sat.reset_propagation_queue();
        None
    }

    /// Add theory propagation clauses and record in proof trail (#2442 Phase 2).
    /// Returns `Some(SmtResult)` if UNSAT, `None` to continue the DPLL(T) loop.
    pub(super) fn add_propagation_clauses(
        &mut self,
        props: Vec<AttributedPropagation>,
    ) -> Option<SmtResult> {
        for propagation in props {
            let AttributedPropagation {
                implied: lit,
                explanation,
                theory_name,
            } = propagation;
            let mut clause: Vec<Lit> = explanation.iter().map(|premise| premise.not()).collect();
            clause.push(lit);
            let cref = self.sat.add_theory_clause(clause);
            let implied_theory_lit = self.lit_to_theory_literal(lit);
            let explanation_theory_lits = self.resolve_theory_literals(&explanation);
            self.proof_trail.push(ProofTrailEntry::TheoryPropagation {
                implied: lit,
                implied_theory_lit,
                explanation,
                explanation_theory_lits,
                theory_name,
                clause_index: cref.map(|clause_ref| clause_ref.raw()),
            });
            if cref.is_none() {
                return Some(self.take_unsat_core_result());
            }
        }
        self.sat.backtrack_to_root();
        self.sat.reset_propagation_queue();
        None
    }

    /// Map a SAT literal to its corresponding theory literal (#2442 Phase 2).
    ///
    /// Returns the theory literal for a positive literal, or its negation for
    /// a negative literal. Returns `None` if the variable has no theory mapping
    /// (e.g., auxiliary Boolean variables introduced by the SAT solver).
    pub(crate) fn lit_to_theory_literal(&self, lit: Lit) -> Option<TheoryLiteral> {
        self.var_to_theory.get(&lit.var()).map(|theory_lit| {
            if lit.is_pos() {
                theory_lit.clone()
            } else {
                theory_lit.negate()
            }
        })
    }

    /// Resolve SAT literals to theory literals for proof-trail payloads.
    fn resolve_theory_literals(&self, lits: &[Lit]) -> Vec<TheoryLiteral> {
        lits.iter()
            .filter_map(|lit| self.lit_to_theory_literal(*lit))
            .collect()
    }

    /// Map a theory literal back to its SAT literal.
    ///
    /// Returns the SAT literal for tracked theory atoms, preserving polarity for
    /// negative forms like `Neq`/`NegBool`. Equality/disequality lookups are
    /// orientation-insensitive because the SAT layer tracks one shared equality
    /// atom regardless of `(lhs, rhs)` order. Returns `None` if the literal has
    /// not been interned into the SAT layer yet.
    pub(crate) fn theory_literal_to_sat_literal(&self, theory_lit: &TheoryLiteral) -> Option<Lit> {
        match theory_lit {
            TheoryLiteral::Eq(lhs, rhs) => self.equality_literal_to_sat_literal(*lhs, *rhs, true),
            TheoryLiteral::Neq(lhs, rhs) => self.equality_literal_to_sat_literal(*lhs, *rhs, false),
            TheoryLiteral::Lt(lhs, rhs) => self
                .theory_var_for_literal(&TheoryLiteral::Lt(*lhs, *rhs))
                .map(Lit::pos),
            TheoryLiteral::Le(lhs, rhs) => self
                .theory_var_for_literal(&TheoryLiteral::Le(*lhs, *rhs))
                .map(Lit::pos),
            TheoryLiteral::Bool(var) => self
                .theory_var_for_literal(&TheoryLiteral::Bool(*var))
                .map(Lit::pos),
            TheoryLiteral::NegBool(var) => self
                .theory_var_for_literal(&TheoryLiteral::Bool(*var))
                .map(Lit::neg),
        }
    }
}
