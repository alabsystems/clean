// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen theory propagation collection for DPLL(T).
//!
//! These methods are part of `SmtSolver` but separated for file size
//! management. They collect theory-deduced equalities and forward them
//! as SAT propagations, implementing the Nelson-Oppen combination.
//!
//! # Architecture (#2366)
//!
//! All theories participate through trait hooks:
//! - `prepare_deduced_equalities()` — pre-drain computation step
//! - `drain_deduced_equalities()` — surface deduced equality pairs
//!
//! The solver-side `collect_theory_deduced_equalities` iterates all
//! theories uniformly. Theory name no longer controls propagation
//! routing — any theory can surface equalities through the same path.
//! Cross-theory forwarding uses a cursor-driven work queue so new
//! propagations appended during forwarding are visited in the same pass.

use super::solver::{AttributedPropagation, ForwardEqualityResult, SmtSolver};
use super::{TheoryCheckResult, TheoryLiteral};
use crate::cdcl::Lit;
use std::collections::HashSet;

impl SmtSolver {
    /// Collect deduced equalities from all theories via trait hooks (#2366).
    ///
    /// Iterates all theories, calls `prepare_deduced_equalities()` then
    /// `drain_deduced_equalities()`, and converts the combined batch through
    /// the existing SAT conversion logic. Theory name no longer controls
    /// propagation routing — any theory can surface equalities.
    ///
    /// Uses `self.fixpoint_seen_deduced` to track equality pairs already
    /// converted in this `check_theories_attributed` call so the outer
    /// fixpoint loop only treats newly converted equalities as progress.
    ///
    /// Uses `self.fixpoint_deduction_source` to record which theory (by index)
    /// originated each deduced equality's SAT variable. Used by
    /// `forward_equality_deductions` to skip forwarding equalities back to the
    /// originating theory (proper Nelson-Oppen: only forward to OTHER theories).
    pub(super) fn collect_theory_deduced_equalities(
        &mut self,
        propagations: &mut Vec<AttributedPropagation>,
        model: &[bool],
    ) {
        // Collect equalities from each theory, tagged with source index.
        let mut batch: Vec<(_, _, Vec<Lit>, usize)> = Vec::new();
        for (idx, theory) in self.theories.iter_mut().enumerate() {
            theory.prepare_deduced_equalities();
            batch.extend(
                theory
                    .drain_deduced_equalities()
                    .into_iter()
                    .map(|(t1, t2, expl)| (t1, t2, expl, idx)),
            );
        }

        let fresh: Vec<_> = batch
            .into_iter()
            .filter(|(t1, t2, _, _)| self.mark_fixpoint_equality_seen(*t1, *t2))
            .collect();

        self.convert_deduced_to_propagations(fresh, propagations, model);
    }

    /// Convert deduced equality triples to SAT propagations (#2391).
    ///
    /// Shared logic for the generic propagation collector.
    /// Creates SAT variables on demand when no mapping exists (#2325).
    /// Checks both `(t1, t2)` and `(t2, t1)` orderings (#2314).
    /// Skips propagation for equalities already true in `model`.
    /// Records source theory index in `self.fixpoint_deduction_source` for
    /// forwarding.
    fn convert_deduced_to_propagations(
        &mut self,
        deduced: Vec<(super::TermId, super::TermId, Vec<Lit>, usize)>,
        propagations: &mut Vec<AttributedPropagation>,
        model: &[bool],
    ) {
        for (t1, t2, explanation, source_idx) in deduced {
            let eq_lit = TheoryLiteral::Eq(t1, t2);
            let theory_name = self.theories[source_idx].name();
            let var = if let Some(v) = self.equality_var(t1, t2) {
                if model.get(v.index()).copied() == Some(true) {
                    continue;
                }
                v
            } else {
                self.get_or_create_var(eq_lit)
            };
            self.record_fixpoint_deduction_source(var, source_idx);
            propagations.push(AttributedPropagation::new(
                Lit::pos(var),
                explanation,
                theory_name,
            ));
        }
    }

    /// Forward equality propagations to all OTHER theories using a cursor-driven
    /// work queue (#2353, #2366).
    ///
    /// `eq_prop_start` marks where the equality propagations begin in
    /// `propagations`. Uses a mutable cursor instead of a fixed range so
    /// new propagations appended during forwarding are visited in the same
    /// call — this is the correct primitive for the fixpoint loop.
    ///
    /// Uses `self.fixpoint_deduction_source` to map SAT variables to the
    /// theory index that originated the deduction. Forwarding skips the
    /// originating theory (proper Nelson-Oppen: share equalities with OTHER
    /// theories only). Variables not in the map (e.g., from
    /// forwarding-generated propagations) are forwarded to all theories.
    ///
    /// Returns whether forwarding stayed consistent, hit a conflict, or
    /// encountered an incomplete (`Unknown`) peer theory result.
    pub(super) fn forward_equality_deductions(
        &mut self,
        propagations: &mut Vec<AttributedPropagation>,
        eq_prop_start: usize,
    ) -> ForwardEqualityResult {
        let mut cursor = eq_prop_start;
        while cursor < propagations.len() {
            let propagated_lit = propagations[cursor].implied;
            cursor += 1;
            let Some((t1, t2)) =
                self.theory_literal_for_var(propagated_lit.var())
                    .and_then(|theory_lit| match theory_lit {
                        TheoryLiteral::Eq(t1, t2) => Some((*t1, *t2)),
                        _ => None,
                    })
            else {
                continue;
            };

            let source_idx = self.fixpoint_deduction_source(propagated_lit.var());
            for idx in 0..self.theories.len() {
                // Skip forwarding back to the originating theory.
                if source_idx == Some(idx) {
                    continue;
                }
                // Use dedicated shared equality/disequality methods (#2386)
                // so theories can distinguish cross-theory forwarding from
                // direct SAT-model assertions. Converges with ay's
                // assert_shared_equality/assert_shared_disequality.
                let result = if propagated_lit.is_pos() {
                    let theory = &mut self.theories[idx];
                    theory.assert_shared_equality(t1, t2, propagated_lit)
                } else {
                    let theory = &mut self.theories[idx];
                    theory.assert_shared_disequality(t1, t2, propagated_lit)
                };
                self.record_theory_runtime_result(&result);
                let theory_name = self.theories[idx].name();
                match result {
                    TheoryCheckResult::Conflict(conflict_lits) => {
                        return ForwardEqualityResult::Conflict(conflict_lits);
                    }
                    TheoryCheckResult::Propagation(new_props) => {
                        // Tag forwarding-generated propagations with
                        // the theory that produced them so they are
                        // not forwarded back to the same theory.
                        for &(lit, _) in &new_props {
                            self.record_fixpoint_deduction_source(lit.var(), idx);
                        }
                        propagations.extend(new_props.into_iter().map(|(implied, explanation)| {
                            AttributedPropagation::new(implied, explanation, theory_name)
                        }));
                    }
                    TheoryCheckResult::Unknown => return ForwardEqualityResult::Unknown,
                    TheoryCheckResult::Consistent => {}
                }
            }
        }
        ForwardEqualityResult::Consistent
    }

    /// Resolve a forwarding conflict's explanation by replacing dynamic
    /// SAT variables (created during forwarding) with their original
    /// explanation premises (#2386).
    ///
    /// When a theory returns `Conflict(lits)` during forwarding, the
    /// explanation may reference SAT literals created on-the-fly by
    /// `convert_deduced_to_propagations`. These dynamic variables have
    /// no SAT clause yet, so the CDCL solver cannot learn from them.
    ///
    /// Resolution replaces each dynamic lit with the premises of the
    /// propagation entry that introduced it:
    /// - Conflict says: "L_dynamic AND L_model → false"
    /// - Propagation says: "P1 AND ... AND Pn → L_dynamic"
    /// - Resolved: "P1 AND ... AND Pn AND L_model → false"
    ///
    /// Only exact-match lits (same var AND polarity) are resolved. Lits
    /// sharing a var with a forwarding entry but at opposite polarity are
    /// only safe to keep when the SAT variable already existed before this
    /// fixpoint pass. If the variable was created on-the-fly for the
    /// propagation, the opposite polarity has no learned clause behind it yet
    /// and the direct-conflict shortcut must fail closed.
    ///
    /// This is iterated until no dynamic lits remain (handles multi-hop
    /// forwarding chains).
    pub(super) fn resolve_forwarding_conflict(
        &self,
        conflict_lits: &[Lit],
        propagations: &[AttributedPropagation],
        eq_prop_start: usize,
    ) -> Option<Vec<Lit>> {
        let forwarding_lits: HashSet<Lit> = propagations[eq_prop_start..]
            .iter()
            .map(|propagation| propagation.implied)
            .collect();
        let forwarding_vars: HashSet<_> = forwarding_lits.iter().map(|lit| lit.var()).collect();

        let mut resolved = conflict_lits.to_vec();
        loop {
            let mut next = Vec::with_capacity(resolved.len());
            let mut any_resolved = false;
            for &lit in &resolved {
                if forwarding_lits.contains(&lit) {
                    // Exact match: replace with the original premises.
                    let premises = propagations[eq_prop_start..]
                        .iter()
                        .find(|propagation| propagation.implied == lit)
                        .map(|propagation| &propagation.explanation)
                        .expect("invariant: every forwarding lit has a propagation entry");
                    next.extend_from_slice(premises);
                    any_resolved = true;
                } else if forwarding_vars.contains(&lit.var())
                    && !self.is_theory_var_synced(lit.var())
                {
                    // The conflict references the opposite polarity of a
                    // forwarding-created atom that has no SAT clause yet. Do
                    // not learn a direct clause from an explanation the CDCL
                    // core cannot justify; fall back to the two-iteration path.
                    return None;
                } else {
                    // Model lit or pre-existing opposite-polarity var: keep as-is.
                    next.push(lit);
                }
            }
            if !any_resolved {
                break;
            }
            resolved = next;
        }

        // Deduplicate exact repeats from multi-hop resolution paths while
        // preserving polarity.
        let mut seen = HashSet::new();
        resolved.retain(|lit| seen.insert(*lit));
        Some(resolved)
    }
}
