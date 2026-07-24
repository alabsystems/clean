// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::EqualityTheory;
use crate::cdcl::Lit;
use crate::egraph::MergeReason as EgraphMergeReason;
use crate::proof::UnionReason;
use crate::smt::{SmtTerm, TermId};
use std::collections::HashMap;

impl EqualityTheory {
    /// Take the class-members snapshot for use in `assert_equality`.
    ///
    /// When `class_members_valid` is true, the buffer already reflects current
    /// pre-union canonical IDs and is returned as-is (O(1) amortized). Otherwise
    /// falls back to a full O(T) rebuild from `term_to_eclass` (#2406).
    ///
    /// Returns the snapshot as an owned `HashMap` (taken out of `self` via
    /// `std::mem::take`) so the caller can pass `&snapshot` to methods that
    /// take `&mut self` without a borrow conflict. The caller MUST assign
    /// the map back to `self.class_members_buf` after use and call
    /// `update_class_members_after_union` to preserve incremental validity.
    pub(super) fn take_class_members_snapshot(&mut self) -> HashMap<u32, Vec<TermId>> {
        if self.class_members_valid {
            return std::mem::take(&mut self.class_members_buf);
        }
        // Full rebuild when incremental state is stale (first call, after
        // backtrack, or after reset).
        let mut members = std::mem::take(&mut self.class_members_buf);
        members.clear();
        for (&tid, &ec) in &self.term_to_eclass {
            let canonical = self.egraph.find_const(ec).id();
            members.entry(canonical).or_default().push(tid);
        }
        members
    }

    /// Update `class_members_buf` to reflect post-union canonical IDs (#2406).
    ///
    /// Processes only the merges that occurred during the last `egraph.union()`
    /// call (from `history_start` onward), making this O(merges) instead of
    /// O(T). For each merge `(ec1, ec2)`, the entries under the old canonicals
    /// are combined under the new canonical.
    pub(super) fn update_class_members_after_union(&mut self, history_start: usize) {
        let history_len = self.egraph.merge_history().len();
        for i in history_start..history_len {
            let ec1_id = self.egraph.merge_history()[i].ec1.id();
            let ec2_id = self.egraph.merge_history()[i].ec2.id();
            let new_canonical = self
                .egraph
                .find_const(self.egraph.merge_history()[i].ec1)
                .id();

            // Remove entries for both old canonicals and merge into new canonical.
            let members1 = self.class_members_buf.remove(&ec1_id).unwrap_or_default();
            let members2 = self.class_members_buf.remove(&ec2_id).unwrap_or_default();
            if !members1.is_empty() || !members2.is_empty() {
                let entry = self.class_members_buf.entry(new_canonical).or_default();
                entry.extend(members1);
                entry.extend(members2);
            }
        }
    }

    /// Record congruence merges from E-graph merge history into proof trace,
    /// and populate `pending_deduced` with newly-equal registered term pairs (#2344).
    ///
    /// Uses index-based iteration over `merge_history` to avoid allocating a
    /// Vec per call (#2406). The borrow on `self.egraph.merge_history()` is
    /// released between iterations by indexing into the slice.
    ///
    /// `pre_union_members` maps canonical E-class ID (before the union) to all
    /// registered TermIds in that class. This snapshot is needed because after
    /// the merge, `find_const` returns the same canonical for both sides.
    pub(super) fn record_congruence_merges(
        &mut self,
        history_start: usize,
        pre_union_members: &HashMap<u32, Vec<TermId>>,
    ) {
        // Skip the first merge (the direct assertion merge) — start at +1.
        let mut idx = history_start + 1;
        loop {
            let history_len = self.egraph.merge_history().len();
            if idx >= history_len {
                break;
            }
            // Extract fields by value/clone to release the borrow on self.egraph
            // before calling methods that need &mut self.
            let merge = &self.egraph.merge_history()[idx];
            let merge_ec1 = merge.ec1;
            let merge_ec2 = merge.ec2;
            let reason = merge.reason.clone();
            idx += 1;

            match &reason {
                EgraphMergeReason::Congruence {
                    func,
                    children1,
                    children2,
                } => {
                    let arg_reasons: Vec<u32> = children1
                        .iter()
                        .zip(children2.iter())
                        .filter_map(|(c1, c2)| {
                            if c1.id() == c2.id() {
                                None
                            } else {
                                self.proof_trace
                                    .get_proof_index(c1.id(), c2.id())
                                    .map(|idx| {
                                        u32::try_from(idx)
                                            .expect("invariant: proof trace index fits in u32")
                                    })
                            }
                        })
                        .collect();

                    self.proof_trace.record_union(
                        merge_ec1.id(),
                        merge_ec2.id(),
                        UnionReason::Congruence {
                            func: func.name().to_string(),
                            app1: merge_ec1.id(),
                            app2: merge_ec2.id(),
                            arg_reasons,
                        },
                    );

                    let func_name = func.name();
                    let find_app_term =
                        |members: &HashMap<u32, Vec<TermId>>, ec_id: u32| -> Option<TermId> {
                            members.get(&ec_id)?.iter().copied().find(|&tid| {
                                matches!(
                                    &self.terms[tid.index()],
                                    SmtTerm::App(f, _) if f.name() == func_name
                                )
                            })
                        };
                    let term1 = find_app_term(pre_union_members, merge_ec1.id());
                    let term2 = find_app_term(pre_union_members, merge_ec2.id());
                    if let (Some(t1), Some(t2)) = (term1, term2) {
                        if let (SmtTerm::App(_, args1), SmtTerm::App(_, args2)) =
                            (&self.terms[t1.index()], &self.terms[t2.index()])
                        {
                            let arg_pairs: Vec<(TermId, TermId)> = args1
                                .iter()
                                .zip(args2.iter())
                                .filter(|(a, b)| a != b)
                                .map(|(a, b)| (*a, *b))
                                .collect();
                            self.proof_forest.record_merge(
                                t1,
                                t2,
                                crate::proof::ForestReason::Congruence(arg_pairs),
                                self.level,
                            );
                        }
                    }

                    self.emit_cross_boundary_pair(
                        pre_union_members,
                        merge_ec1.id(),
                        merge_ec2.id(),
                    );
                }
                EgraphMergeReason::External => {}
            }
        }
    }

    /// Emit ONE cross-boundary pair of registered terms from two pre-merge
    /// classes into `pending_deduced` (#2344). O(1) per merge.
    pub(super) fn emit_cross_boundary_pair(
        &mut self,
        pre_union_members: &HashMap<u32, Vec<TermId>>,
        class_a: u32,
        class_b: u32,
    ) {
        let first_a = pre_union_members
            .get(&class_a)
            .and_then(|members| members.first().copied());
        let first_b = pre_union_members
            .get(&class_b)
            .and_then(|members| members.first().copied());
        if let (Some(ta), Some(tb)) = (first_a, first_b) {
            self.pending_deduced.push((ta, tb));
        }
    }

    /// Drain newly deduced equalities since last call (#2344).
    ///
    /// Each call returns fresh equalities only — O(D) where D is
    /// the number of new congruence deductions since last drain, not O(T^2).
    /// Used by Nelson-Oppen theory combination (#2302).
    ///
    /// Each deduction includes a precise explanation: the subset of asserted
    /// SAT literals that caused the equality, extracted from the E-graph's
    /// proof trace (#2344 criterion 4). Falls back to the conservative
    /// over-approximation (all asserted lits) when the proof trace is incomplete.
    pub fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
        let pairs = std::mem::take(&mut self.pending_deduced);
        pairs
            .into_iter()
            .map(|(t1, t2)| {
                let explanation = self.explain_why_equal(t1, t2);
                (t1, t2, explanation)
            })
            .collect()
    }
}
