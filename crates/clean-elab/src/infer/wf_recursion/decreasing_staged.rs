// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The staged Lean4-parity `solve_decreasing_obligation` scaffold: user
//! `decreasing_by` -> `simp_arith` -> `mathverse` -> unresolved metavariable.
//!
//! It has NO production caller (its metavariable fallback is exactly what the
//! fail-closed contract in `decreasing.rs` forbids) and is kept per the
//! keep-and-annotate doctrine. Split out of `decreasing.rs` for file size.

use super::*;

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
impl<'a> ElabCtx<'a> {
    /// Discharge a decreasing proof obligation, trying multiple strategies.
    ///
    /// 1. If `decreasing_tactic` is provided, run it on the goal.
    /// 2. Otherwise, try the default cascade: `simp_arith`, then `mathverse`.
    /// 3. If all else fails, produce a `sorry` term.
    pub(crate) fn solve_decreasing_obligation(
        &mut self,
        obligation: &DecreasingObligation,
        decreasing_tactic: Option<&[SurfaceTactic]>,
    ) -> DecreasingProof {
        // Strategy 1: User-provided decreasing_by tactic
        if let Some(tactics) = decreasing_tactic {
            if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, tactics) {
                return DecreasingProof {
                    proof,
                    strategy: DecreasingStrategy::UserTactic,
                };
            }
        }

        // Strategy 2: Default simp_arith
        let simp_arith_tac = vec![SurfaceTactic::Named {
            span: clean_parser::Span::dummy(),
            name: "simp_arith".to_owned(),
            args: vec![],
        }];
        if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, &simp_arith_tac) {
            return DecreasingProof {
                proof,
                strategy: DecreasingStrategy::SimpArith,
            };
        }

        // Strategy 3: Default mathverse
        let mathverse_tac = vec![SurfaceTactic::Named {
            span: clean_parser::Span::dummy(),
            name: "mathverse".to_owned(),
            args: vec![],
        }];
        if let Ok(proof) = self.try_tactic_on_goal(&obligation.goal_type, &mathverse_tac) {
            return DecreasingProof {
                proof,
                strategy: DecreasingStrategy::Mathverse,
            };
        }

        // Fallback: leave the obligation as an unresolved metavariable rather
        // than manufacturing an unchecked proof term.
        let proof = self.fresh_meta(obligation.goal_type.clone());
        DecreasingProof {
            proof,
            strategy: DecreasingStrategy::Sorry,
        }
    }

    /// Build decreasing proofs for all recursive call sites in a function body.
    ///
    /// Scans the transformed body for sorry placeholders and attempts to
    /// replace them with actual proofs using the specified strategy.
    ///
    /// This is called after `transform_rec_calls` which inserts sorry terms
    /// as placeholders for decreasing proof obligations.
    pub(crate) fn solve_all_decreasing_obligations(
        &mut self,
        body: &Expr,
        _measure_fn: &Expr,
        _current_arg: &Expr,
        _decreasing_tactic: Option<&[SurfaceTactic]>,
    ) -> (Expr, Vec<DecreasingStrategy>) {
        // For now, the sorry-based approach from transform_rec_calls is retained.
        // When we detect sorry terms that serve as decreasing proofs, we attempt
        // to replace them. In the current architecture, sorry terms are inserted
        // directly by the rec call replacement and are not easily distinguishable
        // from other sorry terms.
        //
        // A more refined implementation would:
        // 1. During rec call replacement, tag each sorry with metadata
        // 2. Walk the body and collect all tagged sorry terms
        // 3. For each, build the obligation and try to solve it
        //
        // For now, we report that sorry was used for all obligations.
        (body.clone(), vec![DecreasingStrategy::Sorry])
    }
}
