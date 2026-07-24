// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared non-sort local-hypothesis contract for the SMT decide tactic.
//!
//! Both the primary SMT bridge lane and the superposition recovery lane
//! need to enumerate the same set of usable hypotheses from the goal's
//! local context. This module owns that single contract so the two paths
//! cannot drift.

use crate::tactic::{Goal, ProofState};
use clean_kernel::{Expr, FVarId};

/// Invoke `f` for each non-sort local hypothesis in the goal context.
///
/// "Non-sort" means the instantiated type is not a `Sort` expression
/// (i.e., not `Type u` or `Prop` used as a type universe).
///
/// # Contract
///
/// REQUIRES: `goal.local_ctx` contains the current goal's local declarations
/// ENSURES: `f` is called exactly once for each `decl` where `!instantiate(decl.ty).is_sort()`
/// ENSURES: The yielded `Expr` is the instantiated hypothesis type
pub(in crate::tactic::smt) fn for_each_non_sort_goal_hypothesis(
    state: &ProofState,
    goal: &Goal,
    mut f: impl FnMut(Expr, FVarId),
) {
    for decl in &goal.local_ctx {
        let hyp_ty = state.metas.instantiate(&decl.ty);
        if !hyp_ty.is_sort() {
            f(hyp_ty, decl.fvar);
        }
    }
}

/// Add hypotheses from the goal's local context to the SMT bridge.
///
/// Unsupported hypothesis types produce errors that are logged but not fatal —
/// partial hypothesis coverage still enables proving many goals (#2391).
///
/// # Contract
///
/// REQUIRES: `goal.local_ctx` contains the current goal's local declarations
/// ENSURES: All translatable hypotheses are added to `bridge`
/// ENSURES: Untranslatable hypotheses are silently dropped with a warning
pub(in crate::tactic::smt) fn add_hypotheses_from_context(
    state: &ProofState,
    goal: &Goal,
    bridge: &mut clean_auto::bridge::SmtBridge<'_>,
) {
    let mut dropped_hypotheses = 0u32;
    for_each_non_sort_goal_hypothesis(state, goal, |hyp_ty, fvar| {
        if let Err(_e) = bridge.add_hypothesis_with_fvar(&hyp_ty, Some(fvar)) {
            dropped_hypotheses += 1;
        }
    });
    if dropped_hypotheses > 0 {
        tracing::warn!(
            dropped = dropped_hypotheses,
            "hypothesis(es) dropped (unsupported by SMT bridge)"
        );
    }
}
