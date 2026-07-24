// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! peel tactic: strip matching universal quantifiers from a hypothesis and the goal.

use crate::stack_safe;
use clean_kernel::{Expr, ExprKind};

use super::super::{intro, ProofState, TacticError, TacticResult};

/// peel tactic: strip universal quantifiers and apply to goal
///
/// The `peel` tactic helps prove goals of the form `forall x, P x -> Q x` given
/// a hypothesis `forall x, P x`. It "peels" matching quantifiers.
///
/// # Example
/// ```text
/// -- h : forall n, 0 <= n
/// -- Goal: forall n, 0 <= n -> n >= 0
/// peel h
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a universally quantified hypothesis in the current goal
/// ENSURES: On Ok, `min(hyp_foralls, goal_foralls)` intro steps have been applied
/// ENSURES: On Err(InvalidTarget), the named hypothesis has zero leading forall quantifiers
/// ENSURES: On Err(HypothesisNotFound), no hypothesis with `hyp_name` exists
pub fn peel(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;

    // Find the hypothesis
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

    let hyp_type = hyp.ty.clone();
    let target = goal.target.clone();

    // Count foralls in hypothesis and goal
    let hyp_foralls = count_foralls(&hyp_type);
    let goal_foralls = count_foralls(&target);

    if hyp_foralls == 0 {
        return Err(TacticError::InvalidTarget {
            tactic: "peel".into(),
            detail: "hypothesis is not universally quantified".into(),
        });
    }

    // Intro the same number of foralls as the hypothesis has
    let to_intro = hyp_foralls.min(goal_foralls);

    for i in 0..to_intro {
        let name = format!("x{i}");
        intro(state, &name)?;
    }

    Ok(())
}

/// Count forall quantifiers at the head of an expression
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns the number of leading `Pi` (forall) binders before a non-Pi node
pub(crate) fn count_foralls(expr: &Expr) -> usize {
    stack_safe(|| match expr.kind() {
        ExprKind::Pi(_, _, body) => 1 + count_foralls(body),
        _ => 0,
    })
}
