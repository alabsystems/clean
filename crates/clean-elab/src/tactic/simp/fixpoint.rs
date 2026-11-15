// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simp's traversal repeated to a fixpoint, for a TYPE that is not the goal
//! (`simp at h`, `simpa … using e`).
//!
//! Lean's `Simp.main` revisits every rewritten term (`post` hands the result
//! back to `visit` until no step applies), so `simp at hc` on `hc : c ∈ [1,
//! 2, 3]` ends at `c = 1 ∨ c = 2 ∨ c = 3`. One `simp_expr` traversal does not
//! re-enter the right-hand side it just produced, and the goal entry point
//! (`simp_with_budget`) has always looped over traversals; the hypothesis
//! entry points ran ONE, so `simp at hc` stopped at `c = 1 ∨ c ∈ [2, 3]`
//! (trust-ir gap G25, ledger class (94)).
//!
//! Proofs chain exactly as the goal loop chains them (`Eq.trans`, keeping the
//! other side when a step was definitional only); whatever cast the caller
//! builds from the result is kernel-checked by `close_goal`, so a chain that
//! does not prove `ty = result` is refused there, never trusted.

use clean_kernel::Expr;

use super::budget::SimpBudget;
use super::expr::simp_expr_budgeted;
use super::proof::mk_eq_trans_expr;
use super::types::{SimpConfig, SimpLemmaSet, SimpResult};
use crate::tactic::{Goal, ProofState};

/// `config.max_steps` traversals ran and the last one still rewrote: the
/// rewriting does not terminate. Lean's simp fails here too (pinned 4.8.0 on
/// `(h1 : ∀ x, f x = f (x + 1)) (h : f 0 = 5) … simp [h1] at h`: "maximum
/// recursion depth has been reached"), so the caller refuses rather than
/// hand back whatever term the last traversal left.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct NoFixpoint {
    /// Traversals run before giving up (`config.max_steps`).
    pub(super) traversals: usize,
}

impl NoFixpoint {
    /// The refusal text, naming Lean's error for the same input.
    pub(super) fn detail(self) -> String {
        format!(
            "no fixpoint after {} traversals; the rewriting does not terminate \
             (Lean: maximum recursion depth has been reached)",
            self.traversals
        )
    }
}

/// Simplify `ty` with `lemmas` until a traversal changes nothing, at most
/// `config.max_steps` traversals. The result's `proof` (when present) proves
/// `ty = result.expr`. A tripped `budget` stops the loop; the caller reads
/// `budget.detail()` and refuses, as after a single traversal. Running out of
/// traversals without reaching a fixpoint is [`NoFixpoint`].
pub(super) fn simp_type_to_fixpoint(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Result<SimpResult, NoFixpoint> {
    let mut current = ty.clone();
    let mut proof: Option<Expr> = None;
    let mut steps = 0;
    let mut converged = false;
    while steps < config.max_steps {
        // The bound is per traversal, as in the goal loop.
        budget.refuel();
        let step = simp_expr_budgeted(state, goal, &current, lemmas, config, budget);
        if budget.detail().is_some() {
            converged = true;
            break;
        }
        if step.expr == current {
            converged = true;
            break;
        }
        proof = match (proof.take(), step.proof) {
            (None, p) => p,
            (p, None) => p,
            (Some(p1), Some(p2)) => Some(mk_eq_trans_expr(state, goal, &p1, &p2).unwrap_or(p2)),
        };
        current = step.expr;
        steps += 1;
    }
    // `max_steps == 0` runs nothing and claims nothing: that is a fixpoint of
    // the empty traversal sequence, not a runaway.
    if !converged && steps > 0 {
        return Err(NoFixpoint { traversals: steps });
    }
    Ok(SimpResult {
        expr: current,
        proof,
    })
}
