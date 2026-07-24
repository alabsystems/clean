// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regressions for the `by_cases h : p` tactic through the full
//! `parse → elab_decl → elab_by_tactic → eval_tactic → by_cases → closed_proof`
//! path.
//!
//! These guard two bugs that made `by_cases h : p` fail in the surface path:
//!
//! 1. **Dispatch.** `by_cases` uses the `ExprList` arg pattern, so the
//!    dispatcher (`eval_tactic`) elaborated *every* arg as a term — including
//!    the new hypothesis name `h`. Because `h` is not yet in scope it was bound
//!    as a fresh auto-implicit FVar absent from the goal's local context, and
//!    the handler's `expr_to_hyp_name` then raised
//!    `HypothesisNotFound`. Fixed by treating the binder-name slot as a bare
//!    `Const` (no elaboration), exactly like the ident-list pass-through.
//!
//! 2. **Proof-term closing.** The two branches are parallel `λ h => …` lambdas
//!    under `Or.rec`, both at the same binder depth. The original code gave them
//!    two distinct FVar ids; `close_fvars` (which assumes FVar ids grow with
//!    binder *nesting* depth) then could not close the second, tripping the
//!    `close_fvars` debug-assert. Fixed by sharing one FVar id across the two
//!    disjoint branch scopes.
//!
//! The positive cases mirror Lean 4 (cross-checked: `lean` accepts t1/t2/t3,
//! rejects the wrong-hypothesis branch). The negative case must ERROR, never
//! panic.

use super::*;

/// Classical excluded middle on a `Prop` parameter, closing each branch with the
/// matching disjunct. The theorem has binders (`p : Prop`) so the proof state
/// runs with `fvar_base > 0`, which is exactly what tripped the `close_fvars`
/// debug-assert before the shared-FVar fix.
#[test]
fn test_by_cases_em_split_closes_both_branches() {
    let result = elab_decl_with_prelude(
        "theorem t (p : Prop) : p ∨ ¬p := by\n  by_cases h : p\n  · exact Or.inl h\n  · exact Or.inr h",
    );
    assert!(
        result.is_ok(),
        "by_cases h : p should split via Classical.em and close both branches \
         (h : p / h : ¬p) through the full surface path, got: {:?}",
        result.err()
    );
}

/// A goal whose branches USE the introduced hypothesis: the positive branch
/// applies `hpq : p → q` to `h : p`, the negative branch returns `h : ¬p`.
/// Confirms `h` is actually in scope and correctly typed inside each branch.
#[test]
fn test_by_cases_branches_use_hypothesis() {
    let result = elab_decl_with_prelude(
        "theorem t (p q : Prop) (hpq : p → q) : ¬p ∨ q := by\n  by_cases h : p\n  · exact Or.inr (hpq h)\n  · exact Or.inl h",
    );
    assert!(
        result.is_ok(),
        "by_cases branches should expose h : p (positive) and h : ¬p (negative) \
         and close the goal using them, got: {:?}",
        result.err()
    );
}

/// Negative: the second branch is closed with the WRONG disjunct
/// (`Or.inl h` where `h : ¬p` but the left disjunct needs `p`). This must be
/// REJECTED (the assembled term is kernel-rechecked) and must NOT panic.
#[test]
fn test_by_cases_wrong_hypothesis_branch_errors_no_panic() {
    let result = elab_decl_with_prelude(
        "theorem t (p : Prop) : p ∨ ¬p := by\n  by_cases h : p\n  · exact Or.inl h\n  · exact Or.inl h",
    );
    assert!(
        result.is_err(),
        "a branch closed with the wrong-typed hypothesis (h : ¬p where p is \
         required) must error rather than over-accept",
    );
}
