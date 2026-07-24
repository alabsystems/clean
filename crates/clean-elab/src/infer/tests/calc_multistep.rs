// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for multi-step `calc` blocks.
//!
//! These exercise the full pipeline — parse a theorem, run the `by calc …`
//! tactic, compose the steps via transitivity, and kernel-check the composed
//! proof through `add_decl` — for the multi-step gap that single-step calc did
//! not cover. A successful `Ok(ElabResult)` therefore means the composed proof
//! was accepted by the trusted kernel, not merely elaborated.
//!
//! Covers:
//! - The reported gap: `calc a ≤ b := h1` / `_ ≤ c := h2` proving `a ≤ c`,
//!   including the canonical layout where the `_` step sits to the LEFT of the
//!   first step's column (Lean's separate `withPosition` for the step list).
//! - 3-step LE chains.
//! - Pure-Eq chains via `Eq.trans`.
//! - Single-step calc (unchanged).
//! - Broken chains (middle-term mismatch) — must ERROR, never silently accept.

use super::*;

/// The reported gap: a two-step `≤` chain whose second step opens with `_` that
/// sits to the LEFT of the first step's column. Both the parser (step-column
/// re-base) and the elaborator (`_` threading + `Nat.le_trans` composition) must
/// cooperate for the kernel to accept `a ≤ c`.
#[test]
fn test_calc_multistep_le_chain_proves_le() {
    let src = "theorem t (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by calc a ≤ b := h1\n    _ ≤ c := h2";
    elab_decl_with_prelude(src).expect("two-step ≤ calc chain should kernel-check");
}

/// Same chain, but with `calc` on its own line and the `_` step indented under
/// the first step. Exercises the common real-world layout.
#[test]
fn test_calc_multistep_le_chain_own_line_layout() {
    let src = "theorem t (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by\n  calc a ≤ b := h1\n    _ ≤ c := h2";
    elab_decl_with_prelude(src).expect("own-line layout ≤ calc chain should kernel-check");
}

/// A three-step `≤` chain `a ≤ b ≤ c ≤ d` proving `a ≤ d`.
#[test]
fn test_calc_multistep_three_step_le_chain_proves_le() {
    let src = "theorem t (a b c d : Nat) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by calc a ≤ b := h1\n    _ ≤ c := h2\n    _ ≤ d := h3";
    elab_decl_with_prelude(src).expect("three-step ≤ calc chain should kernel-check");
}

/// A two-step equality chain `a = b = c` proving `a = c` via `Eq.trans`.
#[test]
fn test_calc_multistep_eq_chain_proves_eq() {
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by calc a = b := h1\n    _ = c := h2";
    elab_decl_with_prelude(src).expect("two-step = calc chain should kernel-check");
}

/// Single-step calc still works (no transitivity composition).
#[test]
fn test_calc_singlestep_le_still_works() {
    let src = "theorem t (a b : Nat) (h : a ≤ b) : a ≤ b := by calc a ≤ b := h";
    elab_decl_with_prelude(src).expect("single-step ≤ calc should kernel-check");
}

/// A broken `≤` chain whose middle term does not connect: the second step's
/// implicit LHS is the first step's RHS `b`, but its proof `h3 : c ≤ d` claims
/// `c` on the left. This must ERROR — composing it would be unsound.
#[test]
fn test_calc_multistep_broken_le_chain_errors() {
    let src = "theorem t (a b c d : Nat) (h1 : a ≤ b) (h3 : c ≤ d) : a ≤ d := by calc a ≤ b := h1\n    _ ≤ d := h3";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "broken calc chain (middle mismatch b vs c) must error, got {result:?}"
    );
}

/// A broken equality chain (middle-term mismatch) must likewise ERROR.
#[test]
fn test_calc_multistep_broken_eq_chain_errors() {
    let src = "theorem t (a b c d : Nat) (h1 : a = b) (h3 : c = d) : a = d := by calc a = b := h1\n    _ = d := h3";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "broken eq calc chain (middle mismatch b vs c) must error, got {result:?}"
    );
}

/// A calc chain that proves a different relation than the goal (`a ≤ c` for a
/// goal of `a ≤ d`) must ERROR at the final goal check — no over-acceptance.
#[test]
fn test_calc_multistep_wrong_goal_errors() {
    let src = "theorem t (a b c d : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ d := by calc a ≤ b := h1\n    _ ≤ c := h2";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "calc proving a ≤ c for goal a ≤ d must error, got {result:?}"
    );
}

// --- `by`-block step justifications ---------------------------------------
//
// A calc step may justify its relation with a `by tac_seq` block instead of a
// term. Each step's `by`-block goal must be THAT step's relation (`b = c`), not
// the enclosing `by calc …` goal (`a = c`). Regression for the bug where the
// step's `by`-block inherited the stale outer calc target and reported a bogus
// `fvar mismatch` when composing the transitivity chain. The composed proof is
// kernel-checked through `add_decl`, so `Ok` means the trusted kernel accepted
// the assembled `Eq.trans` term.

/// Tooth 1: a two-step `=` chain whose BOTH steps use `by exact` justifications.
#[test]
fn test_calc_multistep_by_exact_two_steps_proves_eq() {
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := by exact h1\n    _ = c := by exact h2";
    elab_decl_with_prelude(src).expect("two-step = calc with by-exact steps should kernel-check");
}

/// Tooth 2: a three-step `=` chain with `by exact` justifications on every step.
#[test]
fn test_calc_multistep_by_exact_three_steps_proves_eq() {
    let src = "theorem t (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by\n  calc a = b := by exact h1\n    _ = c := by exact h2\n    _ = d := by exact h3";
    elab_decl_with_prelude(src).expect("three-step = calc with by-exact steps should kernel-check");
}

/// Mixed justifications: a term-mode first step and a `by`-mode second step in
/// the same calc block. Exercises the transition where the outer expected type
/// must be restored after the `by`-block so the term step composes correctly.
#[test]
fn test_calc_multistep_mixed_term_and_by_steps_proves_eq() {
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := h1\n    _ = c := by exact h2";
    elab_decl_with_prelude(src).expect("mixed term/by calc chain should kernel-check");
}

/// Negative: a step's `by`-block cannot close its goal — the first step's goal
/// is `a = b`, but `by exact h2` supplies `h2 : b = c`. This MUST error (the
/// tactic fails to close the goal), never panic and never over-accept.
#[test]
fn test_calc_multistep_by_step_cannot_close_errors() {
    let src = "theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by\n  calc a = b := by exact h2\n    _ = c := by exact h2";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "calc step whose by-block cannot close its goal must error, got {result:?}"
    );
}
