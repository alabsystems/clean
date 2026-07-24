// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the `suffices` tactic (`suffices h : T by tac` /
//! `suffices h : T from e`).
//!
//! `suffices h : P by tac` introduces `h : P` into the context, runs `tac` to
//! close the CURRENT main goal using `h`, and leaves the obligation `⊢ P` as
//! the new goal (proved by the subsequent tactics). This is `have h : P :=
//! ?proofOfP` with the obligation order swapped — the faithful desugaring of
//! Lean 4's `expandSuffices` macro (`have h : T := body; by tac`).
//!
//! A successful `Ok(ElabResult)` means the composed proof — both the
//! main-goal closure (using `h`) AND the residual `P` proof — was accepted by
//! the trusted kernel via `add_decl`, not merely elaborated.
//!
//! Covers:
//! - The reported gap: `suffices h2 : p by exact h2` then `exact h` proving `p`.
//! - Using `h2` to close the main goal (`a = b ⇒ b = a` via `h2.symm`).
//! - The `from` justification form.
//! - NEGATIVE: residual `P` goal left unsolved → ERROR (never silently accept).
//! - NEGATIVE: a `by` block that cannot close the main goal → ERROR, no panic.
//! - NEGATIVE: wrong/ill-typed justification → ERROR, no panic.
//!
//! Layout note: the canonical Lean-valid layout puts `by` on its own line so
//! the `suffices` and the trailing tactic align in the same `by` block. The
//! `:= by suffices … <newline> <low-indent tac>` inline layout is rejected by
//! real Lean 4 (the dedented continuation is not part of the block); Clean
//! matches that behaviour, so these tests use the canonical layout.

use super::*;

/// The reported gap. `suffices h2 : p by exact h2` closes `⊢ p` using `h2`,
/// leaving the obligation `⊢ p`, which `exact h` discharges.
#[test]
fn test_suffices_by_closes_main_and_leaves_residual() {
    let src = "theorem t (p : Prop) (h : p) : p := by\n  suffices h2 : p by exact h2\n  exact h";
    elab_decl_with_prelude(src).expect("suffices closing main with h2, residual proved by h");
}

/// The `by` block uses `h2` non-trivially to close the main goal: from
/// `h2 : a = b` it proves `b = a` via `h2.symm`, leaving `⊢ a = b` for `h`.
#[test]
fn test_suffices_by_uses_hyp_to_close_main() {
    let src = "theorem t (a b : Nat) (h : a = b) : b = a := by\n  suffices h2 : a = b by exact h2.symm\n  exact h";
    elab_decl_with_prelude(src)
        .expect("suffices using h2.symm to close main, residual proved by h");
}

/// The `from` justification form: `suffices h2 : p from h2` closes the main
/// goal with the term `h2`, leaving `⊢ p` for `exact h`.
#[test]
fn test_suffices_from_form_closes_main_and_leaves_residual() {
    let src = "theorem t (p : Prop) (h : p) : p := by\n  suffices h2 : p from h2\n  exact h";
    elab_decl_with_prelude(src).expect("suffices `from` form should kernel-check");
}

/// NEGATIVE: with no subsequent proof of the residual `P`, the obligation
/// `⊢ p` is left unsolved. Elaboration must ERROR (unsolved goals), never
/// silently accept, and never panic.
#[test]
fn test_suffices_residual_goal_unsolved_errors() {
    let src = "theorem t (p : Prop) (h : p) : p := by\n  suffices h2 : p by exact h2";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "suffices with no proof of the residual P must error (unsolved goal), got {result:?}"
    );
}

/// NEGATIVE: the `by` block (`skip`) does not close the main goal from
/// `h2 : q`. Elaboration must ERROR and never panic.
#[test]
fn test_suffices_by_block_does_not_close_main_errors() {
    let src = "theorem t (p q : Prop) (h : p) : p := by\n  suffices h2 : q by skip\n  exact h";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "suffices whose `by` block cannot close the main goal must error, got {result:?}"
    );
}

/// NEGATIVE: `exact h2` with `h2 : q` cannot close the main goal `⊢ p` when
/// `q ≠ p`. The kernel-checked `exact` must reject the type mismatch — ERROR,
/// no panic, no over-accept.
#[test]
fn test_suffices_wrong_prop_closure_errors() {
    let src = "theorem t (p q : Prop) (h : p) : p := by\n  suffices h2 : q by exact h2\n  exact h";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "suffices closing `⊢ p` with `h2 : q` must error (type mismatch), got {result:?}"
    );
}
