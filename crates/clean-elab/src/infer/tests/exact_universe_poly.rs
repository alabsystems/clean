// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `exact <universe-polymorphic term>`.
//!
//! `exact e` must elaborate its term argument AGAINST the current goal target
//! as the expected type, so that a fully-implicit, universe-polymorphic term —
//! `@rfl.{u} {α : Sort u} {a : α} : a = a`, or `Eq.refl n` whose `Sort`
//! universe `?u` is otherwise abstract — has its implicit arguments AND its
//! universe levels solved by unifying the term's type with the goal. Without
//! this, those metavariables/levels stay unsolved and the assembled term fails
//! the def-eq check against the goal (e.g. `n = n`).
//!
//! A successful `Ok(ElabResult)` means the proof term was accepted by the
//! trusted kernel via `add_decl`, not merely elaborated.
//!
//! Covers:
//! - `exact rfl` on a `Prop` equality goal (`n = n`, `(5 : Nat) = 5`).
//! - `exact rfl` / `exact Eq.refl x` on a `Type`-universe equality goal.
//! - `exact Eq.refl n` (explicit value arg, abstract universe).
//! - A plain non-polymorphic `exact` still works (`exact h hp`).
//! - A universe-polymorphic `exact` in a NON-equality goal (`Or.inl` / `Or.inr`).
//! - NEGATIVE: a term whose type genuinely does not match the goal still
//!   ERRORS (no over-accept), never panics.

use super::*;

// ── Positives: the reported bug ────────────────────────────────────────────

/// `exact rfl` closing `n = n`. The fully-implicit `rfl` has its `?α`/`?a` and
/// universe `?u` solved from the goal `n = n`.
#[test]
fn test_exact_rfl_closes_eq_goal() {
    let src = "theorem t (n : Nat) : n = n := by exact rfl";
    elab_decl_with_prelude(src).expect("exact rfl should close n = n");
}

/// `exact rfl` closing a literal equality `(5 : Nat) = 5`.
#[test]
fn test_exact_rfl_closes_literal_eq_goal() {
    let src = "theorem t : (5 : Nat) = 5 := by exact rfl";
    elab_decl_with_prelude(src).expect("exact rfl should close (5 : Nat) = 5");
}

/// `exact Eq.refl n`: the value argument `n` is supplied, but the `Sort`
/// universe of `α` is still abstract and must be solved from the goal.
#[test]
fn test_exact_eq_refl_with_value_arg_closes_eq_goal() {
    let src = "theorem t (n : Nat) : n = n := by exact Eq.refl n";
    elab_decl_with_prelude(src).expect("exact Eq.refl n should close n = n");
}

/// `exact rfl` on a `Type`-universe equality (`x : a`, `a : Type`), exercising
/// the level solving above `Prop`.
#[test]
fn test_exact_rfl_closes_type_universe_eq_goal() {
    let src = "theorem t (a : Type) (x : a) : x = x := by exact rfl";
    elab_decl_with_prelude(src).expect("exact rfl should close x = x at Type level");
}

/// `exact Eq.refl x` on a `Type`-universe equality.
#[test]
fn test_exact_eq_refl_closes_type_universe_eq_goal() {
    let src = "theorem t (a : Type) (x : a) : x = x := by exact Eq.refl x";
    elab_decl_with_prelude(src).expect("exact Eq.refl x should close x = x at Type level");
}

// ── Positives: don't break plain / non-eq exact ────────────────────────────

/// Plain, non-polymorphic `exact` (a function application of hypotheses) must
/// keep working.
#[test]
fn test_exact_plain_application_still_works() {
    let src = "theorem t (p q : Prop) (h : p → q) (hp : p) : q := by exact h hp";
    elab_decl_with_prelude(src).expect("exact h hp should still close q");
}

/// Universe-polymorphic `exact` in a NON-equality goal: `Or.inl hp : p ∨ q`.
#[test]
fn test_exact_or_inl_in_disjunction_goal() {
    let src = "theorem t (p q : Prop) (hp : p) : p ∨ q := by exact Or.inl hp";
    elab_decl_with_prelude(src).expect("exact Or.inl hp should close p ∨ q");
}

/// Universe-polymorphic `exact` in a NON-equality goal: `Or.inr hq : p ∨ q`.
#[test]
fn test_exact_or_inr_in_disjunction_goal() {
    let src = "theorem t (p q : Prop) (hq : q) : p ∨ q := by exact Or.inr hq";
    elab_decl_with_prelude(src).expect("exact Or.inr hq should close p ∨ q");
}

// ── Negatives: must still ERROR (no over-accept, no panic) ──────────────────

/// A hypothesis of the WRONG type passed to `exact` must error, not be
/// silently accepted by the expected-type-driven elaboration.
#[test]
fn test_exact_wrong_type_hypothesis_errors() {
    let src = "theorem t (n : Nat) (h : n = n + 1) : n = n := by exact h";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "exact h with h : n = n + 1 against goal n = n must error, got {result:?}"
    );
}

/// `exact rfl` on a NON-reflexive equality goal (`a = b` with `a` ≠ `b`
/// syntactically) must error: reflexivity does not prove `a = b`.
#[test]
fn test_exact_rfl_on_non_reflexive_goal_errors() {
    let src = "theorem t (a b : Nat) (h : a = b) : a = b := by exact rfl";
    let result = elab_decl_with_prelude(src);
    assert!(
        result.is_err(),
        "exact rfl against goal a = b (a ≠ b) must error, got {result:?}"
    );
}
