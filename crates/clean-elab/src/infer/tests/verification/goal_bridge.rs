// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Regression test for #1165 / #2440: induction alternatives must route by
/// constructor tag, not by source order, and renamed IH binders must be visible
/// to recursive tactic elaboration.
#[test]
fn test_elab_by_tactic_induction_alts_match_by_tag_and_rename_ih() {
    let result = elab_decl_with_nat_env(
        "theorem t : Nat → Nat := by intro n; induction n with | succ m ih => exact ih | zero => exact Nat.zero",
    );
    assert!(
        result.is_ok(),
        "induction with reversed alternatives should still route by constructor tag, \
         and renamed succ/IH binders must be visible to `exact ih`, got: {:?}",
        result.err()
    );
}

/// Regression test for #1165 / #2440: cases alternatives share the same
/// `eval_induction_alts` routing path and must expose renamed field binders to
/// recursive elaboration even when the alts are out of source-order.
#[test]
fn test_elab_by_tactic_cases_alts_match_by_tag_and_rename_field() {
    let result = elab_decl_with_nat_env(
        "theorem t : Nat → Nat := by intro n; cases n with | succ k => exact k | zero => exact Nat.zero",
    );
    assert!(
        result.is_ok(),
        "cases with reversed alternatives should still route by constructor tag, \
         and renamed field binders must be visible to `exact k`, got: {:?}",
        result.err()
    );
}

/// Regression test for #2184: parser-driven `refine _` must create a subgoal
/// with the same target type, and the final proof must be closed.
///
/// Uses `_` for holes — clean parser does not support Lean 4's `?_` syntax.
#[test]
fn test_elab_by_tactic_refine_single_hole() {
    let result = elab_decl("theorem t (A : Prop) (a : A) : A := by refine _; exact a")
        .expect("refine _ then exact should elaborate successfully");

    let ElabResult::Theorem { proof, .. } = result else {
        panic!("expected theorem elaboration result");
    };

    assert!(
        !proof.has_fvar_quick(),
        "refine theorem proof should be closed, got: {proof:?}"
    );
}

/// Regression test for #2184: parser-driven `refine` with function application
/// must remap elaborator holes into tactic goals with accurate types.
#[test]
fn test_elab_by_tactic_refine_app_with_holes() {
    let result = elab_decl(
        "theorem t (P Q R : Prop) (f : P -> Q -> R) (p : P) (q : Q) : R := by \
         refine f _ _; exact p; exact q",
    );

    match &result {
        Ok(ElabResult::Theorem { proof, .. }) => {
            assert!(
                !proof.has_fvar_quick(),
                "refine app proof should be closed, got: {proof:?}"
            );
        }
        Ok(other) => panic!("expected Theorem, got: {other:?}"),
        Err(e) => panic!("refine app theorem should elaborate, got: {e:?}"),
    }
}

/// Regression test for #2184: parser-driven `refine` must remap dependent hole
/// types in left-to-right order, so later goals can mention earlier holes.
#[test]
fn test_elab_by_tactic_refine_dependent_app_with_holes() {
    let result = elab_decl(
        "theorem t (A : Type) (B : A -> Prop) (C : Prop) \
         (f : (x : A) -> B x -> C) (a : A) (b : B a) : C := by \
         refine f _ _; exact a; exact b",
    );

    match &result {
        Ok(ElabResult::Theorem { proof, .. }) => {
            assert!(
                !proof.has_fvar_quick(),
                "refine dependent app proof should be closed, got: {proof:?}"
            );
        }
        Ok(other) => panic!("expected Theorem, got: {other:?}"),
        Err(e) => panic!("refine dependent app theorem should elaborate, got: {e:?}"),
    }
}

/// Regression test for #1848: tactic `match` must route branch tactics using
/// the elaborated constructor order, not the source order of the arms.
#[test]
fn test_elab_by_tactic_match_routes_wildcard_before_later_ctor_arm() {
    let result = elab_decl_with_prelude_env(
        "theorem t : Nat -> Nat := by \
         intro n; \
         match n with \
         | Nat.succ k => exact k \
         | _ => exact Nat.zero",
    );

    match &result {
        Ok(ElabResult::Theorem { proof, .. }) => {
            assert!(
                !proof.has_fvar_quick(),
                "tactic match proof should be closed, got: {proof:?}"
            );
        }
        Ok(other) => panic!("expected Theorem, got: {other:?}"),
        Err(e) => panic!("tactic match theorem should elaborate, got: {e:?}"),
    }
}

/// Regression test for #1848: multi-discriminant tactic `match` must lower the
/// scrutinee tuple and expose branch-local binders from the selected pattern.
#[test]
fn test_elab_by_tactic_match_multi_discriminant_tuple_pattern() {
    let result = elab_decl_with_prelude_env(
        "theorem t : Nat -> Nat -> Nat := by \
         intro a; intro b; \
         match a, b with \
         | (Nat.zero, k) => exact k \
         | (Nat.succ n, _) => exact n",
    );

    match &result {
        Ok(ElabResult::Theorem { proof, .. }) => {
            assert!(
                !proof.has_fvar_quick(),
                "multi-discriminant tactic match proof should be closed, got: {proof:?}"
            );
        }
        Ok(other) => panic!("expected Theorem, got: {other:?}"),
        Err(e) => panic!("multi-discriminant tactic match theorem should elaborate, got: {e:?}"),
    }
}
