// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end proof-chain regression for `aesop` through `elab_by_tactic`.
//!
//! Exercises the full path:
//!   parse → elab_decl → elab_by_tactic → eval_tactic(aesop) →
//!   aesop_search_tree → merge_meta_assignments (#2533) →
//!   closed_proof → verify_tactic_proof
//!
//! The #2533 fix has two parts:
//! 1. merge_from: copies meta assignments from the proven clone to main state
//! 2. next_fvar bump: ensures closed_proof() covers clone-allocated FVars
//!
//! Without (2), aesop succeeds but verify_tactic_proof fails with UnknownFVar
//! because tactic-created FVars (from intro) in the clone aren't covered by
//! the main state's [fvar_base, next_fvar) range.
//!
//! Part of #2533, Part of #2442.

use super::*;

/// Implication identity: `theorem t (A : Prop) : A → A := by aesop`
///
/// Aesop's safe rules apply intro (allocating a new FVar in the clone),
/// then assumption closes the goal. The proof term is a lambda referencing
/// the clone-allocated FVar. Without the next_fvar merge, closed_proof()
/// won't close this FVar and verify_tactic_proof fails with UnknownFVar.
#[test]
fn test_elab_by_tactic_aesop_intro_assumption() {
    let result = elab_decl("theorem t (A : Prop) : A → A := by aesop");
    assert!(
        result.is_ok(),
        "aesop should close A → A via intro + assumption through elab_by_tactic — \
         clone-allocated FVars must be covered by next_fvar merge (#2533), got: {:?}",
        result.err()
    );
}

/// Double implication: `theorem t (A B : Prop) : A → B → A := by aesop`
///
/// Exercises multiple intro steps in the clone. The clone allocates two
/// FVars (for A and B hypotheses), and the proof term references the first.
/// This tests that next_fvar is bumped past all clone allocations.
#[test]
fn test_elab_by_tactic_aesop_double_intro() {
    let result = elab_decl("theorem t (A B : Prop) : A → B → A := by aesop");
    assert!(
        result.is_ok(),
        "aesop should close A → B → A via double intro + assumption through elab_by_tactic — \
         multiple clone-allocated FVars must be covered (#2533), got: {:?}",
        result.err()
    );
}

/// Nested implication: `theorem t (A B : Prop) : (A → B) → A → B := by aesop`
///
/// Exercises intro of a function-typed hypothesis. Aesop intros both
/// (A → B) and A, then applies the function hypothesis. The proof term
/// involves application of a clone-allocated FVar to another clone-allocated
/// FVar, testing deeper proof term assembly through the merge.
#[test]
fn test_elab_by_tactic_aesop_nested_implication() {
    let result = elab_decl("theorem t (A B : Prop) : (A → B) → A → B := by aesop");
    assert!(
        result.is_ok(),
        "aesop should close (A → B) → A → B through elab_by_tactic — \
         function application with clone FVars must survive merge (#2533), got: {:?}",
        result.err()
    );
}
