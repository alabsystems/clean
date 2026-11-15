// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Annotated elimination targets and the case goals they produce:
//!
//! - `generalize h : e = x at h₁ ⊢` and `at *`;
//! - tactic `match` arms that bind pattern variables, with and without an
//!   annotated discriminant `match h : e with`;
//! - a field-less `cases`/`induction` case whose first `intro` used to take
//!   the eliminated variable's own binder id (an ill-typed proof term);
//! - `cases … with` alternatives with a goal BEHIND the eliminated one.

use crate::common::*;

// --- a field-less case's first `intro` -----------------------------------

#[test]
fn test_cases_fieldless_case_intro_gets_its_own_binder() {
    // `x` is eliminated, but the `none` case's proof is still under `fun x`:
    // `h` must not reuse `x`'s binder (kernel: "expected f n = none, got
    // Option Nat").
    let src = format!(
        "{OPT_FN}theorem intro_cases (n : Nat) (hn : f n ≠ none) : ∀ x, f n = x → ∃ y, x = some y := by\n  \
         intro x\n  cases x\n  · intro h; exact absurd h hn\n  · intro _; exact ⟨_, rfl⟩\n\n\
         theorem intro_cases_alts (n : Nat) (hn : f n ≠ none) : ∀ x, f n = x → ∃ y, x = some y := by\n  \
         intro x\n  cases x with\n  | none => intro h; exact absurd h hn\n  | some y => intro _; exact ⟨y, rfl⟩\n"
    );
    expect_axiom_free(
        &src,
        "an `intro` in a field-less case",
        &["intro_cases", "intro_cases_alts"],
    );
}

#[test]
fn test_cases_fieldless_case_goal_is_the_constructor_instance() {
    // Lean 4.8: the `none` goal is `∃ y, none = some y`; `⟨0, rfl⟩` fails.
    let src = format!(
        "{OPT_FN}theorem intro_cases_twin (n : Nat) (hn : f n ≠ none) : ∀ x, f n = x → ∃ y, x = some y := by\n  \
         intro x\n  cases x\n  · intro h; exact ⟨0, rfl⟩\n  · intro _; exact ⟨_, rfl⟩\n"
    );
    expect_refused_at(
        &src,
        "a `none`-case goal closed as a `some` one",
        "intro_cases_twin",
        MISMATCH,
    );
}

// --- `cases … with` and the goals behind it ------------------------------

#[test]
fn test_cases_alternatives_leave_the_goal_behind_alone() {
    let src = "theorem cases_behind (p q : Prop) (h : p ∨ q) (hq : q) : (q ∨ p) ∧ q := by\n  \
               constructor\n  cases h with\n  | inl hp => exact Or.inr hp\n  \
               | inr hq' => exact Or.inl hq'\n  exact hq\n";
    expect_axiom_free(
        src,
        "`cases … with` before a second goal",
        &["cases_behind"],
    );
}

#[test]
fn test_cases_alternatives_goal_behind_keeps_its_own_target() {
    // Lean 4.8: the goal behind is `q`; `h : p ∨ q` does not close it.
    let src = "theorem cases_behind_twin (p q : Prop) (h : p ∨ q) (hq : q) : (q ∨ p) ∧ q := by\n  \
               constructor\n  cases h with\n  | inl hp => exact Or.inr hp\n  \
               | inr hq' => exact Or.inl hq'\n  exact h\n";
    expect_refused_at(
        src,
        "the goal behind closed by the wrong term",
        "cases_behind_twin",
        MISMATCH,
    );
}

// --- `generalize … at` ---------------------------------------------------

#[test]
fn test_generalize_at_hypothesis_rewrites_it() {
    let src = "theorem gen_at (w : Nat) (i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w ∨ False := by\n  \
               generalize hm : 2 ^ w = m at hlt ⊢\n  exact Or.inl hlt\n\n\
               theorem gen_at_hyp (w : Nat) (i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w ∨ False := by\n  \
               generalize 2 ^ w = m at hlt\n  exact Or.inl hlt\n";
    expect_axiom_free(src, "`generalize … at hlt`", &["gen_at", "gen_at_hyp"]);
}

#[test]
fn test_generalize_without_location_leaves_the_hypothesis() {
    // Lean 4.8: without `at hlt`, `hlt : i < 2 ^ w` does not prove `i < m`.
    let src =
        "theorem gen_at_twin (w : Nat) (i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w ∨ False := by\n  \
               generalize hm : 2 ^ w = m\n  exact Or.inl hlt\n";
    expect_refused_at(
        src,
        "a hypothesis generalize did not touch",
        "gen_at_twin",
        MISMATCH,
    );
}

#[test]
fn test_generalize_at_unknown_hypothesis_is_refused() {
    // Lean 4.8: "unknown identifier 'hnope'".
    let src =
        "theorem gen_at_missing (w : Nat) (i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w ∨ False := by\n  \
               generalize hm : 2 ^ w = m at hnope\n  exact Or.inl hlt\n";
    let err = expect_refused_at(src, "`at` naming no hypothesis", "gen_at_missing", &[]);
    assert!(err.contains("hnope"), "the refusal must name it: {err}");
}

#[test]
fn test_generalize_at_wildcard_rewrites_every_hypothesis() {
    // Lean 4.8 (`generalize e = x at *`): every hypothesis and the goal.
    let src = "theorem gen_all (w i : Nat) (hlt : i < 2 ^ w) (hle : i ≤ 2 ^ w) : \
               i < 2 ^ w ∧ i ≤ 2 ^ w := by\n  generalize hm : 2 ^ w = m at *\n  exact ⟨hlt, hle⟩\n";
    expect_axiom_free(src, "`generalize … at *`", &["gen_all"]);
}

#[test]
fn test_generalize_at_wildcard_leaves_no_occurrence_behind() {
    // Lean 4.8: "application type mismatch … hlt has type i < m but is
    // expected to have type i < 2 ^ w" — after `at *` no hypothesis still
    // mentions `2 ^ w`.
    let src = "theorem gen_all_twin (w i : Nat) (hlt : i < 2 ^ w) (hle : i ≤ 2 ^ w) : \
               i < 2 ^ w ∧ i ≤ 2 ^ w := by\n  generalize hm : 2 ^ w = m at *\n  \
               exact (⟨hlt, hle⟩ : i < 2 ^ w ∧ i ≤ 2 ^ w)\n";
    expect_refused_at(
        src,
        "a hypothesis `at *` did not touch",
        "gen_all_twin",
        MISMATCH,
    );
}

#[test]
fn test_generalize_at_one_hypothesis_leaves_the_others() {
    // Lean 4.8: "application type mismatch … hle has type i ≤ 2 ^ w but is
    // expected to have type i ≤ m" — `at hlt` generalizes `hlt` and the goal.
    let src = "theorem gen_one_twin (w i : Nat) (hlt : i < 2 ^ w) (hle : i ≤ 2 ^ w) : \
               i < 2 ^ w ∧ i ≤ 2 ^ w := by\n  generalize hm : 2 ^ w = m at hlt\n  \
               exact ⟨hlt, hle⟩\n";
    expect_refused_at(src, "`at hlt` read as `at *`", "gen_one_twin", MISMATCH);
}

// --- tactic `match` with pattern variables -------------------------------

#[test]
fn test_tactic_match_arm_goal_names_its_pattern_variables() {
    let src = "theorem match_plain (x : Option Nat) : x = none ∨ ∃ y, x = some y := by\n  \
               match x with\n  | none => exact Or.inl rfl\n  | some y => exact Or.inr ⟨y, rfl⟩\n";
    expect_axiom_free(src, "a tactic `match` arm binding `y`", &["match_plain"]);
}

#[test]
fn test_tactic_match_every_binding_arm_gets_its_own_binders() {
    // Two arms that BOTH bind: each arm's lambda is its own chain, so the
    // second arm's `v` sits at depth 0 exactly like the first arm's `e`.
    let src = "theorem match_two (x : Except String Nat) : (∃ e, x = .error e) ∨ ∃ v, x = .ok v := by\n  \
               match x with\n  | .error e => exact Or.inl ⟨e, rfl⟩\n  | .ok v => exact Or.inr ⟨v, rfl⟩\n\n\
               theorem match_two_h (f : Nat → Except String Nat) (n : Nat) (hn : ∀ e, f n ≠ .error e) : \
               ∃ v, f n = .ok v := by\n  match h : f n with\n  | .error e => exact absurd h (hn e)\n  \
               | .ok v => exact ⟨v, rfl⟩\n";
    expect_axiom_free(
        src,
        "a tactic `match` whose two arms both bind",
        &["match_two", "match_two_h"],
    );
}

/// A SHALLOWER arm that mints a hypothesis (`rw … at hk` replaces `hk`)
/// before a binding arm runs: each arm allocates from its own binder base.
/// Pinned Lean 4.8.0 accepts `match_rw_at` and refuses the twin
/// ("application type mismatch … hk has type P 0 … expected P 1").
const MATCH_RW_AT: &str = "(P : Nat → Prop) (x : Option Nat) (k : Nat) (e : k = 0) (hk : P k) : ";
const MATCH_RW_AT_ARMS: &str =
    " ∨ True := by\n  match x with\n  | none => rw [e] at hk; exact Or.inl hk\n  \
                                | some y => exact Or.inr True.intro\n";

#[test]
fn test_tactic_match_arm_minting_a_local_before_a_binding_arm() {
    let src = format!("theorem match_rw_at {MATCH_RW_AT}P 0{MATCH_RW_AT_ARMS}");
    expect_axiom_free(
        &src,
        "`rw … at` in an arm before a binding arm",
        &["match_rw_at"],
    );
    let src = format!("theorem match_rw_at_twin {MATCH_RW_AT}P 1{MATCH_RW_AT_ARMS}");
    expect_refused_at(
        &src,
        "the rewritten `hk` closing `P 1`",
        "match_rw_at_twin",
        MISMATCH,
    );
}

#[test]
fn test_tactic_match_second_binding_arm_is_its_own_instance() {
    // Lean 4.8: in the `.error e` arm `x` is `.error e`; `⟨0, rfl⟩` claims `.ok 0`.
    let src = "theorem match_two_twin (x : Except String Nat) : (∃ e, x = .error e) ∨ ∃ v, x = .ok v := by\n  \
               match x with\n  | .error e => exact Or.inr ⟨0, rfl⟩\n  | .ok v => exact Or.inr ⟨v, rfl⟩\n";
    expect_refused_at(
        src,
        "the `.error` arm closed as an `.ok` one",
        "match_two_twin",
        MISMATCH,
    );
    // Lean 4.8: in the `.ok v` arm `h : f n = .ok v`, never `.error _`.
    let src = "theorem match_two_h_twin (f : Nat → Except String Nat) (n : Nat) (hn : ∀ e, f n ≠ .error e) : \
               ∃ v, f n = .ok v := by\n  match h : f n with\n  | .error e => exact absurd h (hn e)\n  \
               | .ok v => exact absurd h (hn \"\")\n";
    expect_refused_at(
        src,
        "an `.ok`-arm equation used as an `.error` one",
        "match_two_h_twin",
        MISMATCH,
    );
}

#[test]
fn test_tactic_match_arm_goal_is_the_pattern_instance() {
    // Lean 4.8: the `some y` goal is `some y = none ∨ …`; `Or.inl rfl` fails.
    let src = "theorem match_plain_twin (x : Option Nat) : x = none ∨ ∃ y, x = some y := by\n  \
               match x with\n  | none => exact Or.inl rfl\n  | some y => exact Or.inl rfl\n";
    expect_refused_at(
        src,
        "the `some` arm closed as the `none` one",
        "match_plain_twin",
        MISMATCH,
    );
}
