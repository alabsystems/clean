// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The equation `h` of an annotated target (`cases h : e`, tactic `match
//! h : e`) SHADOWS an older local named `h`.
//!
//! Lean 4.8 leaves the older local in the context as `h✝`, unreachable by
//! name, so every tactic that takes a hypothesis BY NAME — `rw [h] at hn`,
//! `simp only [h] at hn`, `cases h`, `subst h` — acts on the new equation.
//! Names stay on their original locals. By-name lookup selects the newest
//! matching local currently present; clearing it reveals the older local.
//!
//! The same holds for the binders of a `cases … with` alternative and of a
//! `case` (`target_equation::name_local_shadowing`): the field the user names
//! is the newest local of that name.
//!
//! Each twin is a source Lean 4.8.0 REJECTS where the older local WOULD prove
//! the goal: a lookup that reached the older local accepts the twin. Lean's
//! refusal is quoted on each.

use crate::common::*;

// --- `rw [h] at hn` ------------------------------------------------------

#[test]
fn test_cases_named_target_rw_at_uses_the_new_equation() {
    let src = format!(
        "{OPT_FN}theorem sh_rw (P : Option Nat → Prop) (n : Nat) (h : True) (hn : P (f n)) : \
         P none ∨ ∃ y, f n = some y := by\n  cases h : f n with\n  \
         | none => rw [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_axiom_free(&src, "`rw [h] at hn` after `cases h : f n`", &["sh_rw"]);
}

#[test]
fn test_cases_named_target_rw_at_never_reaches_the_older_local() {
    // Lean 4.8: "tactic 'rewrite' failed, did not find instance of the
    // pattern in the target expression f n" — `h` is `f n = none`; the
    // older `h✝ : f m = none` would have rewritten `hn`.
    let src = format!(
        "{OPT_FN}theorem sh_rw_twin (P : Option Nat → Prop) (n m : Nat) (h : f m = none) \
         (hn : P (f m)) : P none ∨ ∃ y, f n = some y := by\n  cases h : f n with\n  \
         | none => rw [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_refused_at(
        &src,
        "`rw [h]` reaching the older `h`",
        "sh_rw_twin",
        NO_MATCH,
    );
}

// --- `simp only [h] at hn` -----------------------------------------------

#[test]
fn test_cases_named_target_simp_at_uses_the_new_equation() {
    let src = format!(
        "{OPT_FN}theorem sh_simp (P : Option Nat → Prop) (n : Nat) (h : True) (hn : P (f n)) : \
         P none ∨ ∃ y, f n = some y := by\n  cases h : f n with\n  \
         | none => simp only [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_axiom_free(
        &src,
        "`simp only [h] at hn` after `cases h : f n`",
        &["sh_simp"],
    );
}

#[test]
fn test_cases_named_target_simp_at_never_reaches_the_older_local() {
    // Lean 4.8: "simp made no progress".
    let src = format!(
        "{OPT_FN}theorem sh_simp_twin (P : Option Nat → Prop) (n m : Nat) (h : f m = none) \
         (hn : P (f m)) : P none ∨ ∃ y, f n = some y := by\n  cases h : f n with\n  \
         | none => simp only [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_refused_at(
        &src,
        "`simp only [h]` reaching the older `h`",
        "sh_simp_twin",
        NO_PROGRESS,
    );
}

// --- `cases h` / `subst h` -----------------------------------------------

#[test]
fn test_cases_named_target_cases_on_the_equation_substitutes_it() {
    let src = "theorem sh_cases (P : Option Nat → Prop) (x : Option Nat) (h : True) (hx : P x) : \
               P none ∨ ∃ y, x = some y := by\n  cases h : x with\n  \
               | none => cases h; exact Or.inl hx\n  | some y => exact Or.inr ⟨y, rfl⟩\n";
    expect_axiom_free(src, "`cases h` on the new equation", &["sh_cases"]);
}

#[test]
fn test_cases_named_target_cases_never_eliminates_the_older_local() {
    // Lean 4.8: "application type mismatch … hx has type P z but is expected
    // to have type P none" — eliminating the older `h✝ : z = none` instead
    // would have turned `hx` into `P none`.
    let src = "theorem sh_cases_twin (P : Option Nat → Prop) (x z : Option Nat) (h : z = none) \
               (hx : P z) : P none ∨ ∃ y, x = some y := by\n  cases h : x with\n  \
               | none => cases h; exact Or.inl hx\n  | some y => exact Or.inr ⟨y, rfl⟩\n";
    expect_refused_at(
        src,
        "`cases h` eliminating the older `h`",
        "sh_cases_twin",
        MISMATCH,
    );
}

#[test]
fn test_cases_named_target_subst_uses_the_new_equation() {
    let src = "theorem sh_subst (P : Option Nat → Prop) (x : Option Nat) (h : True) (hx : P x) : \
               P none ∨ ∃ y, x = some y := by\n  cases h : x with\n  \
               | none => subst h; exact Or.inl hx\n  | some y => exact Or.inr ⟨y, rfl⟩\n";
    expect_axiom_free(src, "`subst h` on the new equation", &["sh_subst"]);
}

#[test]
fn test_cases_named_target_subst_never_reaches_the_older_local() {
    // Lean 4.8: "application type mismatch … hx has type P z but is expected
    // to have type P none".
    let src = "theorem sh_subst_twin (P : Option Nat → Prop) (x z : Option Nat) (h : z = none) \
               (hx : P z) : P none ∨ ∃ y, x = some y := by\n  cases h : x with\n  \
               | none => subst h; exact Or.inl hx\n  | some y => exact Or.inr ⟨y, rfl⟩\n";
    expect_refused_at(
        src,
        "`subst h` reaching the older `h`",
        "sh_subst_twin",
        MISMATCH,
    );
}

// --- tactic `match h : e` ------------------------------------------------

#[test]
fn test_tactic_match_annotated_discriminant_rw_at_uses_the_new_equation() {
    let src = format!(
        "{OPT_FN}theorem sh_match (P : Option Nat → Prop) (n : Nat) (h : True) (hn : P (f n)) : \
         P none ∨ ∃ y, f n = some y := by\n  match h : f n with\n  \
         | none => rw [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_axiom_free(&src, "`rw [h] at hn` after `match h : f n`", &["sh_match"]);
}

#[test]
fn test_tactic_match_annotated_discriminant_never_reaches_the_older_local() {
    // Lean 4.8: "tactic 'rewrite' failed, did not find instance of the
    // pattern in the target expression f n".
    let src = format!(
        "{OPT_FN}theorem sh_match_twin (P : Option Nat → Prop) (n m : Nat) (h : f m = none) \
         (hn : P (f m)) : P none ∨ ∃ y, f n = some y := by\n  match h : f n with\n  \
         | none => rw [h] at hn; exact Or.inl hn\n  | some y => exact Or.inr ⟨y, rfl⟩\n"
    );
    expect_refused_at(
        &src,
        "`rw [h]` after `match` reaching the older `h`",
        "sh_match_twin",
        NO_MATCH,
    );
}

// --- an alternative's or a `case`'s binder -------------------------------

// The same rule for a FIELD the user names: `| intro e hpk` and `case intro e
// hpk` bind the newest `e`, and the theorem's own `e` becomes `e✝`.

#[test]
fn test_alternative_binder_shadows_an_older_local_of_its_name() {
    let src = "theorem alt_sh (P : Nat → Prop) (a k c : Nat) (e : a = c) (h : k = c ∧ P k) : \
               P c := by\n  cases h with\n  | intro e hpk => rw [e] at hpk; exact hpk\n";
    expect_axiom_free(src, "`rw [e]` on the field `e`", &["alt_sh"]);
}

#[test]
fn test_alternative_binder_never_leaves_the_older_local_reachable() {
    // Lean 4.8: "tactic 'rewrite' failed, did not find instance of the
    // pattern in the target expression k" — `e` is the field `k = c`; the
    // theorem's `e✝ : a = c` would have rewritten `hpa : P a`.
    let src = "theorem alt_sh_twin (P : Nat → Prop) (a k c : Nat) (e : a = c) (hpa : P a) \
               (h : k = c ∧ P k) : P c := by\n  cases h with\n  \
               | intro e hpk => rw [e] at hpa; exact hpa\n";
    expect_refused_at(
        src,
        "`rw [e]` reaching the older `e`",
        "alt_sh_twin",
        NO_MATCH,
    );
}

#[test]
fn test_case_binder_shadows_an_older_local_of_its_name() {
    let src = "theorem case_sh (P : Nat → Prop) (a k c : Nat) (e : a = c) (h : k = c ∧ P k) : \
               P c := by\n  cases h\n  case intro e hpk => rw [e] at hpk; exact hpk\n";
    expect_axiom_free(src, "`rw [e]` on the `case` binder `e`", &["case_sh"]);
}

#[test]
fn test_case_binder_never_leaves_the_older_local_reachable() {
    // Lean 4.8: "tactic 'rewrite' failed, did not find instance of the
    // pattern in the target expression k".
    let src = "theorem case_sh_twin (P : Nat → Prop) (a k c : Nat) (e : a = c) (hpa : P a) \
               (h : k = c ∧ P k) : P c := by\n  cases h\n  \
               case intro e hpk => rw [e] at hpa; exact hpa\n";
    expect_refused_at(
        src,
        "`rw [e]` reaching the older `e`",
        "case_sh_twin",
        NO_MATCH,
    );
}

// --- after `clear`: the older name becomes visible again -----------------

// The retired implementation permanently renamed older locals. Lean instead
// keeps the user name and resolves a name to the NEWEST local carrying
// it on every lookup (`LocalContext.findFromUserName?`). Both the term and
// tactic programs below are accepted by the retained genuine Lean 4.30.0-rc2
// measurement. Newest-present lookup keeps the old local available after clear.

const CLEARED_SHADOW: &str = "(P : Nat → Prop) (a c : Nat) (e : a = c) (hpa : P a) (k : Nat) \
                              (h : k = c ∧ P k) : P c := by\n  cases h with\n  \
                              | intro e hpk => clear e; ";

#[test]
fn test_cleared_shadowing_binder_restores_the_older_tactic_name() {
    // The exact program is accepted by genuine pinned Lean 4.30.0-rc2.
    // After `clear e`, the theorem's `e : a = c` becomes visible again.
    let src = format!("theorem clr {CLEARED_SHADOW}rw [e] at hpa; exact hpa\n");
    expect_axiom_free(&src, "`rw [e]` after `clear e`", &["clr"]);
}

#[test]
fn test_cleared_shadowing_binder_term_reaches_the_older_local() {
    // Pinned Lean 4.8.0 accepts it, and so does Clean's term elaborator.
    let src = format!("theorem clr_exact {CLEARED_SHADOW}exact e ▸ hpa\n");
    expect_axiom_free(&src, "a term naming `e` after `clear e`", &["clr_exact"]);
}

#[test]
fn test_shadow_three_ok() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_three_ok.lean");
    expect_axiom_free(src, "shadow_three_ok", &["shadow_three_ok"]);
}

#[test]
fn test_shadow_three_bad() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_three_bad.lean");
    expect_refused_at(src, "shadow_three_bad", "shadow_three_bad", MISMATCH);
}

#[test]
fn test_shadow_clear_all_ok() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_clear_all_ok.lean");
    expect_axiom_free(src, "shadow_clear_all_ok", &["shadow_clear_all_ok"]);
}

#[test]
fn test_shadow_clear_all_bad() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_clear_all_bad.lean");
    expect_refused_at(
        src,
        "shadow_clear_all_bad",
        "shadow_clear_all_bad",
        &["unknown identifier", "hypothesis not found"],
    );
}

#[test]
fn test_shadow_rename_old_ok() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_rename_old_ok.lean");
    expect_axiom_free(src, "shadow_rename_old_ok", &["shadow_rename_old_ok"]);
}

#[test]
fn test_shadow_rename_after_clear_bad() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_rename_after_clear_bad.lean");
    expect_refused_at(
        src,
        "shadow_rename_after_clear_bad",
        "shadow_rename_after_clear_bad",
        &["too many variable names"],
    );
}

#[test]
fn test_shadow_rename_two_ok() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_rename_two_ok.lean");
    expect_axiom_free(src, "shadow_rename_two_ok", &["shadow_rename_two_ok"]);
}

#[test]
fn test_shadow_rename_two_bad() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_rename_two_bad.lean");
    expect_refused_at(
        src,
        "shadow_rename_two_bad",
        "shadow_rename_two_bad",
        MISMATCH,
    );
}

#[test]
fn test_shadow_hygiene_ok() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_hygiene_ok.lean");
    expect_axiom_free(src, "shadow_hygiene_ok", &["shadow_hygiene_ok"]);
}

#[test]
fn test_shadow_hygiene_bad() {
    let src = include_str!("../fixtures/cleared_shadow/shadow_hygiene_bad.lean");
    expect_refused_at(src, "shadow_hygiene_bad", "shadow_hygiene_bad", MISMATCH);
}
