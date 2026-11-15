// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `cases` on a nested inductive's member (trust-ir gap G45, ledger (115)):
//! the native block `casesOn` takes every block member's motive and minors
//! (`crate::tactic::cases_on_spine`: lane D's `cases_block_spine` and lane B's
//! brick B5 built the same `PUnit`-filled spine; the round-6 integration keeps
//! B's, which reads every slot off the eliminator's declared type).
//!
//! Pinned Lean 4.8.0 (2026-10-16) accepts `key_some` and `key_cases` below
//! and refuses `key_bad` (`rfl` fails in case `int`). Before the fix Clean
//! refused every `cases c` here with a goal whose auxiliary motives were
//! typed by the primary constructors' fields (`fun (f : Float) => …` applied
//! to `Prod.mk s c`), the trust-ir `constantKey_inj` / `constInt_denote` rows.
//!
//! `key_int` is the trust-ir shape: a hypothesis mentions the case-split
//! variable. Lean's `cases` generalizes it; Clean's left it about the
//! eliminated variable (trust-ir gap G64, the `cases` face of G22), pinned
//! here as a refusal until round-5 lane B's class (80) fix closed it; it is a
//! PASS test with a twin since the round-6 integration.

use crate::module_driver::VerdictKind;
use crate::tests_do_lane_r5_lift::{assert_passed, check_module, verdict};

const NESTED: &str = "inductive C where\n  | int : Int → C\n  | float : Float → C\n  | bool : Bool → C\n  | record : List (String × C) → C\n\n\
def key : C → Option Int\n  | .int v => some v\n  | _ => none\n\n";

#[test]
fn test_cases_nested_inductive_member_passes() {
    let report = check_module(&format!(
        "{NESTED}theorem key_some (c : C) : key c = key c := by\n  cases c\n  all_goals rfl\n\n\
         theorem key_cases (c : C) : key c = none ∨ ∃ v, key c = some v := by\n  cases c with\n  | int v => exact Or.inr ⟨v, rfl⟩\n  | float f => exact Or.inl rfl\n  | bool b => exact Or.inl rfl\n  | record r => exact Or.inl rfl\n"
    ));
    assert_passed(&report, "key_some");
    assert_passed(&report, "key_cases");
}

#[test]
fn test_cases_nested_inductive_false_goal_refused() {
    let report = check_module(&format!(
        "{NESTED}theorem key_bad (c : C) : key c = none := by\n  cases c with\n  | int v => rfl\n  | float f => rfl\n  | bool b => rfl\n  | record r => rfl\n"
    ));
    let v = verdict(&report, "key_bad");
    assert_ne!(v.kind, VerdictKind::Passed, "Lean refuses key_bad: {v:#?}");
}

#[test]
fn test_cases_dependent_hypothesis_is_generalized_g64() {
    // Lean 4.8.0 accepts `key_int`: `cases c` turns `h : key c = some k` into
    // `h : key (C.int v) = some k`. This was the open pin of G64 (`cases`
    // left `h` about `c`, so `rw [h]` found no `key (C.int v)`); round-5 lane
    // B's class (80) fix (`docs/DECISIONS.md` R63, `tactic/major_dependents.rs`)
    // closes it, and the round-6 integration flips it. The twin claims
    // `C.int (k + 1)`: pinned Lean 4.8.0 leaves `C.int k = C.int (k + 1)`
    // unsolved (measured 2026-10-17).
    let report = check_module(&format!(
        "{NESTED}theorem key_int {{c : C}} {{k : Int}} (h : key c = some k) : c = .int k := by\n  cases c with\n  | int v => simp [key] at h; rw [h]\n  | float f => simp [key] at h\n  | bool b => simp [key] at h\n  | record r => simp [key] at h\n\n\
         theorem key_int_twin {{c : C}} {{k : Int}} (h : key c = some k) : c = .int (k + 1) := by\n  cases c with\n  | int v => simp [key] at h; rw [h]\n  | float f => simp [key] at h\n  | bool b => simp [key] at h\n  | record r => simp [key] at h\n"
    ));
    assert_passed(&report, "key_int");
    let v = verdict(&report, "key_int_twin");
    assert_ne!(
        v.kind,
        VerdictKind::Passed,
        "Lean refuses key_int_twin: {v:#?}"
    );
}
