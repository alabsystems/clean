// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic surfaces the in-tree `Mathbot/` task fixtures use, checked through
//! the `clean check` pipeline: `parse_file_with_tactics` with the builtin
//! patterns, `preprocess_decl_with_context`, then registration, where the
//! kernel re-checks the proof. A passing fixture must register with no trust
//! warning (no `sorry` of any kind); every negative control must be refused.
//!
//! The fixtures are the theorems of `Mathbot/Tasks/Llvm2.lean`,
//! `Mathbot/Tasks/Lrat.lean` and `Mathbot/Calibration.lean`'s
//! `c3_xor_parity_unsat`, written at top level so a failure is the
//! declaration's own result, and the shapes of class (80) of
//! `docs/FRONTEND_CLASS_LEDGER.md`, which the same `cases` change closed.

use crate::tactic::builtins::builtin_tactic_patterns;
use crate::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file_with_tactics;

/// The outcome of each declaration in `code`: `Ok` when it registered with no
/// trust warning, otherwise the error or the warning.
fn check(code: &str) -> Vec<Result<(), String>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file_with_tactics(code, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            match elaborate_decl_and_register_with_context_and_warning(
                &mut env,
                &processed,
                &mut file_ctx,
            ) {
                Ok(registered) => match registered.warning {
                    None => Ok(()),
                    Some(warning) => Err(format!("registered with a warning: {warning:?}")),
                },
                Err(err) => Err(format!("{err:?}")),
            }
        })
        .collect()
}

fn assert_all_check(code: &str, label: &str) {
    for (i, outcome) in check(code).into_iter().enumerate() {
        if let Err(err) = outcome {
            panic!("{label}: declaration {i} must check: {err}");
        }
    }
}

fn assert_last_refused(code: &str, label: &str) {
    let outcomes = check(code);
    let (last, setup) = outcomes.split_last().expect("fixture has declarations");
    for (i, outcome) in setup.iter().enumerate() {
        if let Err(err) = outcome {
            panic!("{label}: setup declaration {i} must check: {err}");
        }
    }
    assert!(
        last.is_err(),
        "{label}: the last declaration must be refused"
    );
}

const LLVM2_KERNELS: &str = "\
def sourceAddKernel (x y : Nat) : Nat :=
  x + (y + 1)

def loweredAddKernel (x y : Nat) : Nat :=
  x + y + 1
";

/// `Mathbot/Tasks/Llvm2.lean`: `unfold a b` unfolds both names (Lean's
/// `unfold id+`). Clean read the second name as a tactic of its own.
#[test]
fn test_unfold_two_names_then_rw_checks() {
    let code = format!(
        "{LLVM2_KERNELS}
theorem llvm2_add_kernel_denotation_preserved
    (x y : Nat) :
    loweredAddKernel x y = sourceAddKernel x y := by
  unfold loweredAddKernel sourceAddKernel
  rw [Nat.add_assoc]
"
    );
    assert_all_check(&code, "Llvm2 unfold of two names");
}

/// Both names are unfolded at the hypothesis the tactic names.
#[test]
fn test_unfold_two_names_at_a_hypothesis_checks() {
    let code = format!(
        "{LLVM2_KERNELS}
theorem kernels_agree_from_hypothesis
    (x y z : Nat) (h : loweredAddKernel x y = sourceAddKernel x z) :
    x + y + 1 = x + (z + 1) := by
  unfold loweredAddKernel sourceAddKernel at h
  exact h
"
    );
    assert_all_check(&code, "unfold of two names at h");
}

/// Negative control: unfolding both names does not make a false equation
/// provable.
#[test]
fn test_unfold_two_names_keeps_a_false_goal_refused() {
    let code = format!(
        "{LLVM2_KERNELS}
theorem kernels_differ (x y : Nat) :
    loweredAddKernel x y = sourceAddKernel x (y + 1) := by
  unfold loweredAddKernel sourceAddKernel
  rw [Nat.add_assoc]
"
    );
    assert_last_refused(&code, "false kernel equation");
}

/// `Mathbot/Calibration.lean`'s `c3_xor_parity_unsat`: after `cases b`, each
/// case reads `h0`/`h1` at that case's constructor, so `simp at h0 h1` finds
/// `false = true` (or `true = false`) and closes it.
#[test]
fn test_cases_bool_carries_dependent_hypotheses_into_simp() {
    assert_all_check(
        "theorem c3_xor_parity_unsat (b : Bool) (h0 : b = false) (h1 : b = true) : False := by
  cases b <;> simp at h0 h1
",
        "Calibration c3",
    );
}

/// `Mathbot/Tasks/Lrat.lean`: the carried hypotheses are unfolded and
/// simplified in each case.
#[test]
fn test_cases_bool_carries_hypotheses_through_definitions() {
    assert_all_check(
        "def positiveUnitSatisfied (assignment : Bool) : Prop :=
  assignment = true

def negativeUnitSatisfied (assignment : Bool) : Prop :=
  assignment = false

theorem lrat_unit_conflict_sound
    (assignment : Bool)
    (hpos : positiveUnitSatisfied assignment)
    (hneg : negativeUnitSatisfied assignment) :
    False := by
  cases assignment <;> simp [positiveUnitSatisfied, negativeUnitSatisfied] at hpos hneg
",
        "Lrat unit conflict",
    );
}

/// The carried hypothesis is usable by name in each case, under bullets and
/// under `with` alternatives (whose field names are applied first).
#[test]
fn test_cases_carried_hypothesis_is_the_cases_own() {
    assert_all_check(
        "theorem bullets (b : Bool) (h : b = true) : b = true := by
  cases b
  · exact h
  · exact h

theorem alternatives (n : Nat) (h : 0 < n + 1) : 0 < n + 1 := by
  cases n with
  | zero => exact h
  | succ k => exact h

theorem succ_witness (n : Nat) (h : n ≠ 0) : ∃ k, n = k + 1 := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => exact ⟨k, rfl⟩
",
        "carried hypotheses",
    );
}

/// The local is reverted by identity: with an older `h` shadowed by the one
/// that mentions `b`, each case's `h` is the carried one.
#[test]
fn test_cases_carries_the_shadowing_hypothesis() {
    assert_all_check(
        "theorem shadowed (h : True) (b : Bool) (h : b = true) : b = true := by
  cases b
  · exact h
  · exact h
",
        "shadowed carried hypothesis",
    );
}

/// Negative control: in the `true` case the carried hypothesis reads
/// `true = true`, which proves nothing about the goal `true = false`.
#[test]
fn test_cases_carried_hypothesis_does_not_prove_another_case() {
    assert_last_refused(
        "theorem bad (b : Bool) (h : b = true) : b = false := by
  cases b
  · rfl
  · exact h
",
        "true case of b = false",
    );
}

/// Negative control: `h : b = false` becomes `false = false` in the `false`
/// case, which `simp` discards, so `False` stays unproved there.
#[test]
fn test_cases_consistent_hypothesis_stays_unrefuted() {
    assert_last_refused(
        "theorem bad (b : Bool) (h : b = false) : False := by
  cases b <;> simp at h
",
        "consistent b = false",
    );
}

/// Class (80) of `docs/FRONTEND_CLASS_LEDGER.md`, the shape trust-ir's
/// semantics package pinned: the `false` alternative's `h` is
/// `false = true`, its goal's own statement.
#[test]
fn test_cases_dependent_hypothesis_is_specialized_class_80() {
    assert_all_check(
        "theorem cases_dep_hyp (b : Bool) (h : b = true) : b = true := by
  cases b with
  | false => exact h
  | true => rfl
",
        "class (80)",
    );
}

/// Negative control for class (80): the `true` alternative's `h` is
/// `true = true`, which does not prove `true = false`.
#[test]
fn test_cases_dependent_hypothesis_proves_only_its_case_class_80() {
    assert_last_refused(
        "theorem cases_dep_hyp_bad (b : Bool) (h : b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact h
",
        "class (80) negative control",
    );
}

const OPTION_HEAD: &str = "\
def g (l : List Nat) : Option Nat := l.head?
";

/// Class (80)'s second face: after `generalize h : g l = x`, `cases x`
/// carries the tactic-introduced `h`, so `have … := h` reads `g l = some v`
/// (the ledger's "Too many arguments: function type `g l = x`" was the stale
/// `h`). `gen_alts`'s goal does not mention `g l`, so `generalize` leaves it
/// and the case proves it from `h`. Under bullets and alternatives, with
/// `at`, and with `h` unused.
#[test]
fn test_cases_carries_a_generalized_equation_class_80() {
    let code = format!(
        "{OPTION_HEAD}
theorem gen_alts (l : List Nat) (hy : g l ≠ none) : ∃ z, l.head? = some z := by
  generalize h : g l = x
  cases x with
  | none => exact absurd h hy
  | some v =>
    have h2 : g l = some v := h
    exact ⟨v, h2⟩

theorem gen_bullets (l : List Nat) (hy : g l ≠ none) : ∃ z, g l = some z := by
  generalize h : g l = x
  cases x
  · exact absurd h hy
  · exact ⟨_, rfl⟩

theorem gen_at (l : List Nat) (y : Nat) (hy : g l = some y) : ∃ z, g l = some z := by
  generalize h : g l = x at hy
  cases x with
  | none => simp at hy
  | some v => exact ⟨v, rfl⟩

theorem gen_unused (n : Nat) : True := by
  generalize hk : n + 1 = k
  cases k with
  | zero => trivial
  | succ m => trivial
"
    );
    assert_all_check(&code, "generalized equation carried by cases");
}

/// Negative control: in the `some` case the carried equation is
/// `g l = some v`, which does not prove `some v = none`.
#[test]
fn test_cases_generalized_equation_proves_only_its_case_class_80() {
    let code = format!(
        "{OPTION_HEAD}
theorem gen_bad (l : List Nat) : g l = none := by
  generalize h : g l = x
  cases x with
  | none => rfl
  | some v => exact h
"
    );
    assert_last_refused(&code, "generalized equation negative control");
}
