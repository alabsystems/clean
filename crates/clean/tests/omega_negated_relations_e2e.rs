// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `omega` on negated linear relations `¬(rel)`.
//!
//! Covers the completeness gap where `omega` could not handle `Not (<linear
//! relation>)` in either hypothesis or goal position:
//!   - HYPOTHESIS-side: `¬(a ≤ 2)` / `¬(a < b)` hypotheses (normalized to their
//!     positive form via proof-carrying `push_neg`).
//!   - GOAL-side: `¬(a ≥ 3)` goal (normalized to `a < 3`) and `¬(a = 5)` goal
//!     (closed from a bounding inequality hypothesis via an intro-to-False
//!     reconstruction).
//!
//! Every positive case builds a kernel-re-checked proof term (the `omega`
//! certificate is independently kernel-verified by `close_goal`). The negative
//! cases MUST stay failing: they are genuinely unprovable, so a pass would mean
//! `omega` became unsound.
//!
//! Run with:
//!   cargo test -p clean --test omega_negated_relations_e2e

use clean::{check_source, CheckConfig, CheckResult};

fn default_config() -> CheckConfig {
    CheckConfig::default()
}

/// Assert the source kernel-checks: no errors and at least one passed decl.
fn assert_proves(source: &str, context: &str) {
    let result: CheckResult =
        check_source(source, &default_config()).expect("source should parse and elaborate");
    assert!(
        result.errors.is_empty(),
        "{context}: expected omega to prove the goal (kernel-checked), got errors: {:?}",
        result.errors
    );
    assert!(
        result.passed_count >= 1,
        "{context}: expected >=1 passed decl, got {}",
        result.passed_count
    );
}

/// Assert the source does NOT prove (omega must fail closed): the pipeline does
/// not panic, and the (genuinely unprovable) declaration is reported as an error
/// rather than passing.
fn assert_fails_closed(source: &str, context: &str) {
    let result: CheckResult =
        check_source(source, &default_config()).expect("source should still parse");
    assert!(
        !result.errors.is_empty(),
        "{context}: UNPROVABLE goal must fail closed, but omega reported no errors \
         (passed={})",
        result.passed_count
    );
}

// ---------------------------------------------------------------------------
// Positive teeth — must kernel-check (`1 passed`).
// ---------------------------------------------------------------------------

#[test]
fn test_omega_neg_le_hypothesis_proves() {
    // ¬(a ≤ 2) means a > 2, i.e. a ≥ 3.
    assert_proves(
        "theorem t (a : Nat) (h : ¬ (a ≤ 2)) : a ≥ 3 := by omega",
        "tooth 1: ¬(a≤2) hypothesis ⊢ a≥3",
    );
}

#[test]
fn test_omega_neg_lt_hypothesis_proves() {
    // ¬(a < b) means a ≥ b, i.e. b ≤ a.
    assert_proves(
        "theorem t (a b : Nat) (h : ¬ (a < b)) : b ≤ a := by omega",
        "tooth 2: ¬(a<b) hypothesis ⊢ b≤a",
    );
}

#[test]
fn test_omega_neg_ge_goal_proves() {
    // goal ¬(a ≥ 3); a < 3 contradicts a ≥ 3.
    assert_proves(
        "theorem t (a : Nat) (h : a < 3) : ¬ (a ≥ 3) := by omega",
        "tooth 3: a<3 ⊢ ¬(a≥3)",
    );
}

#[test]
fn test_omega_neg_eq_goal_proves() {
    // goal ¬(a = 5), i.e. a ≠ 5; a < 3 ⟹ a ≠ 5.
    assert_proves(
        "theorem t (a : Nat) (h : a < 3) : ¬ (a = 5) := by omega",
        "tooth 4: a<3 ⊢ ¬(a=5)",
    );
}

// ---------------------------------------------------------------------------
// Negative teeth — must stay FAILING (proves omega did not become unsound).
// ---------------------------------------------------------------------------

#[test]
fn test_omega_neg_self_contradiction_goal_fails_closed() {
    // ¬(a < 3) cannot be proved while a < 3 holds — unprovable goal.
    assert_fails_closed(
        "theorem t (a : Nat) (h : a < 3) : ¬ (a < 3) := by omega",
        "tooth 5: a<3 ⊬ ¬(a<3)",
    );
}

#[test]
fn test_omega_neg_le_hypothesis_wrong_conclusion_fails_closed() {
    // ¬(a ≤ 5) means a ≥ 6, which does NOT imply a ≤ 3.
    assert_fails_closed(
        "theorem t (a : Nat) (h : ¬ (a ≤ 5)) : a ≤ 3 := by omega",
        "tooth 6: ¬(a≤5) ⊬ a≤3",
    );
}

#[test]
fn test_omega_neg_ge_goal_unprovable_fails_closed() {
    // a ≥ 3 ⊬ ¬(a ≥ 3) — unprovable.
    assert_fails_closed(
        "theorem t (a : Nat) (h : a ≥ 3) : ¬ (a ≥ 3) := by omega",
        "tooth 7: a≥3 ⊬ ¬(a≥3)",
    );
}

// ---------------------------------------------------------------------------
// Extra soundness guards for the negated-equality goal reconstruction: a
// `¬(a = k)` goal where `k` is actually reachable is FALSE and must fail closed.
// ---------------------------------------------------------------------------

#[test]
fn test_omega_neg_eq_goal_reachable_value_fails_closed() {
    // a < 3 allows a = 2, so ¬(a = 2) is NOT provable.
    assert_fails_closed(
        "theorem t (a : Nat) (h : a < 3) : ¬ (a = 2) := by omega",
        "soundness: a<3 ⊬ ¬(a=2)",
    );
}

#[test]
fn test_omega_neg_eq_goal_from_lower_bound_proves() {
    // a ≥ 3 excludes a = 1, so ¬(a = 1) is provable.
    assert_proves(
        "theorem t (a : Nat) (h : a ≥ 3) : ¬ (a = 1) := by omega",
        "positive: a≥3 ⊢ ¬(a=1)",
    );
}

#[test]
fn test_omega_neg_eq_goal_boundary_reachable_fails_closed() {
    // a < 3 reaches a = 0/1/2; ¬(a = 0) is FALSE, must fail closed.
    assert_fails_closed(
        "theorem t (a : Nat) (h : a < 3) : ¬ (a = 0) := by omega",
        "soundness: a<3 ⊬ ¬(a=0)",
    );
}

#[test]
fn test_omega_neg_eq_goal_upper_bound_reachable_fails_closed() {
    // a ≥ 3 reaches a = 5; ¬(a = 5) is FALSE, must fail closed.
    assert_fails_closed(
        "theorem t (a : Nat) (h : a ≥ 3) : ¬ (a = 5) := by omega",
        "soundness: a≥3 ⊬ ¬(a=5)",
    );
}

#[test]
fn test_omega_neg_le_hypothesis_gt_form_proves() {
    // ¬(a > 5) hypothesis means a ≤ 5, i.e. a < 6.
    assert_proves(
        "theorem t (a : Nat) (h : ¬ (a > 5)) : a ≤ 5 := by omega",
        "positive: ¬(a>5) ⊢ a≤5",
    );
}
