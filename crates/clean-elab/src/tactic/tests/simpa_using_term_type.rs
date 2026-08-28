// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simpa … using e` must simplify `e`'s TYPE, not just the goal.
//!
//! Lean 4's `simpa` simplifies BOTH the goal and the `using` term's type, then
//! closes the goal with the transported term. Clean's live compound handler
//! (`builtins_phase3d_rewrite::compound_simpa`) simplified only the goal and
//! then ran `exact` on the RAW term, so `simpa using h` worked exactly when
//! simp was a no-op on `h` — which is why the g_simp fixture scored 4/21.
//!
//! The correct semantics were already written down as spec on
//! `SurfaceTactic::Simpa::using_term` (`clean-parser/src/surface_tactic.rs`):
//! "simplifies both the goal and `term`'s type and closes the goal with the
//! simplified term". This was a documented-spec-vs-implementation mismatch.
//!
//! Each test drives the production path — `parse_file` → preprocess →
//! elaborate → kernel — so the compound handler registered at
//! `register_phase3d_rewrite` is the code under test, not a hand-built
//! `SurfaceTactic`.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_closed(code: &str, what: &str) {
    let results = elab_all(code);
    assert!(!results.is_empty(), "{what}: nothing parsed");
    for result in &results {
        assert!(
            matches!(result, Ok(ElabResult::Theorem { .. })),
            "{what}: expected a kernel-registered theorem, got {result:?}"
        );
    }
}

/// `h : p ∧ True ⊢ p` — the `p_simpa_03` shape. The goal is already normal, so
/// only simplifying `h`'s type can close this. `exact h` on the raw term fails:
/// `p ∧ True` is not definitionally `p`.
#[test]
fn test_simpa_using_simplifies_a_conjunction_with_true() {
    assert_closed(
        "theorem simpaAndTrue (p : Prop) (h : p ∧ True) : p := by simpa using h\n",
        "simpa using (h : p ∧ True)",
    );
}

/// Nested version — `p_simpa_07`. Proves the transport survives a rewrite that
/// happens under a constructor rather than at the root.
#[test]
fn test_simpa_using_simplifies_a_nested_conjunction() {
    assert_closed(
        "theorem simpaNested (p q : Prop) (h : (True ∧ p) ∧ q) : p ∧ q := by simpa using h\n",
        "simpa using (h : (True ∧ p) ∧ q)",
    );
}

/// `h : 0 + a = 5 ⊢ a = 5` — the `p_simpa_06` shape. Arithmetic rather than
/// propositional, so the transported equality is over `Prop` reached through a
/// `Nat` congruence.
#[test]
fn test_simpa_using_simplifies_an_arithmetic_hypothesis() {
    assert_closed(
        "theorem simpaZeroAdd (a : Nat) (h : 0 + a = 5) : a = 5 := by simpa using h\n",
        "simpa using (h : 0 + a = 5)",
    );
}

/// Control 1 — the goal-side half must keep working. `p_simpa_01`/`p_simpa_02`
/// were already passing before this brick and are the rows the fix must not
/// cost: here simp is a no-op on `h` and does the work on the goal.
#[test]
fn test_simpa_goal_side_still_works() {
    assert_closed(
        "theorem simpaGoalSide (a : Nat) (h : a = 5) : a + 0 = 5 := by simpa\n",
        "simpa (goal side, no using term)",
    );
    assert_closed(
        "theorem simpaGoalSide2 (a : Nat) : a + 0 = a := by simpa\n",
        "simpa (goal side, closes by simp alone)",
    );
}

/// Control 2 — a `using` term on which simp genuinely IS a no-op must still
/// close by `exact`. The transport helper returns the term untouched when simp
/// makes no progress, so this path must be unchanged.
#[test]
fn test_simpa_using_a_term_simp_cannot_touch_still_closes() {
    assert_closed(
        "theorem simpaExactShape (p : Prop) (h : p) : p := by simpa using h\n",
        "simpa using (h : p) — nothing to simplify on either side",
    );
}
