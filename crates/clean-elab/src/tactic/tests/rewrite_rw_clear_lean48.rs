// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rewrite` vs `rw`, and `clear`'s dependency refusals, against pinned Lean
//! 4.8.0 (integ/r5 fix, 2026-10-16). Every row is a declaration of the probe
//! `RewriteForms.lean` / `clr.lean` with the oracle's verdict.
//!
//! * `rewrite [rules] (at loc)?` is the rewrite alone: a goal it leaves
//!   reflexive stays open ("unsolved goals"). Clean parsed `rewrite` as `rw`.
//! * `rw` is Lean's macro `rewrite …; try (with_reducible rfl)` at EVERY
//!   location; the closing `rfl` is REDUCIBLE, so `rw [h]` leaving `ff 1 = 2`
//!   (`def ff x := x + 1`), `b + 0 = b` or `[] ++ [1] = [1]` is "unsolved
//!   goals" (Clean's goal path closed them with a full-transparency `rfl`),
//!   while literal arithmetic (`2 + 2 = 4`) and a projection of a pair
//!   literal still close.
//! * `clear h` refuses when a later local or the target mentions `h`
//!   (`MVarId.clear`); `clear h hp` clears the later `hp` first.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext};

const FF: &str = "def ff (x : Nat) : Nat := x + 1\n";

#[test]
fn shared_sibling_context_types_keep_free_variables_under_binders() {
    use clean_kernel::{BinderInfo, Expr, FVarId};
    use std::sync::Arc;

    let a = FVarId::new(17);
    let b = FVarId::new(18);
    let mut shared = Arc::new(Expr::lam(
        BinderInfo::Default,
        Expr::fvar(a),
        Expr::app(Expr::bvar(0), Expr::fvar(b)),
    ));
    for _ in 0..12 {
        shared = Arc::new(Expr::app_arc(Arc::clone(&shared), shared));
    }
    let vars = crate::tactic::hypothesis::collect_fvars(&shared);
    assert_eq!(vars, [a, b].into_iter().collect());
    assert!(crate::tactic::hypothesis::collect_fvars(&Expr::prop()).is_empty());
}

/// The outcome of the LAST declaration of `code` (every earlier one must
/// elaborate) in a fresh prelude environment.
fn elab_last(code: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    assert!(!decls.is_empty(), "nothing parsed from:\n{code}");
    let mut last = Ok(());
    for (i, decl) in decls.iter().enumerate() {
        assert!(
            last.is_ok(),
            "declaration {} failed: {last:?}\n{code}",
            i.saturating_sub(1)
        );
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map(|_| ())
            .map_err(|e| e.to_string());
    }
    last
}

#[track_caller]
fn accepts(code: &str) {
    if let Err(e) = elab_last(code) {
        panic!("Lean 4.8.0 accepts; Clean refused: {e}\n--- source ---\n{code}");
    }
}

#[track_caller]
fn refuses(code: &str, needle: &str) {
    match elab_last(code) {
        Ok(()) => panic!("Lean 4.8.0 refuses; Clean accepted\n--- source ---\n{code}"),
        Err(e) => assert!(
            e.to_lowercase().contains(&needle.to_lowercase()),
            "refused for another reason than `{needle}`: {e}\n--- source ---\n{code}"
        ),
    }
}

/// r1/r6: `rewrite … at h` leaves the main goal alone, so `exact h` and
/// `rfl` still have it; n1 is the `rw` neighbour, whose reducible `rfl`
/// closes `x = x` first ("no goals to be solved").
#[test]
fn test_rewrite_at_hypothesis_has_no_trailing_rfl() {
    accepts(
        "theorem r1 (x : Nat) (h : x + 0 = x) : x = x := by rewrite [Nat.add_zero] at h; exact h\n",
    );
    refuses(
        "theorem n1 (x : Nat) (h : x + 0 = x) : x = x := by rw [Nat.add_zero] at h; exact h\n",
        "no goals",
    );
    accepts("theorem r6 (a b : Nat) (h : a = b) (h2 : a = 3) : b = 3 := by rwa [h] at h2\n");
    refuses(
        "theorem n6 (a b : Nat) (h : a = b) (h2 : a = 3) : b = 3 := by rewrite [h] at h2\n",
        "unsolved goals",
    );
}

/// n2 (the D2 twin): `rewrite [h]` leaving `b = b` is "unsolved goals"; r2
/// closes it with an explicit `rfl`; r8 / n7 are the `rw` neighbours.
#[test]
fn test_rewrite_at_goal_leaves_a_reflexive_goal_open() {
    refuses(
        "theorem n2 (a b : Nat) (h : a = b) : a = b := by rewrite [h]\n",
        "unsolved goals",
    );
    accepts("theorem r2 (a b : Nat) (h : a = b) : a = b := by\n  rewrite [h]\n  rfl\n");
    accepts("theorem r8 (a b : Nat) (h : a = b) : a = b := by rw [h]\n");
    refuses(
        "theorem n7 (a b : Nat) (h : a = b) : a = b := by\n  rw [h]\n  rfl\n",
        "no goals",
    );
}

/// n3: `rw`'s closing `rfl` is reducible, so a semireducible user `def` is not
/// unfolded; r3/r4/r7 are what it (or an explicit `rfl`) still closes; r5 is
/// `rwa` at the goal. n4/n5 (`b + 0 = b`, `[] ++ [1] = [1]`), which Lean 4.8.0
/// also leaves open, are still closed: Clean's builtin prelude marks the
/// operator instances and `Nat.add` reducible where Lean has them
/// semireducible — ledger class (153), pinned in
/// `test_rw_reducible_rfl_sees_through_the_prelude_known_false_acceptance`.
#[test]
fn test_rw_closes_only_by_reducible_rfl() {
    refuses(
        &format!("{FF}theorem n3 (a : Nat) (h : a = 1) : ff a = 2 := by rw [h]\n"),
        "unsolved goals",
    );
    accepts("theorem r3 (a : Nat) (h : a = 2) : a + 2 = 4 := by rw [h]\n");
    accepts("theorem r4 (p : Nat × Nat) (h : p = (1, 2)) : p.1 = 1 := by rw [h]\n");
    accepts(&format!(
        "{FF}theorem r7 (a : Nat) (h : a = 1) : ff a = 2 := by rw [h]; rfl\n"
    ));
    accepts("theorem r5 (a b c : Nat) (h : a = b) (h2 : b = c) : a = c := by rwa [h]\n");
}

/// c1/c2/c6: `clear` refuses a hypothesis something later depends on, with
/// `MVarId.clear`'s messages; c3/c4 clear both (the later one first); c5 is
/// the plain clear.
#[test]
fn test_clear_refuses_a_hypothesis_with_dependents() {
    refuses(
        "theorem c1 (a : Nat) (h : a = 1) (hp : h = h) : True := by\n  clear h\n  trivial\n",
        "variable 'hp' depends on 'h'",
    );
    refuses(
        "theorem c2 (a : Nat) (h : a = 1) : h = h := by\n  clear h\n  rfl\n",
        "target depends on 'h'",
    );
    refuses(
        "theorem c6 (a : Nat) (h : a = 1) : a = 1 := by\n  clear a\n  exact h\n",
        "variable 'h' depends on 'a'",
    );
    accepts(
        "theorem c3 (a : Nat) (h : a = 1) (hp : h = h) : True := by\n  clear h hp\n  trivial\n",
    );
    accepts(
        "theorem c4 (a : Nat) (h : a = 1) (hp : h = h) : True := by\n  clear hp h\n  trivial\n",
    );
    accepts("theorem c5 (a : Nat) (h : a = 1) : True := by\n  clear h\n  trivial\n");
}

/// n4/n5, KNOWN FALSE ACCEPTANCE (ledger class (153), G83): pinned Lean 4.8.0
/// says "unsolved goals" for both (`with_reducible rfl` cannot unfold the
/// semireducible `instHAdd` / `Nat.add` / `instHAppend` / `List.append`);
/// Clean's builtin prelude marks them reducible, so the reducible `rfl` closes
/// them. The full-transparency `rfl` `rw` used before this change closed them
/// too, so this is not new. Fails the day it closes; then move both rows back
/// to `test_rw_closes_only_by_reducible_rfl` as refusals.
#[test]
fn test_rw_reducible_rfl_sees_through_the_prelude_known_false_acceptance() {
    for code in [
        "theorem n4 (a b : Nat) (h : a = b) : a + 0 = b := by rw [h]\n",
        "theorem n5 (xs : List Nat) (h : xs = []) : xs ++ [1] = [1] := by rw [h]\n",
    ] {
        assert!(
            elab_last(code).is_ok(),
            "class (153) closed? Lean refuses this; flip the pin\n{code}"
        );
    }
}
