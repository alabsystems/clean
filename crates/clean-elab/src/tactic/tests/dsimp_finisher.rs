// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `dsimp` must CLOSE a goal its own definitional normalization made
//! self-evident.
//!
//! `dsimp_with_config` reduced the target correctly (`replace_target_def_eq`)
//! and then returned `Ok(())` with the goal still open, so every
//! dsimp-as-finisher proof reported unsolved goals. Measured on the release
//! binary before the fix: **0 of 7** representative goals closed — including
//! `((fun x : Nat => x) 5) = 5`, whose target is already SYNTACTICALLY
//! reflexive by the time `dsimp` abandons it:
//!
//! ```text
//! ✗ d01: TacticFailed(UnsolvedGoals { count: 1, detail:
//!     "⊢ Eq Nat (OfNat.ofNat Nat 5 (instOfNatNat 5))
//!               (OfNat.ofNat Nat 5 (instOfNatNat 5))" })
//! ```
//!
//! The reduction engine was already right; only the last step was missing.
//! The fix reuses simp's own closer pair through
//! `simp::try_definitional_closers` — reflexivity at REDUCIBLE transparency
//! plus `⊢ True` — and deliberately not simp's `assumption` /
//! constructor-disequality closers, which Lean's `dsimp` does not have.

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

#[track_caller]
fn assert_not_closed(code: &str, what: &str) {
    let results = elab_all(code);
    assert!(
        results.iter().any(|r| r.is_err()),
        "{what}: dsimp closed a goal it must leave open. Got {results:?}"
    );
}

/// Beta, zeta and nested-beta reduction each leave a syntactically reflexive
/// `Eq`. These are the `p_dsimp_01/02/06/10` shapes.
#[test]
fn test_dsimp_closes_a_goal_reduction_made_reflexive() {
    assert_closed(
        "theorem dsBeta : ((fun x : Nat => x) 5) = 5 := by dsimp\n",
        "dsimp beta → 5 = 5",
    );
    assert_closed(
        "theorem dsBetaOpen (n : Nat) : (fun x : Nat => x + 0) n = n + 0 := by dsimp\n",
        "dsimp beta under a variable",
    );
    assert_closed(
        "theorem dsZeta (n : Nat) : (let m := n; m + 0) = n + 0 := by dsimp\n",
        "dsimp zeta → n + 0 = n + 0",
    );
    assert_closed(
        "theorem dsBetaNested (n : Nat) : (fun x : Nat => (fun y : Nat => x + y)) 2 3 = 2 + 3 := by dsimp\n",
        "dsimp nested beta",
    );
}

/// The closer is `close_refl_reducible`, not a syntactic equality test, so it
/// also sees through the `instOfNatNat` / `instHAddNat` instance layer down to
/// the kernel's Nat literal arithmetic (`p_dsimp_05/08`) and through
/// `Proj`-of-`Prod.mk` (`p_dsimp_09`) — cases where `dsimp_expr` itself leaves
/// the target un-reduced.
#[test]
fn test_dsimp_closes_through_reducible_transparency() {
    assert_closed(
        "theorem dsGroundAdd : ((fun (a b : Nat) => a + b) 2 3) = 5 := by dsimp\n",
        "dsimp ground arithmetic after beta",
    );
    assert_closed(
        "theorem dsGroundAdd2 : (2 : Nat) + 3 = 5 := by dsimp\n",
        "dsimp ground arithmetic, no reduction step at all",
    );
    assert_closed(
        "theorem dsProj (n : Nat) : (n, 3).1 = n := by dsimp\n",
        "dsimp projection of a constructor",
    );
}

/// Negative control 1: `dsimp` must not close a goal that is TRUE but not
/// definitionally so. `a + b = b + a` needs `Nat.add_comm`, a propositional
/// rewrite; a finisher that closed it would mean the gate is not the
/// definitional one.
#[test]
fn test_dsimp_leaves_a_non_definitional_goal_open() {
    assert_not_closed(
        "theorem dsComm (a b : Nat) : a + b = b + a := by dsimp\n",
        "dsimp on commutativity",
    );
}

/// Negative control 2: `dsimp` must not close by ASSUMPTION. Lean's `dsimp`
/// has no assumption closer, and reusing simp's full `try_simp_closers` here
/// would have added one — silently making Clean's `dsimp` stronger than the
/// tactic it is replacing.
#[test]
fn test_dsimp_does_not_close_by_assumption() {
    assert_not_closed(
        "theorem dsAssumption (p : Prop) (h : p) : p := by dsimp\n",
        "dsimp with a matching hypothesis in scope",
    );
}
