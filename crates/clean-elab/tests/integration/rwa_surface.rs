// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the Lean 4 `rwa [rules] (at loc)?` surface form.
//!
//! `rwa` is a Lean 4 *core* tactic (defined in `Init/Tactics.lean`) as the
//! macro `(rw $rws $(loc)?; assumption)`. It is one of the most common
//! finishing tactics in Lean/Mathlib: rewrite the goal (or a hypothesis) with
//! the given rules, then close the resulting goal by matching a hypothesis.
//!
//! These tests exercise the full parse -> elaborate -> kernel-type-check path:
//! a `theorem ... := by rwa [...]` proof is parsed by `clean-parser` (which
//! desugars `rwa` into a parenthesized `rw [...]; assumption` sequence,
//! mirroring the Lean macro), elaborated by `clean-elab` (the `rw` compound
//! handler builds an `Eq`-congruence proof term; `assumption` closes via a
//! kernel-checked hypothesis reference), and the assembled proof term is
//! type-checked against the stated theorem type by the kernel.
//!
//! Faithfulness/soundness: `rwa` introduces no new proof-construction
//! machinery — every goal is closed only through the existing kernel-checked
//! `rw`/`assumption` effects. A misuse (no rewrite rule applies, or no
//! hypothesis matches the rewritten goal) surfaces as an elaboration error,
//! never a panic.

use super::common::check_and_add_decl;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};

/// Build an environment with `Nat`, `Eq` (and friends), and a unary predicate
/// `P : Nat -> Prop` so we can state rewrite-then-assumption goals.
fn setup_pred_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // P : Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::prop()),
    })
    .expect("add P");

    // Q : Nat -> Prop  (second predicate for the hypothesis-rewrite test)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::arrow(nat, Expr::prop()),
    })
    .expect("add Q");

    env
}

#[test]
fn test_rwa_goal_rewrite_then_assumption_kernel_accepts() {
    // theorem t (a b : Nat) (hab : a = b) (h : P b) : P a := by rwa [hab]
    //
    // `rw [hab]` rewrites the goal `P a` (replacing `a` with `b`) to `P b`,
    // then `assumption` closes `P b` using `h`. The full proof term must
    // kernel-check against `P a`.
    let mut env = setup_pred_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rwa_goal (a b : Nat) (hab : a = b) (h : P b) : P a := by\n  rwa [hab]",
    );
    assert!(
        result.is_ok(),
        "`rwa [hab]` should rewrite `P a` to `P b` and close via `h`, got: {result:?}"
    );
}

#[test]
fn test_rwa_reverse_rule_kernel_accepts() {
    // theorem t (a b : Nat) (hab : a = b) (h : P a) : P b := by rwa [<- hab]
    //
    // The reverse rule rewrites `b` to `a` in the goal `P b`, yielding `P a`,
    // which `assumption` closes via `h`.
    let mut env = setup_pred_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rwa_reverse (a b : Nat) (hab : a = b) (h : P a) : P b := by\n  rwa [<- hab]",
    );
    assert!(
        result.is_ok(),
        "`rwa [<- hab]` should rewrite `P b` to `P a` and close via `h`, got: {result:?}"
    );
}

#[test]
fn test_rwa_no_matching_hypothesis_errors_no_panic() {
    // theorem t (a b : Nat) (hab : a = b) (h : Q b) : P a := by rwa [hab]
    //
    // After `rw [hab]` the goal is `P b`, but the only hypothesis is `Q b`.
    // `assumption` finds no match, so `rwa` must return an elaboration error
    // (NOT close the goal, and NOT panic).
    let mut env = setup_pred_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rwa_no_match (a b : Nat) (hab : a = b) (h : Q b) : P a := by\n  rwa [hab]",
    );
    assert!(
        result.is_err(),
        "`rwa [hab]` with no matching hypothesis must error, got: {result:?}"
    );
}

#[test]
fn test_rwa_no_applicable_rewrite_errors_no_panic() {
    // theorem t (a b c : Nat) (hbc : b = c) (h : P a) : P a := by rwa [hbc]
    //
    // `rw [hbc]` cannot rewrite the goal `P a` (it contains no `b`), so `rw`
    // reports no progress. `rwa` must surface that as an error, not a panic.
    let mut env = setup_pred_env();
    // Need a third Nat parameter `c`; `Nat` is in scope.
    let result = check_and_add_decl(
        &mut env,
        "theorem rwa_no_progress (a b c : Nat) (hbc : b = c) (h : P a) : P a := by\n  rwa [hbc]",
    );
    assert!(
        result.is_err(),
        "`rwa [hbc]` that cannot rewrite the goal must error, got: {result:?}"
    );
}

#[test]
fn test_rwa_direct_assumption_after_trivial_rewrite_kernel_accepts() {
    // theorem t (a b : Nat) (hab : a = b) (h : P b) : P a := by rwa [hab]
    // (variant that also confirms the assembled term is added to the env, so
    // the kernel re-check on `add_decl` succeeds — `check_and_add_decl`
    // type-checks the proof before registration.)
    //
    // Additionally state a curried predicate over two args to make sure the
    // congruence/rewrite path generalizes beyond the unary head.
    let mut env = setup_pred_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // R : Nat -> Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat.clone(),
            Expr::arrow(nat, Expr::prop()),
        ),
    })
    .expect("add R");

    let result = check_and_add_decl(
        &mut env,
        "theorem rwa_binary (a b c : Nat) (hab : a = b) (h : R b c) : R a c := by\n  rwa [hab]",
    );
    assert!(
        result.is_ok(),
        "`rwa [hab]` should rewrite `R a c` to `R b c` and close via `h`, got: {result:?}"
    );
}
