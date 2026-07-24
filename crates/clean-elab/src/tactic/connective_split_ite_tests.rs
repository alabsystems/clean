// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `split` on a goal containing an `if-then-else`.
//!
//! Lean 4's `split` case-splits a goal that CONTAINS `if c then a else b` on
//! the condition's `Decidable` instance, producing two goals with the `ite`
//! definitionally reduced (`a` under `isTrue h`, `b` under `isFalse h`). These
//! tests confirm:
//! - `split` finds the `ite` (whether nested inside `Eq` or the whole target)
//!   and produces two subgoals with the reduced branch values,
//! - the assembled `Decidable.casesOn` proof term is accepted by the KERNEL,
//! - a genuinely-false branch is NOT over-accepted (fail-closed),
//! - misuse (no `ite`/`And`/`Iff`) errors rather than panics.
//!
//! The environment is built with `Decidable` / `ite` / `Eq` and an abstract
//! `Decidable`-decided proposition `C` (instance `instC : Decidable C`), so the
//! `ite`'s instance is symbolic — it cannot ι-reduce on its own, exactly
//! exercising the `Decidable.casesOn` split path (not a whnf shortcut).

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, Level, TypeChecker};

use super::core::{ProofState, TacticError};
use super::proof_term::exact;
use super::split_;

/// Prelude environment plus:
/// - `C : Prop` and an instance `instC : Decidable C`,
/// - `T : Type` with values `a b : T`.
fn setup_env() -> Environment {
    let mut env = Environment::with_prelude();

    let prop = Expr::prop();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("C"),
        level_params: vec![],
        type_: prop,
    })
    .expect("add C : Prop");

    // instC : Decidable C
    let decidable_c = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        Expr::const_(Name::from_string("C"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("instC"),
        level_params: vec![],
        type_: decidable_c,
    })
    .expect("add instC : Decidable C");

    // T : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add T : Type");

    // a b : T
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("T"), vec![]),
        })
        .expect("add value : T");
    }

    env
}

fn c_const() -> Expr {
    Expr::const_(Name::from_string("C"), vec![])
}
fn t_const() -> Expr {
    Expr::const_(Name::from_string("T"), vec![])
}
fn val(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@ite.{1} T C instC then_val else_val` — `T : Type` lives in `Sort 1`.
fn ite_t(then_val: Expr, else_val: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [t_const(), c_const(), val("instC"), then_val, else_val],
    )
}

/// `@Eq.{1} T lhs rhs`.
fn eq_t(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [t_const(), lhs, rhs],
    )
}

/// `@Eq.refl.{1} T x`.
fn eq_refl_t(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [t_const(), x],
    )
}

/// Tooth 1/3 analog: `(if C then a else a) = a`. `split` yields two goals,
/// both of which reduce to `a = a`. Closing each with `Eq.refl a` gives a
/// complete proof, and the KERNEL accepts the assembled `Decidable.casesOn`
/// proof term against the original `ite` goal.
#[test]
fn test_split_ite_both_branches_equal_kernel_accepts() {
    let env = setup_env();
    // Goal: @Eq T (@ite T C instC a a) a
    let target = eq_t(ite_t(val("a"), val("a")), val("a"));
    let mut state = ProofState::new(env.clone(), target.clone());

    split_(&mut state).expect("split should case-split on the ite's Decidable instance");

    // Two subgoals: true/`c` case first, then false/`¬c` case.
    assert_eq!(state.goals().len(), 2, "split should produce two subgoals");
    // Both reduced targets are `a = a`.
    let expected = eq_t(val("a"), val("a"));
    assert_eq!(
        state.goals()[0].target,
        expected,
        "true-branch target should be the reduced `a = a`"
    );
    assert_eq!(
        state.goals()[1].target,
        expected,
        "false-branch target should be the reduced `a = a`"
    );
    // Each branch carries the condition hypothesis `h`.
    assert!(
        state.goals()[0]
            .local_ctx
            .iter()
            .any(|d| d.name == "h" && d.ty == c_const()),
        "true branch must have `h : C`"
    );

    // Close both with `Eq.refl a`.
    exact(&mut state, eq_refl_t(val("a"))).expect("Eq.refl a closes the true branch");
    exact(&mut state, eq_refl_t(val("a"))).expect("Eq.refl a closes the false branch");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the Decidable.casesOn proof term for the ite goal");
}

/// Tooth 2 analog (self-referential ite): `(if C then a else b) = (if C then a
/// else b)`. Each branch reduces both sides identically, so both close by
/// reflexivity, and the kernel accepts the assembled term.
#[test]
fn test_split_ite_reflexive_goal_kernel_accepts() {
    let env = setup_env();
    let ite = ite_t(val("a"), val("b"));
    // Goal: @Eq T (@ite T C instC a b) (@ite T C instC a b)
    let target = eq_t(ite.clone(), ite.clone());
    let mut state = ProofState::new(env.clone(), target.clone());

    split_(&mut state).expect("split should case-split the reflexive ite goal");
    assert_eq!(state.goals().len(), 2, "split should produce two subgoals");
    // True branch: both sides became `a` → `a = a`. False branch: `b = b`.
    assert_eq!(state.goals()[0].target, eq_t(val("a"), val("a")));
    assert_eq!(state.goals()[1].target, eq_t(val("b"), val("b")));

    exact(&mut state, eq_refl_t(val("a"))).expect("Eq.refl a closes the true branch");
    exact(&mut state, eq_refl_t(val("b"))).expect("Eq.refl b closes the false branch");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the Decidable.casesOn proof term");
}

/// Tooth 4 analog: the `ite` is the WHOLE goal (a Prop), not nested inside an
/// `Eq`. `(if C then True else True)`. `split` must still find the top-level
/// `ite` (WHNF would delta-unfold it into `Decidable.casesOn` and hide it).
#[test]
fn test_split_ite_top_level_prop_goal_kernel_accepts() {
    let env = setup_env();
    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    // Goal: @ite.{1} Prop C instC True True — Prop lives in Sort 1.
    let target = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            Expr::prop(),
            c_const(),
            val("instC"),
            true_c.clone(),
            true_c.clone(),
        ],
    );
    let mut state = ProofState::new(env.clone(), target.clone());

    split_(&mut state).expect("split should find the top-level ite and case-split");
    assert_eq!(state.goals().len(), 2, "split should produce two subgoals");
    // Both branches reduce to `True`.
    assert_eq!(state.goals()[0].target, true_c);
    assert_eq!(state.goals()[1].target, true_c);

    exact(&mut state, true_intro.clone()).expect("True.intro closes the true branch");
    exact(&mut state, true_intro).expect("True.intro closes the false branch");

    assert!(state.is_complete(), "proof should be complete");
    let proof = state
        .closed_proof()
        .expect("closed proof term should exist");
    let tc = TypeChecker::new(&env);
    tc.check_type(&proof, &target)
        .expect("kernel must accept the Decidable.casesOn proof term for the Prop ite goal");
}

/// Negative tooth: `(if C then a else b) = a`. `split` succeeds, but the
/// FALSE/`¬c` branch goal is `b = a`, which is genuinely false. Closing it
/// with `Eq.refl a` (the "obvious" but wrong witness) MUST be rejected by the
/// type checker — the split does not over-accept an unprovable branch.
#[test]
fn test_split_ite_false_branch_not_over_accepted() {
    let env = setup_env();
    // Goal: @Eq T (@ite T C instC a b) a
    let target = eq_t(ite_t(val("a"), val("b")), val("a"));
    let mut state = ProofState::new(env, target);

    split_(&mut state).expect("split should case-split even when a branch is false");
    assert_eq!(state.goals().len(), 2, "split should produce two subgoals");
    // True branch: `a = a` (provable). False branch: `b = a` (NOT provable).
    assert_eq!(state.goals()[0].target, eq_t(val("a"), val("a")));
    assert_eq!(state.goals()[1].target, eq_t(val("b"), val("a")));

    // True branch closes fine.
    exact(&mut state, eq_refl_t(val("a"))).expect("Eq.refl a closes the true branch");

    // False branch: `Eq.refl a : a = a` does NOT have type `b = a`. The checked
    // `exact` must reject it (type mismatch / unification failure), never panic
    // and never silently accept.
    let err = exact(&mut state, eq_refl_t(val("a")))
        .expect_err("wrong witness for `b = a` must be rejected");
    assert!(
        matches!(
            err,
            TacticError::TypeMismatch { .. } | TacticError::UnificationFailed(_)
        ),
        "false-branch over-close should be a type/unification error, got: {err:?}"
    );
}

/// `split` on a goal with no `And`/`Iff`/`ite` must error (fail-closed), not
/// panic.
#[test]
fn test_split_no_and_iff_ite_errors_not_panics() {
    let env = setup_env();
    // Goal: `@Eq T a a` — no And, Iff, or ite anywhere.
    let target = eq_t(val("a"), val("a"));
    let mut state = ProofState::new(env, target);

    let err = split_(&mut state).expect_err("split with no And/Iff/ite must error");
    assert!(
        matches!(err, TacticError::GoalMismatch(_)),
        "split on a non-And/Iff/ite goal should be a GoalMismatch, got: {err:?}"
    );
}
