// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `interval_cases` descent guard-rails (#2533): the environment gate, the
//! binder-slot allocation contract, the `Nat.lt ≡ Nat.le ∘ succ` defeq the
//! descent rests on, and the documented range/endpoint caps.
//!
//! Companion to `interval_cases_descent.rs`, which owns the fixtures and the
//! "branches consume `n_eq`" proof tests. Split for the 500-line file rule.

use super::finite_cases_proof_chain::setup_env_for_interval_cases;
use super::interval_cases_descent::{
    interval_state, make_nat_lt_tc, setup_env_for_interval_cases_ordered, sname,
};
use super::*;

/// Without Nat order theory the descent cannot be built, so the tactic must
/// fail closed with a typed `EnvironmentMissing` — not a scope error, and
/// certainly not a silent success. Also pins that the env gate runs AFTER the
/// bound/range checks, so the error-path tests keep their exact messages.
#[test]
fn test_interval_cases_disengages_without_order_lemmas() {
    let env = setup_env_for_interval_cases();
    let (mut state, _target) = interval_state(env, 2, 4);

    let err = interval_cases(&mut state, &sname("n"))
        .expect_err("a thin env without Nat order lemmas must not produce a proof");
    match &err {
        TacticError::EnvironmentMissing { constant } => {
            assert!(
                constant.starts_with("Nat."),
                "should name the missing Nat order lemma, got: {constant}"
            );
        }
        other => panic!("expected EnvironmentMissing, got: {other:?}"),
    }
    assert_eq!(
        state.goals.len(),
        1,
        "a disengaged interval_cases must leave the state untouched"
    );
}

/// The descent stacks one binder per value, outermost at the LARGEST value, so
/// sub-goal contexts are deliberately NON-CONTIGUOUS (`{0,1,2,4}` for the
/// middle branch). `goal_binder_base` — the capture-safe authority every
/// goal-derived mint (`intro` included) reads — and the context-only
/// `goal_fvar_base` both take the max, not the count, so the next `intro` on
/// that branch still lands one slot past its own binder.
#[test]
fn test_interval_cases_branch_intro_allocates_next_slot() {
    let env = setup_env_for_interval_cases_ordered();
    let (mut state, _target) = interval_state(env, 2, 4);

    interval_cases(&mut state, &sname("n")).expect("interval_cases 2 ≤ n ≤ 4 should succeed");

    // Goals are in ascending value order: 2, 3, 4.
    // Binder nesting position j = count-1-k, and id = goal_binder_base + j,
    // where the root goal's base is fvar_base = 3 (elab locals 0..=2).
    let expected_ids = [5u64, 4, 3];
    for (idx, goal) in state.goals.iter().enumerate() {
        let n_eq = goal
            .local_ctx
            .iter()
            .find(|d| d.name == sname("n_eq"))
            .expect("branch should carry n_eq");
        assert_eq!(
            n_eq.fvar.as_u64(),
            expected_ids[idx],
            "branch {idx} n_eq must sit at its binder nesting position"
        );
        assert_eq!(
            state.goal_fvar_base(goal),
            expected_ids[idx] + 1,
            "branch {idx}'s next intro must take the slot after its own binder"
        );
        assert_eq!(
            state.goal_binder_base(goal),
            expected_ids[idx] + 1,
            "branch {idx}'s capture-safe binder base must agree: nothing narrowed"
        );
    }
}

/// Canary for the `Nat.lt ≡ Nat.le ∘ succ` reducibility the descent depends on.
///
/// If a future kernel change makes `Nat.lt` (or `instLTNat`/`LT.lt`) opaque,
/// this fails in one line instead of a 100-node term dump from
/// `interval_cases`.
#[test]
fn test_interval_cases_defeq_canary_lt_is_le_succ() {
    let env = setup_env_for_interval_cases_ordered();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::fvar(FVarId::new(0));

    // (a) `Nat.lt_irrefl n (Nat.le_trans (succ n) 2 n hlt h_lower) : False`
    //     with `hlt : n < 2` fed to a slot expecting `Nat.le (succ n) 2`.
    let mut state = ProofState::with_elab_context(
        env.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: sname("n"),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: sname("h_lower"),
                ty: make_nat_le_tc(make_nat_literal(2), n.clone()),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(2),
                name: sname("hlt"),
                ty: make_nat_lt_tc(n.clone(), make_nat_literal(2)),
                value: None,
            },
        ],
    );
    let goal = state.current_goal().cloned().expect("goal");
    let le_succ_n_n = Expr::apps(
        Expr::const_(Name::from_string("Nat.le_trans"), vec![]),
        [
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                n.clone(),
            ),
            make_nat_literal(2),
            n.clone(),
            Expr::fvar(FVarId::new(2)),
            Expr::fvar(FVarId::new(1)),
        ],
    );
    let false_pf = Expr::apps(
        Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
        [n.clone(), le_succ_n_n],
    );
    let _ = state
        .verify_proof(&goal, &false_pf)
        .expect("`n < lo` with `lo ≤ n` must close via Nat.le_trans + Nat.lt_irrefl");

    // (b) `Nat.le_of_succ_le_succ n 3 hlt4 : n ≤ 3` with `hlt4 : n < 4`,
    //     relying on `lit(4) ≡ Nat.succ lit(3)` syntactically.
    let mut state2 = ProofState::with_elab_context(
        env,
        make_nat_le_tc(n.clone(), make_nat_literal(3)),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: sname("n"),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: sname("hlt4"),
                ty: make_nat_lt_tc(n.clone(), make_nat_literal(4)),
                value: None,
            },
        ],
    );
    let goal2 = state2.current_goal().cloned().expect("goal");
    let peeled = Expr::apps(
        Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
        [n, make_nat_literal(3), Expr::fvar(FVarId::new(1))],
    );
    let _ = state2
        .verify_proof(&goal2, &peeled)
        .expect("`n < k+1` must peel to `n ≤ k` with no conversion lemma");
}

/// The documented 100-value cap is built and closed for real, and the endpoint
/// gate cannot drift.
#[test]
fn test_interval_cases_full_range_kernel_checks() {
    let env = setup_env_for_interval_cases_ordered();
    let (mut state, _target) = interval_state(env.clone(), 0, 100);
    interval_cases(&mut state, &sname("n")).expect("the documented 100-value cap must build");
    assert_eq!(state.goals.len(), 101);
    for (idx, goal) in state.goals.iter().enumerate() {
        assert!(
            goal.local_ctx.iter().any(|d| d.name == sname("n_eq")),
            "branch {idx} must carry n_eq"
        );
    }

    // Endpoint gate: 1025 is past MAX_ENDPOINT and must be refused, with a
    // message distinct from the range cap.
    let (mut too_big, _t) = interval_state(env, 1025, 1025);
    let err = interval_cases(&mut too_big, &sname("n"))
        .expect_err("an endpoint past the literal cap must be refused");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("exceeds the literal cap"),
        "endpoint gate should name the literal cap, got: {msg}"
    );
}
