// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for `gcongr`'s trivial side-goal discharger (RC-N).
//!
//! `gcongr` decomposed `a + 1 ≤ b + 1` into `a ≤ b` and `1 ≤ 1` and then
//! stopped, leaving BOTH goals open even when `h : a ≤ b` was already in
//! context — so the tactic never closed anything by itself. Lean's `gcongr`
//! sends its main subgoals to a `gcongr_assumption` step and its side goals to
//! `gcongr_discharger`; these tests pin the trivial subset implemented here:
//! `assumption` and reflexivity.

use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr};

use super::core::ProofState;
use super::gcongr::{gcongr, match_inequality};
use super::proof_term::intro;
use super::tc_app;

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_add(x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(nat_const("Nat.add"), x), y)
}

/// Prelude env with `a`, `b`, `c` declared as `Nat` axioms.
fn nat_env_with_abc() -> Environment {
    let mut env = Environment::with_prelude();
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_ty(),
        })
        .expect("declare Nat axiom");
    }
    env
}

/// The plan's probe: `a + 1 ≤ b + 1` with `h : a ≤ b` in context must be CLOSED,
/// not left as two open subgoals. `a ≤ b` goes to `assumption`, `1 ≤ 1` to the
/// `Nat.le_refl` rung.
#[test]
fn test_gcongr_discharges_assumption_and_refl_subgoals() {
    let env = nat_env_with_abc();
    let one = Expr::app(nat_const("Nat.succ"), nat_const("Nat.zero"));
    let conclusion = tc_app::nat_le_tc(
        nat_add(nat_const("a"), one.clone()),
        nat_add(nat_const("b"), one),
    );
    let hyp = tc_app::nat_le_tc(nat_const("a"), nat_const("b"));
    let mut state = ProofState::new(env, Expr::arrow(hyp, conclusion));
    intro(&mut state, "h").expect("intro h");

    gcongr(&mut state).expect("gcongr should decompose a + 1 ≤ b + 1");
    assert!(
        state.goals().is_empty(),
        "gcongr must discharge its own subgoals (`a ≤ b` by assumption, `1 ≤ 1` by \
         Nat.le_refl); {} left: {:?}",
        state.goals().len(),
        state.goals()
    );
}

/// Same shape with a shared symbolic operand: `a + c ≤ b + c` from `h : a ≤ b`.
#[test]
fn test_gcongr_discharges_shared_operand_subgoal() {
    let env = nat_env_with_abc();
    let conclusion = tc_app::nat_le_tc(
        nat_add(nat_const("a"), nat_const("c")),
        nat_add(nat_const("b"), nat_const("c")),
    );
    let hyp = tc_app::nat_le_tc(nat_const("a"), nat_const("b"));
    let mut state = ProofState::new(env, Expr::arrow(hyp, conclusion));
    intro(&mut state, "h").expect("intro h");

    gcongr(&mut state).expect("gcongr should decompose a + c ≤ b + c");
    assert!(
        state.goals().is_empty(),
        "`a ≤ b` (assumption) and `c ≤ c` (refl) are both trivial; {} left: {:?}",
        state.goals().len(),
        state.goals()
    );
}

/// A subgoal the trivial rungs cannot reach must be LEFT OPEN — the discharger
/// never closes a goal without a checked proof term. `a + c ≤ b + c` with no
/// usable hypothesis keeps `a ≤ b` and discharges only the reflexive `c ≤ c`.
#[test]
fn test_gcongr_leaves_undischargeable_subgoal_open() {
    let env = nat_env_with_abc();
    let target = tc_app::nat_le_tc(
        nat_add(nat_const("a"), nat_const("c")),
        nat_add(nat_const("b"), nat_const("c")),
    );
    let mut state = ProofState::new(env, target);

    gcongr(&mut state).expect("gcongr should decompose a + c ≤ b + c");
    assert_eq!(
        state.goals().len(),
        1,
        "only the reflexive `c ≤ c` subgoal is dischargeable here, got {:?}",
        state.goals()
    );
    let (_, _, _, lhs, rhs) = match_inequality(&state.goals()[0].target)
        .expect("the surviving subgoal is still an inequality");
    assert_eq!(lhs, nat_const("a"), "surviving subgoal should be `a ≤ b`");
    assert_eq!(rhs, nat_const("b"), "surviving subgoal should be `a ≤ b`");
}
