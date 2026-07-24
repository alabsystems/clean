// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::decide as smt_decide;
use super::*;
use clean_kernel::Declaration;

// ============================================================================
// decide() error variant tests (Part of #2442)
// ============================================================================

/// Verify that `decide` returns `SmtFailed` (not a panic or other error
/// variant) when the goal is provably false. This exercises the `Refuted`
/// or `Unknown` branch in the match on `bridge.prove()`.
#[test]
fn test_decide_returns_smt_failed_on_false_goal() {
    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let a_ty = Expr::type_();

    use clean_kernel::level::Level;
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a,
        ),
        b,
    );

    let mut state = ProofState::new(env, target);
    let err = smt_decide::decide(&mut state).expect_err("decide should fail on an unprovable goal");
    assert!(
        matches!(&err, crate::tactic::TacticError::SmtFailed { tactic, .. } if tactic == "decide"),
        "expected SmtFailed error from decide on an unprovable goal, got: {err:?}"
    );
    assert!(
        !state.is_complete(),
        "state should not be complete after decide failure"
    );
}

/// Verify that `decide` does not increment the trusted axiom counter when
/// it successfully proves a goal via kernel-validated proof reconstruction.
/// This is the positive soundness check: verified proofs carry zero trust debt.
#[test]
fn test_decide_verified_path_has_zero_trusted_axiom_count() {
    let mut env = Environment::new();
    env.init_eq().expect("Eq should initialize");

    // Add type A and constant a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A should register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .expect("a should register");

    use clean_kernel::level::Level;
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let mut state = ProofState::new(env, target);
    let result = smt_decide::decide(&mut state);
    assert!(result.is_ok(), "decide should prove a = a");
    assert!(state.is_complete(), "goal should be closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "reflexivity proof should not use any trusted axioms"
    );
}
