// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The identity strategy for `P → Q` must compare `P` and `Q` at the SAME
//! binder depth (decide review probe a07, 2026-09-28).
//!
//! `LogicalForm::Implies(p, q)` hands back the arrow's codomain `q` unlowered,
//! one binder deeper than `p`. Under a `∀` the propositional reconstruction
//! works on the OPEN body, so both carry loose bound variables, and comparing
//! them raw matched `b = true` (outside the arrow: `b` = #1) against
//! `c = true` (inside it: `c` = #1). For the FALSE goal
//! `∀ b c : Bool, b = true → c = true` the bridge answered `Verified` with
//! `fun b c h => h : ∀ b c : Bool, b = true → b = true`, which only the
//! kernel check downstream rejected.

use super::super::*;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, Level, TypeChecker};

fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

/// `x = true` at `Bool`.
fn eq_true(x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            bool_ty(),
            x,
            Expr::const_(Name::from_string("Bool.true"), vec![]),
        ],
    )
}

/// `∀ b c : Bool, b = true → <consequent>`, the consequent built INSIDE the
/// arrow (there `h` = #0, `c` = #1, `b` = #2).
fn forall_b_c_b_true_implies(consequent: Expr) -> Expr {
    let arrow = Expr::pi(BinderInfo::Default, eq_true(Expr::bvar(1)), consequent);
    Expr::pi(
        BinderInfo::Default,
        bool_ty(),
        Expr::pi(BinderInfo::Default, bool_ty(), arrow),
    )
}

fn kernel_accepts(env: &Environment, proof: &Expr, goal: &Expr) -> bool {
    TypeChecker::new(env).check_type(proof, goal).is_ok()
}

#[test]
fn a07_false_goal_is_never_verified() {
    let env = Environment::with_prelude();
    // ∀ b c : Bool, b = true → c = true     (false: b := true, c := false)
    let goal = forall_b_c_b_true_implies(eq_true(Expr::bvar(1)));
    let mut bridge = SmtBridge::new(&env);
    if let Ok(SmtVerificationResult::Verified(proof)) = bridge.prove(&goal) {
        panic!(
            "SOUNDNESS: the bridge 'verified' a false goal with `{}` (kernel accepts it: {})",
            proof.proof_term(),
            kernel_accepts(&env, proof.proof_term(), &goal)
        );
    }
}

#[test]
fn a07_control_the_true_identity_goal_still_verifies_with_a_checked_term() {
    let env = Environment::with_prelude();
    // ∀ b c : Bool, b = true → b = true     (true: the identity)
    let goal = forall_b_c_b_true_implies(eq_true(Expr::bvar(2)));
    let mut bridge = SmtBridge::new(&env);
    match bridge.prove(&goal) {
        Ok(SmtVerificationResult::Verified(proof)) => assert!(
            kernel_accepts(&env, proof.proof_term(), &goal),
            "a Verified term must kernel-check: `{}`",
            proof.proof_term()
        ),
        other => panic!("the identity implication must still be proved, got {other:?}"),
    }
}
