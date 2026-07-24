// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn zero_add_type(nat: Expr, zero: Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        eq_target(
            nat,
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), zero),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        ),
    )
}

/// Build env with Nat + Eq + Nat.zero_add simp lemma + myVal : Nat.
/// Returns (env, target) where target = `@Eq.{1} Nat (Nat.add Nat.zero myVal) myVal`.
fn setup_simp_zero_add_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.zero_add"),
        level_params: vec![],
        type_: zero_add_type(nat.clone(), zero.clone()),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("myVal"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let my_val = Expr::const_(Name::from_string("myVal"), vec![]);
    let target = eq_target(
        nat,
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), zero),
            my_val.clone(),
        ),
        my_val,
    );
    (env, target)
}

/// Regression test for #2477: `simp` must preserve the proof chain through
/// `elab_by_tactic` when using a simp lemma to rewrite the goal.
///
/// Target: `Nat.add Nat.zero myVal = myVal`
/// Tactic: `by simp`
/// simp applies Nat.zero_add to rewrite LHS, gets `myVal = myVal`, closes with rfl.
/// Exercises the non-def-eq `replace_target_eq` proof-carry path.
#[test]
fn test_elab_by_tactic_simp_rewrite_preserves_proof_chain() {
    let (env, target) = setup_simp_zero_add_env();
    assert_tactic_preserves_target(
        &env,
        target,
        "by simp",
        "simp should elaborate successfully through elab_by_tactic",
        "simp proof should be closed",
        "simp proof type should match the original target after post-hoc verification",
    );
}
