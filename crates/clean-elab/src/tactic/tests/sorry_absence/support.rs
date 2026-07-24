// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Build a `ProofState` for `x <= z` with `h1: x <= y, h2: y <= z`.
pub(super) fn setup_linarith_transitivity() -> ProofState {
    // Use with_prelude() so Nat ordering lemmas (Nat.le_trans, Nat.add_le_add,
    // Nat.mul_le_mul_left) are available for build_linarith_proof (#2124).
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let x = FVarId::new(0);
    let y = FVarId::new(1);
    let z = FVarId::new(2);

    // Use make_nat_le_tc (correct @LE.le.{0} Nat instLENat form) instead of
    // make_nat_le (wrong Nat-as-instance placeholder). close_goal
    // rejects proofs with the wrong LE instance (#2130, Part of #1144).
    let h1_ty = make_nat_le_tc(Expr::fvar(x), Expr::fvar(y));
    let h2_ty = make_nat_le_tc(Expr::fvar(y), Expr::fvar(z));
    let goal_ty = make_nat_le_tc(Expr::fvar(x), Expr::fvar(z));

    ProofState::with_context(
        env,
        goal_ty,
        vec![
            LocalDecl {
                fvar: x,
                name: "x".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y,
                name: "y".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: z,
                name: "z".into(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(3),
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(4),
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    )
}

/// Assert all three counters are zero on tactic failure (error or panic).
/// Used by sorry-absence tests where the tactic did not succeed.
pub(super) fn assert_all_counters_zero_on_failure(
    tactic: &str,
    outcome: &str,
    sorry_used: u64,
    arith_used: u64,
    ay_used: u64,
) {
    assert_eq!(
        sorry_used, 0,
        "{tactic} {outcome} AND used {sorry_used} sorry terms"
    );
    assert_eq!(
        arith_used, 0,
        "{tactic} {outcome} AND used {arith_used} trustedArith terms"
    );
    assert_eq!(
        ay_used, 0,
        "{tactic} {outcome} AND used {ay_used} trustedAy terms"
    );
}

/// Build env with Nat, Eq, and a simp lemma: `Nat.add Nat.one Nat.one = Nat.two`.
/// Returns `(env, goal)` where goal is `Eq Nat (Nat.add 1 1) 2`.
pub(super) fn setup_env_with_simp_add_lemma() -> (Environment, Expr) {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let one_name = Name::from_string("Nat.one");
    if env.get_const(&one_name).is_none() {
        env.add_decl(Declaration::Axiom {
            name: one_name.clone(),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    let one = Expr::const_(one_name, vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.two"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();
    let two = Expr::const_(Name::from_string("Nat.two"), vec![]);

    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            one.clone(),
        ),
        one,
    );
    let eq_type = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let lemma_type = Expr::app(
        Expr::app(Expr::app(eq_type.clone(), nat.clone()), lhs.clone()),
        two.clone(),
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_add_lemma"),
        level_params: vec![],
        type_: lemma_type,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("my_add_lemma"), SimpPriority::Default);

    let goal = Expr::app(Expr::app(Expr::app(eq_type, nat), lhs), two);
    (env, goal)
}
