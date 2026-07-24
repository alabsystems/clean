// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn nat_zero_target(lhs: Expr, rhs: Expr) -> Expr {
    eq_target(Expr::const_(Name::from_string("Nat"), vec![]), lhs, rhs)
}

/// Regression test for #2477: `unfold` must preserve the proof chain through
/// `elab_by_tactic` when unfolding a definition in the goal target.
///
/// Registers `myConst : Nat := Nat.zero`, then:
/// Target: `myConst = Nat.zero`
/// Tactic: `by unfold myConst; rfl`
/// unfold replaces `myConst` with its definition, then rfl closes.
/// Exercises the `replace_target_def_eq` path through unfold in the full pipeline.
#[test]
fn test_elab_by_tactic_unfold_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    env.add_decl(Declaration::Definition {
        name: Name::from_string("myConst"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
        value: zero.clone(),
        is_reducible: true,
    })
    .unwrap();

    let my_const = Expr::const_(Name::from_string("myConst"), vec![]);
    let target = nat_zero_target(my_const, zero.clone());

    assert_tactic_preserves_target(
        &env,
        target,
        "by unfold myConst; rfl",
        "unfold followed by rfl should elaborate successfully through elab_by_tactic",
        "unfold proof should be closed",
        "unfold proof type should match the original target after post-hoc verification",
    );
}

/// Regression test for #2477: chained goal transformations (unfold → dsimp → rfl)
/// must compose through the proof chain without losing MetaId(0) connectivity.
///
/// Registers `myId : Nat := (fun x : Nat => x) Nat.zero`, then:
/// Target: `myId = Nat.zero`
/// Tactic: `by unfold myId; dsimp; rfl`
/// unfold replaces `myId` with `(fun x => x) Nat.zero`, dsimp beta-reduces,
/// rfl closes. Two chained `replace_target_def_eq` calls must compose.
#[test]
fn test_elab_by_tactic_chained_unfold_dsimp_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let id_applied = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::bvar(0),
        ),
        zero.clone(),
    );

    env.add_decl(Declaration::Definition {
        name: Name::from_string("myId"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
        value: id_applied,
        is_reducible: true,
    })
    .unwrap();

    let my_id = Expr::const_(Name::from_string("myId"), vec![]);
    let target = nat_zero_target(my_id, zero.clone());

    assert_tactic_preserves_target(
        &env,
        target,
        "by unfold myId; dsimp; rfl",
        "chained unfold + dsimp + rfl should elaborate successfully through elab_by_tactic",
        "chained unfold+dsimp proof should be closed",
        "chained unfold+dsimp proof type should match original target",
    );
}

/// Regression test for #2477: `push_neg` must preserve the proof chain through
/// `elab_by_tactic` when transforming a double-negation target.
///
/// Target: ¬¬P (which is (P → False) → False)
/// Tactic: `by push_neg; exact p`
/// push_neg eliminates the double negation via an explicit `replace_target_eq`
/// proof, then `exact p` closes the simplified goal P.
/// Exercises the checked proof-carry path through the full elaboration pipeline.
#[test]
fn test_elab_by_tactic_push_neg_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_iff().unwrap();
    env.init_classical().unwrap();
    env.init_propext().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: prop_p.clone(),
    })
    .unwrap();

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let not_p = Expr::arrow(prop_p.clone(), false_const.clone());
    let not_not_p = Expr::arrow(not_p, false_const);

    assert_tactic_preserves_target(
        &env,
        not_not_p,
        "by push_neg; exact p",
        "push_neg followed by exact p should elaborate successfully through elab_by_tactic",
        "push_neg proof should be closed",
        "push_neg proof type should match the original target ¬¬P after post-hoc verification",
    );
}
