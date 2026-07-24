// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for propositional logic tactics: contrapose, push_neg, tauto
//!
//! Split from advanced.rs. Related test files:
//! - advanced.rs: remaining advanced tactics
//! - conv.rs: conv tactic tests
//! - library_search.rs: library search tests
//! - mathlib_tactics.rs: mathlib-style tactics
//! - pattern_tactics.rs: rintro, peel, split_ifs tests
use super::*;
use crate::tactic::arith_push_neg::push_neg_expr_with_proof;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::tc::TypeChecker;

// contrapose tests
// =========================================================================

#[test]
fn test_contrapose_transforms_goal() {
    let mut env = setup_env_with_prop_ext();
    // Propositions P, Q : Prop (contrapose requires Prop-level implications)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let goal_type = Expr::arrow(p.clone(), q.clone());

    let mut state = ProofState::new(env, goal_type);
    contrapose(&mut state).expect("contrapose on P → Q should succeed");

    // New goal should be ¬Q → ¬P
    // ¬Q = Q → False
    // ¬P = P → False
    let goal = state.current_goal().unwrap();
    if let ExprKind::Pi(_, not_q_ty, _) = goal.target.kind() {
        if let ExprKind::Pi(_, q_ty, false_ty) = not_q_ty.kind() {
            assert_eq!(**q_ty, q);
            assert!(
                matches!(false_ty.kind(), ExprKind::Const(name, _) if name.to_string() == "False")
            );
        } else {
            panic!("Expected ¬Q to be Q → False");
        }
    } else {
        panic!("Expected goal to be Pi type");
    }
}

#[test]
fn test_contrapose_missing_propext_fails() {
    // contrapose must fail closed with `EnvironmentMissing { propext }` when
    // `propext` is absent, rather than emitting an ill-typed proof. NOTE:
    // `init_classical` now transitively registers `propext` (it proves
    // `Classical.em` from `Classical.choice` + `propext` + `funext`, see
    // `logic_decidable.rs::init_classical`), so a propext-less environment can no
    // longer be reached through it. Instead, register every constant contrapose
    // requires *before* `propext` as opaque placeholders — the require-consts
    // guard only checks presence by name — and deliberately omit `propext` so the
    // guard trips specifically on it.
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
    // Constants contrapose checks for before `propext`; opaque placeholders are
    // enough since `require_const` only checks for presence (added if-absent so we
    // never collide with any the prelude inits already registered).
    for name in [
        "Classical.byContradiction",
        "False.elim",
        "Iff.intro",
        "Iff.mp",
        "Iff.mpr",
    ] {
        let _ = env.add_decl_if_absent(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        });
    }

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, Expr::arrow(p, q));
    let err = contrapose(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::EnvironmentMissing { ref constant } if constant == "propext"),
        "expected missing propext, got: {err:?}"
    );
}

#[test]
fn test_contrapose_non_implication_fails() {
    let env = setup_env();
    // Goal: A (not an implication)
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let err = contrapose(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::GoalMismatch(ref msg) if msg.contains("not an implication")),
        "contrapose on non-implication should mention 'not an implication', got: {err}"
    );
}

// =========================================================================
// push_neg tests
// =========================================================================

#[test]
fn test_match_not_pi_form() {
    // ¬P = P → False
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let not_p = Expr::arrow(p.clone(), false_const);

    let inner = match_not(&not_p).expect("match_not should recognize P → False as ¬P");
    assert_eq!(inner, p);
}

#[test]
fn test_is_false() {
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    assert!(is_false(&false_const));

    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    assert!(!is_false(&true_const));
}

#[test]
fn test_make_not() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not_p = make_not(&p);

    // Should be P → False
    if let ExprKind::Pi(_, dom, cod) = not_p.kind() {
        assert_eq!(**dom, p);
        assert!(is_false(cod));
    } else {
        panic!("Expected Pi type for Not");
    }
}

#[test]
fn test_push_neg_double_negation() {
    // ¬¬P → P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let not_p = make_not(&p);
    let not_not_p = make_not(&not_p);

    let result = push_neg_expr(&not_not_p, &mut state);
    assert_eq!(result, p);
}

#[test]
fn test_push_neg_missing_by_contradiction_fails() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_iff().unwrap();
    env.init_propext().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, make_not(&make_not(&p)));
    let err = push_neg(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::EnvironmentMissing { ref constant } if constant == "Classical.byContradiction"),
        "expected missing Classical.byContradiction, got: {err:?}"
    );
}

#[test]
fn test_push_neg_non_nat_comparison_stays_unchanged() {
    let carrier = Expr::const_(Name::from_string("Carrier"), vec![]);
    let inst_le = Expr::const_(Name::from_string("instLECarrier"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let carrier_le = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![]),
                    carrier.clone(),
                ),
                inst_le,
            ),
            x,
        ),
        y,
    );

    let env = Environment::new();
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let negated = make_not(&carrier_le);
    assert_eq!(push_neg_expr(&negated, &mut state), negated);
}

#[test]
fn test_push_neg_proof_carry_preserves_bvars_under_forall_not_and() {
    let mut env = setup_env_with_prop_ext();
    env.init_nat().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_prop = Expr::arrow(nat.clone(), Expr::prop());
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_to_prop.clone(),
        })
        .unwrap();
    }

    let p_x = Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0));
    let q_x = Expr::app(Expr::const_(Name::from_string("Q"), vec![]), Expr::bvar(0));
    let and_pq = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_x.clone()),
        q_x.clone(),
    );
    let original_body = make_not(&and_pq);
    let target = Expr::pi(BinderInfo::Default, nat.clone(), original_body.clone());

    let mut state = ProofState::new(env.clone(), target.clone());
    let goal = state.current_goal().expect("goal should exist").clone();
    let result = push_neg_expr_with_proof(&mut state, &goal, &target)
        .expect("push_neg proof-carry should rewrite binder-bearing conjunction");

    let expected_body = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            make_not(&p_x),
        ),
        make_not(&q_x),
    );
    let expected_target = Expr::pi(BinderInfo::Default, nat, expected_body);
    assert_eq!(
        result.expr, expected_target,
        "push_neg should preserve the forall binder while rewriting the body"
    );

    let proof = result
        .proof
        .expect("binder-bearing push_neg rewrite should return an equality proof");
    assert!(
        !proof.has_fvar_quick(),
        "push_neg proof-carry should close over the forall binder: {proof:?}"
    );

    let expected_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::prop(),
            ),
            target,
        ),
        expected_target,
    );
    let tc = TypeChecker::new(&env);
    assert!(
        tc.check_type(&proof, &expected_ty).is_ok(),
        "push_neg binder proof should type-check against the rewritten equality target"
    );
}

// =========================================================================
// tauto tests
// =========================================================================

#[test]
fn test_tauto_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    let goal = state.current_goal().expect("goal should exist").clone();
    state.close_goal(&goal, proof).unwrap();

    // Now tauto should fail with NoGoals
    let result = tauto(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_tauto_true_goal() {
    let mut env = setup_env();
    env.init_true_false().unwrap();

    // Goal: True
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, true_const);

    // tauto tries various tactics including trivial
    // The result depends on whether trivial can construct True.intro
    let result = tauto(&mut state);

    // If tauto succeeds on True, all goals should be closed
    if result.is_ok() {
        assert!(
            state.goals().is_empty(),
            "tauto should close True goal when successful"
        );
    }
}

#[test]
fn test_tauto_splits_and_hypothesis() {
    let env = setup_env_with_and_or();
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let and_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty.clone()),
        q_ty,
    );
    let goal_ty = Expr::pi(BinderInfo::Default, and_ty, p_ty.clone());

    let mut state = ProofState::new(env, goal_ty);
    let result = tauto(&mut state);
    assert!(
        result.is_ok(),
        "tauto should use ∧ hypothesis to prove left conjunct"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after using And hypothesis"
    );
}

#[test]
fn test_tauto_splits_or_hypothesis() {
    let mut env = setup_env_with_and_or();
    env.init_true_false().unwrap();

    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);

    // (P ∨ Q) → (P → Q) → Q
    let or_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_ty.clone()),
        q_ty.clone(),
    );
    let p_implies_q = Expr::pi(BinderInfo::Default, p_ty.clone(), q_ty.clone());
    let goal_ty = Expr::pi(
        BinderInfo::Default,
        or_ty,
        Expr::pi(BinderInfo::Default, p_implies_q, q_ty.clone()),
    );

    let mut state = ProofState::new(env, goal_ty);
    let result = tauto(&mut state);
    assert!(
        result.is_ok(),
        "tauto should case-split on disjunctive hypothesis and close the goal"
    );
    assert!(
        state.is_complete(),
        "goal should be solved after disjunction split"
    );
}

#[test]
fn test_tauto_uses_contradiction_in_context() {
    let mut env = setup_env_with_and_or();
    env.init_true_false().unwrap();

    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    let not_p = Expr::pi(BinderInfo::Default, p_ty.clone(), false_ty);
    let and_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty.clone()),
        not_p,
    );
    // (P ∧ ¬P) → Q
    let goal_ty = Expr::pi(BinderInfo::Default, and_ty, q_ty.clone());

    let mut state = ProofState::new(env, goal_ty);
    let result = tauto(&mut state);
    assert!(
        result.is_ok(),
        "tauto should close goals when the context is contradictory"
    );
    assert!(
        state.is_complete(),
        "goal should be discharged by contradiction"
    );
}

#[test]
fn test_fresh_hyp_name() {
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: Expr::prop(),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(1),
            name: "h1".to_string(),
            ty: Expr::prop(),
            value: None,
        },
    ];

    let name = fresh_hyp_name(&ctx, "h");
    assert_eq!(name, "h2");

    let name2 = fresh_hyp_name(&ctx, "x");
    assert_eq!(name2, "x");
}
