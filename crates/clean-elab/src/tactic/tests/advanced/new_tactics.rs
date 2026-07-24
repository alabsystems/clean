// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for newer tactic families: abel, group, apply_fun, clear_except,
//! replace, cc, itauto, clean, substs, bound.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// =========================================================================
// Tests for new tactics: abel, group, apply_fun, clear_except, replace, cc
// =========================================================================

#[test]
fn test_abel_no_goals() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = abel(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_group_no_goals() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = group(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_group_non_equality_fails() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    let result = group(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("equality")));
}

#[test]
fn test_apply_fun_hypothesis_not_found() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    let func = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let result = apply_fun(&mut state, func, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_apply_fun_goal_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let func = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let result = apply_fun_goal(&mut state, func);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_clear_except_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = clear_except(&mut state, &[]);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_clear_except_keeps_specified() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, p.clone());

    let goal = state.current_goal_mut().unwrap();
    goal.local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "h1".to_string(),
        ty: p.clone(),
        value: None,
    });
    goal.local_ctx.push(LocalDecl {
        fvar: FVarId::new(101),
        name: "h2".to_string(),
        ty: p.clone(),
        value: None,
    });

    clear_except(&mut state, &["h1"]).unwrap();
    let goal = state.current_goal().unwrap();
    assert!(goal.local_ctx.iter().any(|d| d.name == "h1"));
}

#[test]
fn test_replace_hypothesis_not_found() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    let result = replace(&mut state, "nonexistent", Expr::prop());
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_replace_creates_new_goal() {
    let mut env = Environment::new();
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
    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "h".to_string(),
            ty: p.clone(),
            value: None,
        }],
    );

    let initial_goals = state.goals.len();
    replace(&mut state, "h", q.clone()).unwrap();
    assert_eq!(state.goals.len(), initial_goals + 1);
}

#[test]
fn test_replace_proof_goal_keeps_later_dependency_context() {
    let env = setup_env_with_full_eq();
    let h_fvar = FVarId::new(100);
    let n_fvar = FVarId::new(101);
    let target = make_p(Expr::const_(Name::from_string("x"), vec![]));
    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: h_fvar,
                name: "h".to_string(),
                ty: make_p(Expr::const_(Name::from_string("x"), vec![])),
                value: None,
            },
            LocalDecl {
                fvar: n_fvar,
                name: "n".to_string(),
                ty: Expr::const_(Name::from_string("N"), vec![]),
                value: None,
            },
        ],
    );

    replace(&mut state, "h", make_p(Expr::fvar(n_fvar))).unwrap();

    let main_goal = state.current_goal().unwrap();
    let h = main_goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("main goal should keep a visible replacement hypothesis");
    assert_eq!(h.ty, make_p(Expr::fvar(n_fvar)));
    let h_pos = main_goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == "h")
        .expect("replacement hypothesis should be present");
    let n_pos = main_goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == "n")
        .expect("later dependency should remain present");
    assert!(
        h_pos > n_pos,
        "replacement must be inserted after the dependency"
    );

    let proof_goal = state
        .goals()
        .back()
        .expect("replace should append a proof goal");
    assert_eq!(proof_goal.target, make_p(Expr::fvar(n_fvar)));
    assert!(
        proof_goal.local_ctx.iter().any(|decl| decl.fvar == n_fvar),
        "proof goal must keep later locals needed to prove the replacement type"
    );
}

#[test]
fn test_replace_hyp_updates_hypothesis() {
    let mut env = Environment::new();
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
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q_proof"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let proof = Expr::const_(Name::from_string("q_proof"), vec![]);
    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "h".to_string(),
            ty: p.clone(),
            value: None,
        }],
    );

    replace_hyp(&mut state, "h", q.clone(), proof).unwrap();
    let goal = state.current_goal().unwrap();
    let h = goal.local_ctx.iter().find(|d| d.name == "h").unwrap();
    assert!(exprs_equal(&h.ty, &q));
}

#[test]
fn test_cc_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = cc(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_cc_non_equality_fails() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    let result = cc(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("equality")));
}

#[test]
fn test_itauto_complete_state() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    itauto(&mut state).expect("itauto on complete state should succeed");
    // itauto on a complete state should remain complete (no spurious goals)
    assert!(
        state.is_complete(),
        "itauto should not add goals to a complete state"
    );
}

/// Regression: itauto must prove ALL subgoals after splitting a conjunction,
/// not just the first. Before the fix, `constructor` on `P ∧ Q` created two
/// goals [P, Q], but the recursive search only proved P and returned Ok,
/// leaving Q unsolved.
#[test]
fn test_itauto_conjunction_proves_both_subgoals() {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");

    // Goal: True ∧ True (both sides provable by trivial/constructor)
    let true_ty = Expr::const_(Name::from_string("True"), vec![]);
    let and_target = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [true_ty.clone(), true_ty],
    );
    let mut state = ProofState::new(env, and_target);

    itauto(&mut state).expect("itauto should prove True ∧ True");
    assert!(
        state.is_complete(),
        "itauto must close ALL goals after conjunction split, \
         but {} goal(s) remain",
        state.goals.len()
    );
}

#[test]
fn test_clean_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = clean(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_clean_reduces_beta_redex() {
    let env = Environment::new();
    let target = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::type_(),
    );
    let mut state = ProofState::new(env, target);
    clean(&mut state).unwrap();
    let goal = state.current_goal().unwrap();
    assert!(matches!(goal.target.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_substs_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = substs(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_substs_does_nothing_without_equalities() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    substs(&mut state).expect("substs without equalities should succeed");
    // Without equalities, substs should leave the state unchanged
    assert_eq!(state.goals().len(), 1, "substs should preserve goal count");
    let goal = state.current_goal().unwrap();
    assert!(
        matches!(goal.target.kind(), ExprKind::Sort(_)),
        "substs should not modify the goal target"
    );
}

#[test]
fn test_bound_no_goals() {
    let env = Environment::new();
    let target = Expr::type_();
    let mut state = ProofState::new(env, target);
    state.goals.clear();
    let result = bound(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_abel_term_operations() {
    let term1 = AbelTerm::single(0, Expr::type_());
    let term2 = AbelTerm::single(1, Expr::prop());

    let sum = term1.add(&term2);
    assert_eq!(sum.coefficients.len(), 2);

    let diff = term1.sub(&term2);
    assert_eq!(diff.coefficients.len(), 2);

    let neg = term1.negate();
    assert_eq!(neg.coefficients.get(&0), Some(&-1));

    let zero = AbelTerm::zero();
    assert!(zero.is_zero());
}

#[test]
fn test_group_term_operations() {
    let term1 = GroupTerm::single(0, Expr::type_());
    let term2 = GroupTerm::single(1, Expr::prop());

    let prod = term1.mul(&term2);
    assert_eq!(prod.factors.len(), 2);

    let inv = term1.inv();
    assert_eq!(inv.factors[0].1, -1);

    let squared = term1.pow(2);
    assert_eq!(squared.factors[0].1, 2);

    let id = GroupTerm::identity();
    assert!(id.is_identity());

    let pow_zero = term1.pow(0);
    assert!(pow_zero.is_identity());
}

#[test]
fn test_cc_state_basic() {
    let mut cc_st = CCState::new();
    let expr1 = Expr::const_(Name::from_string("x"), vec![]);
    let expr2 = Expr::const_(Name::from_string("y"), vec![]);

    let id1 = cc_st.add_expr(&expr1);
    let id2 = cc_st.add_expr(&expr2);
    assert_ne!(cc_st.find(id1), cc_st.find(id2));

    cc_st.union(id1, id2);
    assert_eq!(cc_st.find(id1), cc_st.find(id2));
}

#[test]
fn test_beta_reduce_all_identity() {
    let lam = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let reduced = beta_reduce_all(&lam);
    assert!(matches!(reduced.kind(), ExprKind::Lam(_, _, _)));
}

#[test]
fn test_beta_reduce_all_redex() {
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        Expr::type_(),
    );
    let reduced = beta_reduce_all(&redex);
    assert!(matches!(reduced.kind(), ExprKind::Sort(_)));
}

#[test]
fn test_match_eq_simple_basic() {
    let a = Expr::type_();
    let b = Expr::prop();
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::type_(),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let result = match_eq_simple(&eq_expr);
    let result = result.expect("expected Some");
    let (lhs, rhs) = result;
    assert!(exprs_equal(&lhs, &a));
    assert!(exprs_equal(&rhs, &b));
}

#[test]
fn test_match_eq_simple_non_equality() {
    let non_eq = Expr::type_();
    let result = match_eq_simple(&non_eq);
    assert_eq!(result, None);
}

#[test]
fn test_is_pi_expr_true() {
    let pi = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    assert!(is_pi_expr(&pi));
}

#[test]
fn test_is_pi_expr_false() {
    let non_pi = Expr::type_();
    assert!(!is_pi_expr(&non_pi));
}
