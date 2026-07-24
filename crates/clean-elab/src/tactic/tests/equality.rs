// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for equality reasoning tactics: rewrite, symm, trans, calc_trans.
//!
//! Extracted from core.rs during #307 large file split.

use super::*;
use crate::agent_diagnostics::AgentDiagnosticSeverity;
use clean_kernel::env::Declaration;

#[test]
fn test_rewrite_replaces_lhs_with_rhs() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: P(x)
    // Hypothesis h : x = y
    let target = make_p(x.clone());
    let h_ty = make_eq_n(x.clone(), y.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    // After rewrite h, goal should become P(y)
    let result = rewrite(&mut state, "h", false);
    assert!(result.is_ok(), "rewrite should succeed");

    // Goal should now be P(y)
    let new_goal = state.current_goal().unwrap();
    let expected = make_p(y.clone());
    assert_eq!(
        new_goal.target, expected,
        "goal should be P(y) after rewrite"
    );
}

#[test]
fn test_rewrite_rtl_replaces_rhs_with_lhs() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: P(y)
    // Hypothesis h : x = y
    let target = make_p(y.clone());
    let h_ty = make_eq_n(x.clone(), y.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    // After rewrite h (reverse), goal should become P(x)
    let result = rewrite(&mut state, "h", true);
    assert!(result.is_ok(), "rewrite_rtl should succeed");

    // Goal should now be P(x)
    let new_goal = state.current_goal().unwrap();
    let expected = make_p(x.clone());
    assert_eq!(
        new_goal.target, expected,
        "goal should be P(x) after rewrite_rtl"
    );
}

#[test]
fn test_rewrite_hypothesis_not_found() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x);

    let mut state = ProofState::new(env, target);

    // Try to rewrite with nonexistent hypothesis
    let result = rewrite(&mut state, "h", false);
    assert!(
        result.is_err(),
        "rewrite with missing hypothesis should fail"
    );
}

#[test]
fn test_rewrite_non_equality_fails() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());

    // Hypothesis h : P(x) (not an equality)
    let h_ty = make_p(x.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    // Try to rewrite with non-equality hypothesis
    let result = rewrite(&mut state, "h", false);
    assert!(
        result.is_err(),
        "rewrite with non-equality hypothesis should fail"
    );
}

#[test]
fn test_rewrite_pattern_not_in_goal_fails() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: P(z)
    // Hypothesis h : x = y (but z is not in {x, y})
    let target = make_p(z);
    let h_ty = make_eq_n(x, y);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    // rewrite should fail because goal doesn't contain x or y, and should
    // expose the exact focused term to agent diagnostics.
    let result = rewrite(&mut state, "h", false);
    match result {
        Err(TacticError::RewriteNoMatch {
            rule,
            searched_for,
            focus,
            candidates,
            ..
        }) => {
            assert_eq!(rule, "h");
            assert!(searched_for.contains('x'));
            assert!(focus.contains('z'));
            assert!(
                candidates
                    .iter()
                    .any(|candidate| candidate.subterm.contains('z')
                        && candidate.path.starts_with("root")),
                "expected nearby subterm candidate mentioning z, got {candidates:?}"
            );
            let diag = TacticError::RewriteNoMatch {
                tactic: "rewrite".to_owned(),
                rule,
                direction: "forward".to_owned(),
                searched_for,
                focus,
                focus_path: Vec::new(),
                candidates,
            }
            .agent_diagnostics()
            .pop()
            .expect("rewrite no-match should expose an agent diagnostic");
            assert_eq!(diag.code, "rewrite.no_match");
            assert_eq!(diag.severity, AgentDiagnosticSeverity::Error);
            assert_eq!(
                diag.facts.get("failedSubtermPath").map(String::as_str),
                Some("root")
            );
            assert!(diag.facts.contains_key("candidate.0.path"));
            assert!(!diag.related.is_empty());
        }
        other => panic!("expected RewriteNoMatch when pattern not in goal, got {other:?}"),
    }
}

#[test]
fn test_rewrite_no_goals_fails() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_p(x.clone());
    let h_ty = make_eq_n(x.clone(), y);

    // Create state with hypothesis
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    // Clear goals to simulate completed proof
    state.goals.clear();

    // Now try rewrite on completed proof
    let result = rewrite(&mut state, "h", false);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "rewrite on complete proof should fail with NoGoals"
    );
}

// =========================================================================
// symm tactic tests
// =========================================================================

/// Environment with Eq but without Eq.symm (used to test missing constant errors)
fn setup_env_without_symm() -> Environment {
    let mut env = Environment::new();

    // Add Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();

    // Add a base type N and two constants x y : N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["x", "y"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("N"), vec![]),
        })
        .unwrap();
    }

    env
}

#[test]
fn test_symm_swaps_goal_and_uses_hypothesis() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: x = y with hypothesis h : y = x
    let target = make_eq_n(x.clone(), y.clone());
    let hyp_ty = make_eq_n(y.clone(), x.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty,
            value: None,
        }],
    );

    symm(&mut state).unwrap();

    // Goal should now be y = x
    assert_eq!(state.goals().len(), 1);
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(y.clone(), x.clone())
    );

    // Use the hypothesis to close the swapped goal
    assumption(&mut state).unwrap();
    assert!(
        state.is_complete(),
        "symm + assumption should solve equality"
    );

    // Proof should be Eq.symm h
    let mut expected = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    expected = Expr::app(expected, Expr::const_(Name::from_string("N"), vec![]));
    expected = Expr::app(expected, y);
    expected = Expr::app(expected, x);
    expected = Expr::app(expected, Expr::fvar(FVarId::new(0)));

    assert_eq!(state.instantiated_proof().unwrap(), expected);
}

#[test]
fn test_symm_requires_eq_symm_constant() {
    let env = setup_env_without_symm();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_eq_n(x, y);

    let mut state = ProofState::new(env, target);

    let result = symm(&mut state);
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant.contains("Eq.symm")),
        "symm should fail when Eq.symm is missing"
    );
}

#[test]
fn test_symm_goal_mismatch() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = symm(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

// =========================================================================
// Tests for trans and calc_trans tactics
// =========================================================================

#[test]
fn test_trans_splits_goal_into_two_subgoals() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: x = z
    let target = make_eq_n(x.clone(), z.clone());

    let mut state = ProofState::new(env, target);

    // Apply trans with middle term y
    trans(&mut state, y.clone()).unwrap();

    // Should have 2 goals
    assert_eq!(state.goals().len(), 2);

    // First goal: x = y
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x.clone(), y.clone())
    );

    // Second goal: y = z
    assert_eq!(state.goals()[1].target, make_eq_n(y.clone(), z.clone()));
}

#[test]
fn test_trans_proof_term_structure() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: x = z
    let target = make_eq_n(x.clone(), z.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(y.clone(), z.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // Apply trans with middle term y
    trans(&mut state, y.clone()).unwrap();

    // First goal x = y, closed by h1
    assumption(&mut state).unwrap();

    // Second goal y = z, closed by h2
    assumption(&mut state).unwrap();

    assert!(
        state.is_complete(),
        "trans + assumption + assumption should solve"
    );

    // Verify proof term structure: Eq.trans {N} {x} {y} {z} h1 h2
    let proof = state.instantiated_proof().unwrap();
    let head = proof.get_app_fn();
    let args = proof.get_app_args();

    // Should be Eq.trans applied to 6 arguments
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.trans"))
    );
    assert_eq!(args.len(), 6); // α, a, b, c, h1, h2
    assert_eq!(args[4], &Expr::fvar(FVarId::new(0))); // h1
    assert_eq!(args[5], &Expr::fvar(FVarId::new(1))); // h2
}

#[test]
fn test_trans_with_hypotheses() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: x = z with hypotheses h1: x = y, h2: y = z
    let target = make_eq_n(x.clone(), z.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(y.clone(), z.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // Apply trans with middle term y
    trans(&mut state, y.clone()).unwrap();

    // First goal x = y, closed by h1
    assumption(&mut state).unwrap();

    // Second goal y = z, closed by h2
    assumption(&mut state).unwrap();

    assert!(
        state.is_complete(),
        "trans + assumption + assumption should solve"
    );
}

#[test]
fn test_trans_requires_eq_trans_constant() {
    // Create environment without Eq.trans
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("N"), vec![]),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_eq_n(x.clone(), x.clone());

    let mut state = ProofState::new(env, target);

    let result = trans(&mut state, x);
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant.contains("Eq.trans")),
        "trans should fail when Eq.trans is missing"
    );
}

#[test]
fn test_trans_goal_mismatch() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let middle = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = trans(&mut state, middle);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_calc_trans_from_hypotheses() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: x = z with hypotheses h1: x = y, h2: y = z
    let target = make_eq_n(x.clone(), z.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(y.clone(), z.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // Apply calc_trans with h1 and h2
    calc_trans(&mut state, "h1", "h2").unwrap();

    assert!(state.is_complete(), "calc_trans should solve goal directly");

    // Verify the proof structure: Eq.trans h1 h2
    let proof = state.instantiated_proof().unwrap();
    let args = proof.get_app_args();
    assert_eq!(args.len(), 6); // α, a, b, c, h1, h2
    assert_eq!(args[4], &Expr::fvar(FVarId::new(0))); // h1
    assert_eq!(args[5], &Expr::fvar(FVarId::new(1))); // h2
}

#[test]
fn test_calc_trans_chain_broken() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: x = z with hypotheses h1: x = y, h2: x = z (wrong middle!)
    let target = make_eq_n(x.clone(), z.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone()); // x = y
    let h2_ty = make_eq_n(x.clone(), z.clone()); // x = z (should be y = z)

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let result = calc_trans(&mut state, "h1", "h2");
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref msg)) if msg.contains("transitivity chain broken")),
        "calc_trans should fail when chain is broken"
    );
}

#[test]
fn test_calc_trans_hypothesis_not_found() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let target = make_eq_n(x.clone(), y.clone());

    let mut state = ProofState::new(env, target);

    let result = calc_trans(&mut state, "h1", "h2");
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(name)) if name == "h1"),
        "calc_trans should fail when hypothesis not found"
    );
}

#[test]
fn test_calc_trans_not_equality() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: x = y with h1: P (not an equality)
    let target = make_eq_n(x.clone(), y.clone());
    let h1_ty = make_p(x.clone()); // P(x), not an equality

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h1".to_string(),
            ty: h1_ty,
            value: None,
        }],
    );

    let result = calc_trans(&mut state, "h1", "h1");
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(msg)) if msg.contains("is not an equality")),
        "calc_trans should fail when hypothesis is not an equality"
    );
}
