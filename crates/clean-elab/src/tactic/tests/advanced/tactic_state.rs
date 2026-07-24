// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic state management tests: refine, use_, native_decide, fin_cases,
//! interval_cases, goal management (swap, rotate, pick_goal), development
//! tactics (sorry, admit), and definition tactics (substitute_const, unfold).

use super::support::close_current_goal_checked;
use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// =========================================================================
// refine tests
// =========================================================================

#[test]
fn test_refine_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now refine should fail with NoGoals
    let result = refine(&mut state, a);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_refine_no_holes() {
    let env = setup_env();
    // A : Type, so providing A as proof of goal A is a type mismatch
    // (A has type Type, not A)
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    let result = refine(&mut state, a);
    // refine delegates to exact, which must fail: A : Type, but goal expects a term of type A
    assert!(
        matches!(result, Err(TacticError::TypeMismatch { .. })),
        "refine should fail with TypeMismatch when proof type doesn't match goal, got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after refine failure"
    );
}

#[test]
fn test_refine_placeholder_uses_function_argument_type_for_subgoal() {
    let env = setup_env();
    let goal_ty = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, goal_ty);

    let refined_term = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("_"), vec![]),
    );
    refine(&mut state, refined_term).expect("refine should infer the placeholder goal type");

    let first_goal = state
        .current_goal()
        .expect("refine with one placeholder should leave one subgoal");
    assert_eq!(
        first_goal.target,
        Expr::const_(Name::from_string("A"), vec![]),
        "refine placeholder goal should use the function argument type, not the parent goal type"
    );
}

#[test]
fn test_refine_placeholder_goals_preserve_left_to_right_order() {
    let mut env = setup_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("C"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::arrow(
                Expr::const_(Name::from_string("B"), vec![]),
                Expr::const_(Name::from_string("C"), vec![]),
            ),
        ),
    })
    .unwrap();

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("C"), vec![]));
    let refined_term = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("g"), vec![]),
            Expr::const_(Name::from_string("_"), vec![]),
        ),
        Expr::const_(Name::from_string("_"), vec![]),
    );
    refine(&mut state, refined_term)
        .expect("refine should preserve left-to-right placeholder goal order");

    let goals: Vec<_> = state
        .goals()
        .iter()
        .map(|goal| goal.target.clone())
        .collect();
    assert_eq!(
        goals.len(),
        2,
        "refine should create one goal per placeholder"
    );
    assert_eq!(
        goals[0],
        Expr::const_(Name::from_string("A"), vec![]),
        "first placeholder should become the first goal"
    );
    assert_eq!(
        goals[1],
        Expr::const_(Name::from_string("B"), vec![]),
        "second placeholder should become the second goal"
    );
}

#[test]
fn test_count_placeholders() {
    // No placeholders
    let a = Expr::const_(Name::from_string("A"), vec![]);
    assert_eq!(count_placeholders(&a), 0);

    // Placeholder constant
    let placeholder = Expr::const_(Name::from_string("_"), vec![]);
    assert_eq!(count_placeholders(&placeholder), 1);

    // Placeholder in app
    let app = Expr::app(a.clone(), placeholder);
    assert_eq!(count_placeholders(&app), 1);

    // Placeholder inside ZFCMem — Part of #2184
    // count_placeholders should recurse into ZFCMem children
    use clean_kernel::expr::ZFCSetExpr;
    let placeholder2 = Expr::const_(Name::from_string("_"), vec![]);
    let zfc_mem = Expr::from_kind(ExprKind::ZFCMem {
        element: std::sync::Arc::new(placeholder2),
        set: std::sync::Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))),
    });
    assert_eq!(
        count_placeholders(&zfc_mem),
        1,
        "BUG: count_placeholders misses placeholder inside ZFCMem expression"
    );

    // Placeholder inside ZFCComprehension
    let placeholder3 = Expr::const_(Name::from_string("?"), vec![]);
    let comprehension = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: std::sync::Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))),
        pred: std::sync::Arc::new(placeholder3),
    });
    assert_eq!(
        count_placeholders(&comprehension),
        1,
        "BUG: count_placeholders misses placeholder inside ZFCComprehension"
    );
}

#[test]
fn test_refine_placeholder() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    refine_placeholder(&mut state).expect("refine_placeholder should succeed");

    // Should have added a goal
    assert!(!state.goals().is_empty());
}

/// Regression test for #2184 acceptance criterion 4: `refine_elaborated`
/// rejects terms that contain elaborator meta FVars not listed in
/// `pending_metas`. This exercises the `remap_elab_metas` residual-meta
/// rejection path in `refine_bridge.rs`.
#[test]
fn test_refine_elaborated_rejects_residual_elab_metas() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a_ty);

    // Create an elaborator MetaState with one unsolved meta
    let mut elab_metas = crate::unify::MetaState::new();
    let orphan_meta = elab_metas.fresh(Expr::type_());

    // Build a term that contains the orphan meta as an FVar
    let term_with_residual = Expr::fvar(crate::unify::MetaState::to_fvar(orphan_meta));

    // Call refine_elaborated with empty pending_metas — the orphan meta
    // in the term is NOT listed, so remap_elab_metas must reject it.
    let result = term_close::refine_elaborated(&mut state, term_with_residual, &elab_metas, &[]);

    assert!(
        result.is_err(),
        "refine_elaborated must reject terms with residual elaborator metas not in pending_metas"
    );
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("unresolved elaborator metas"),
        "error should mention 'unresolved elaborator metas', got: {err_msg}"
    );
}

// =========================================================================
// use_ tests
// =========================================================================

#[test]
fn test_use_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now use_ should fail with NoGoals
    let witness = Expr::const_(Name::from_string("x"), vec![]);
    let result = use_(&mut state, vec![witness]);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_use_no_witnesses() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = use_(&mut state, vec![]);
    assert!(matches!(result, Err(TacticError::MissingArgument { .. })));
}

// =========================================================================
// native_decide tests
// =========================================================================

#[test]
fn test_native_decide_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now native_decide should fail with NoGoals
    let result = native_decide(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

// NOTE: tauto tests moved to propositional.rs (#1150)

// =========================================================================
// fin_cases tests
// =========================================================================

#[test]
fn test_fin_cases_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now fin_cases should fail with NoGoals
    let result = fin_cases(&mut state, "h");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_fin_cases_hypothesis_not_found() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = fin_cases(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_get_finite_inhabitants_bool() {
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let inhabitants =
        get_finite_inhabitants(&bool_ty).expect("get_finite_inhabitants(Bool) should succeed");
    assert_eq!(inhabitants.len(), 2);
}

#[test]
fn test_get_finite_inhabitants_unit() {
    let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
    let inhabitants =
        get_finite_inhabitants(&unit_ty).expect("get_finite_inhabitants(Unit) should succeed");
    assert_eq!(inhabitants.len(), 1);
}

#[test]
fn test_get_finite_inhabitants_empty() {
    let empty_ty = Expr::const_(Name::from_string("Empty"), vec![]);
    let inhabitants =
        get_finite_inhabitants(&empty_ty).expect("get_finite_inhabitants(Empty) should succeed");
    assert!(inhabitants.is_empty());
}

#[test]
fn test_extract_nat_literal_zero() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let result = extract_nat_literal(&zero);
    assert_eq!(result, Some(0));
}

#[test]
fn test_make_nat_literal() {
    let zero = make_nat_literal(0);
    assert!(matches!(zero.kind(), ExprKind::Const(name, _) if name.to_string() == "Nat.zero"));

    let one = make_nat_literal(1);
    assert!(matches!(one.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_substitute_fvar() {
    let fvar_id = FVarId::new(42);
    let fvar = Expr::fvar(fvar_id);
    let replacement = Expr::const_(Name::from_string("x"), vec![]);

    let result = substitute_fvar(&fvar, fvar_id, &replacement);
    assert_eq!(result, replacement);

    // Non-matching fvar
    let other_fvar = Expr::fvar(FVarId::new(99));
    let result2 = substitute_fvar(&other_fvar, fvar_id, &replacement);
    assert_eq!(result2, other_fvar);
}

// =========================================================================
// fin_cases happy-path tests
// =========================================================================

/// Happy path: fin_cases on a Bool hypothesis creates 2 sub-goals with
/// true/false substituted into the target. Verifies #2232 soundness fix
/// and #2154 Wave 10 migration (close_goal type-checks the casesOn proof).
#[test]
fn test_fin_cases_bool_creates_two_subgoals() {
    // Part of #2154 Wave 10: use enriched env with Bool as proper inductive
    // so close_goal can type-check @Bool.casesOn proof term.
    let env = setup_env_for_finite_cases();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    // Goal: P(h) where h : Bool, P : Bool → Prop
    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, Expr::prop());
    let fvar = state.fresh_fvar();
    let target = Expr::app(p_const.clone(), Expr::fvar(fvar));
    state.goals[0].target = target;
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: bool_ty,
        value: None,
    });

    let result = fin_cases(&mut state, "h");
    assert!(
        result.is_ok(),
        "fin_cases on Bool should succeed, got: {result:?}"
    );

    // Should have 2 goals (true, false)
    assert_eq!(
        state.goals.len(),
        2,
        "fin_cases on Bool should produce 2 sub-goals"
    );

    // First goal should have true substituted (inhabitants[0] = true)
    let true_const = Expr::const_(Name::from_string("true"), vec![]);
    let expected_true = Expr::app(p_const.clone(), true_const);
    assert_eq!(
        state.goals[0].target, expected_true,
        "first sub-goal: true substituted"
    );

    // Second goal should have false substituted (inhabitants[1] = false)
    let false_const = Expr::const_(Name::from_string("false"), vec![]);
    let expected_false = Expr::app(p_const, false_const);
    assert_eq!(
        state.goals[1].target, expected_false,
        "second sub-goal: false substituted"
    );
}

/// fin_cases on PUnit produces exactly 1 sub-goal.
/// Part of #2154 Wave 10: uses enriched env for close_goal type-checking.
#[test]
fn test_fin_cases_unit_creates_one_subgoal() {
    let env = setup_env_for_finite_cases();
    // PUnit.{0} : Type 0
    let unit_ty = Expr::const_(Name::from_string("PUnit"), vec![Level::zero()]);

    // Goal: Q(h) where h : PUnit.{0}, Q : PUnit.{0} → Prop
    let q_const = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, Expr::prop());
    let fvar = state.fresh_fvar();
    let target = Expr::app(q_const, Expr::fvar(fvar));
    state.goals[0].target = target;
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: unit_ty,
        value: None,
    });

    let result = fin_cases(&mut state, "h");
    assert!(
        result.is_ok(),
        "fin_cases on PUnit should succeed, got: {result:?}"
    );
    assert_eq!(
        state.goals.len(),
        1,
        "fin_cases on PUnit should produce 1 sub-goal"
    );
}

/// fin_cases on Empty type should fail (no inhabitants).
#[test]
fn test_fin_cases_empty_type_fails() {
    let env = setup_env();
    let empty_ty = Expr::const_(Name::from_string("Empty"), vec![]);

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("A"), vec![]));
    let fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: empty_ty,
        value: None,
    });

    let result = fin_cases(&mut state, "h");
    assert!(
        result.is_err(),
        "fin_cases on Empty should fail (no inhabitants)"
    );
}

// =========================================================================
// interval_cases tests
// =========================================================================

#[test]
fn test_interval_cases_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    // Now interval_cases should fail with NoGoals
    let result = interval_cases(&mut state, "n");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_interval_cases_hypothesis_not_found() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a);
    let result = interval_cases(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

/// Regression test for #2239: interval_cases must not fabricate default bounds.
/// Previously, if no ≤/< hypotheses constrained the variable, the tactic
/// silently used (0..10), producing an unsound Or.elim chain.
#[test]
fn test_interval_cases_no_bounds_returns_error() {
    let env = setup_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut state = ProofState::new(env, Expr::const_(Name::from_string("P"), vec![]));
    let fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "n".to_string(),
        ty: nat_ty,
        value: None,
    });

    let result = interval_cases(&mut state, "n");
    assert!(result.is_err(), "interval_cases without bounds must fail");
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("no bounds"),
        "error should mention missing bounds, got: {err_msg}"
    );
}

#[test]
fn test_expr_to_int_zero() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let result = expr_to_int(&zero);
    assert_eq!(result, Some(0));
}

#[test]
fn test_make_int_literal_positive() {
    let five = make_int_literal(5);
    // Should be Nat.succ (Nat.succ (... Nat.zero))
    assert!(matches!(five.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_make_int_literal_negative() {
    let neg_five = make_int_literal(-5);
    // Should be Int.negOfNat applied to 5
    assert!(matches!(neg_five.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_make_equality_type() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let eq_type = make_equality_type(&nat, &a, &b, Level::succ(Level::zero()));
    // Should be Eq Nat a b
    assert!(matches!(eq_type.kind(), ExprKind::App(_, _)));
}

// =========================================================================
// Goal Management Tactics Tests
// =========================================================================

#[test]
fn test_swap_swaps_first_two_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // Create state with goal A
    let mut state = ProofState::new(env, a.clone());
    // Manually add a second goal
    let meta_id = state.metas.fresh(b.clone());
    state.goals.push_back(Goal {
        meta_id,
        target: b.clone(),
        local_ctx: vec![],
        tag: None,
    });

    assert_eq!(state.goals.len(), 2);
    assert_eq!(state.goals[0].target, a);
    assert_eq!(state.goals[1].target, b);

    // Swap
    swap(&mut state).unwrap();

    assert_eq!(state.goals[0].target, b);
    assert_eq!(state.goals[1].target, a);
}

#[test]
fn test_swap_fails_with_one_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = swap(&mut state);
    assert!(matches!(result, Err(TacticError::InvalidTarget { .. })));
}

#[test]
fn test_rotate_moves_first_to_end() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    let meta_id = state.metas.fresh(b.clone());
    state.goals.push_back(Goal {
        meta_id,
        target: b.clone(),
        local_ctx: vec![],
        tag: None,
    });

    // Before: [A, B]
    assert_eq!(state.goals[0].target, a);
    assert_eq!(state.goals[1].target, b);

    // Rotate
    rotate(&mut state).unwrap();

    // After: [B, A]
    assert_eq!(state.goals[0].target, b);
    assert_eq!(state.goals[1].target, a);
}

#[test]
fn test_rotate_back_moves_last_to_front() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    let meta_id = state.metas.fresh(b.clone());
    state.goals.push_back(Goal {
        meta_id,
        target: b.clone(),
        local_ctx: vec![],
        tag: None,
    });

    // Before: [A, B]
    rotate_back(&mut state).unwrap();

    // After: [B, A]
    assert_eq!(state.goals[0].target, b);
    assert_eq!(state.goals[1].target, a);
}

#[test]
fn test_pick_goal_selects_by_index() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    let meta_id = state.metas.fresh(b.clone());
    state.goals.push_back(Goal {
        meta_id,
        target: b.clone(),
        local_ctx: vec![],
        tag: None,
    });

    // Pick goal at index 1 (B)
    pick_goal(&mut state, 1).unwrap();

    // B should now be first
    assert_eq!(state.goals[0].target, b);
    assert_eq!(state.goals[1].target, a);
}

#[test]
fn test_pick_goal_out_of_bounds() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = pick_goal(&mut state, 5);
    assert!(matches!(result, Err(TacticError::InvalidTarget { .. })));
}

#[test]
fn test_goal_count() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut state = ProofState::new(env, a.clone());
    assert_eq!(goal_count(&state), 1);

    let meta_id = state.metas.fresh(b.clone());
    state.goals.push_back(Goal {
        meta_id,
        target: b,
        local_ctx: vec![],
        tag: None,
    });
    assert_eq!(goal_count(&state), 2);
}

// =========================================================================
// Development Tactics Tests
// =========================================================================

#[test]
fn test_sorry_closes_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    assert_eq!(state.goals.len(), 1);

    sorry(&mut state).unwrap();

    assert_eq!(state.goals.len(), 0);
}

#[test]
fn test_sorry_closes_goal_with_elab_local_type_target() {
    let env = Environment::with_prelude();
    let alpha_fvar = FVarId::new(10);
    let alpha = Expr::fvar(alpha_fvar);
    let elab_locals = vec![LocalDecl {
        fvar: alpha_fvar,
        name: "alpha".to_string(),
        ty: Expr::type_(),
        value: None,
    }];
    let mut state = ProofState::with_elab_context(env.clone(), alpha.clone(), elab_locals.clone());

    let original_goal = state.current_goal().expect("goal should exist").clone();
    sorry(&mut state).expect("explicit sorry should close elaborator-local type target");

    assert!(state.is_complete(), "explicit sorry should close the goal");

    let proof = state
        .closed_proof()
        .expect("completed sorry goal should expose a proof term");

    let mut check_state =
        ProofState::with_elab_context(env, original_goal.target.clone(), elab_locals);
    let check_goal = check_state
        .current_goal()
        .expect("fresh check state should have a goal")
        .clone();
    let proof_ty = check_state
        .infer_type(&check_goal, &proof)
        .expect("explicit sorry proof should type-check in elaborator-local context");
    let expected_ty = check_state.metas().instantiate(&check_goal.target);
    assert!(
        check_state.is_def_eq(&check_goal, &proof_ty, &expected_ty),
        "explicit sorry proof should match the elaborator-local target: expected {expected_ty:?}, got {proof_ty:?}"
    );
    check_state
        .close_goal(&check_goal, proof)
        .expect("explicit sorry proof should pass checked close_goal for elaborator-local targets");
    assert!(
        check_state.is_complete(),
        "checked close_goal should accept the elaborator-local explicit sorry proof"
    );
}

#[test]
fn test_admit_is_alias_for_sorry() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    assert_eq!(state.goals.len(), 1);

    admit(&mut state).unwrap();

    assert_eq!(state.goals.len(), 0);
}

#[test]
fn test_sorry_fails_with_no_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    // Close the goal first
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    close_current_goal_checked(&mut state, proof);

    let result = sorry(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

// =========================================================================
// Definition Tactics Tests
// =========================================================================

#[test]
fn test_substitute_const_replaces_matching() {
    let a = Expr::const_(Name::from_string("foo"), vec![]);
    let replacement = Expr::const_(Name::from_string("bar"), vec![]);
    let name = Name::from_string("foo");

    let result = substitute_const(&a, &name, &replacement);
    assert_eq!(result, replacement);
}

#[test]
fn test_substitute_const_preserves_non_matching() {
    let a = Expr::const_(Name::from_string("other"), vec![]);
    let replacement = Expr::const_(Name::from_string("bar"), vec![]);
    let name = Name::from_string("foo");

    let result = substitute_const(&a, &name, &replacement);
    assert_eq!(result, a);
}

#[test]
fn test_substitute_const_in_app() {
    let foo = Expr::const_(Name::from_string("foo"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let app = Expr::app(foo, x.clone());

    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let name = Name::from_string("foo");

    let result = substitute_const(&app, &name, &bar);

    // Should be (bar x)
    if let ExprKind::App(f, arg) = result.kind() {
        assert_eq!(**f, bar);
        assert_eq!(**arg, x);
    } else {
        panic!("Expected App");
    }
}

#[test]
fn test_collect_consts_finds_all() {
    let foo = Expr::const_(Name::from_string("foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let app = Expr::app(foo, bar);

    let consts = collect_consts(&app);

    assert!(consts.contains(&Name::from_string("foo")));
    assert!(consts.contains(&Name::from_string("bar")));
    assert_eq!(consts.len(), 2);
}

#[test]
fn test_unfold_fails_on_axiom() {
    let env = setup_env();
    // A is an axiom, not a definition
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, goal);

    let result = unfold(&mut state, "A");
    assert!(
        matches!(result, Err(TacticError::UnfoldFailed { ref reason, .. }) if reason.contains("no definition"))
    );
}

// Conv tests: see conv.rs
