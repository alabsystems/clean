// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Search tactics tests (exact?, apply?, suggest, aesop, hint)
//!
//! Split from advanced.rs as part of #1150.

use super::*;

#[test]
fn test_exact_search_finds_hypothesis() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        a.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: a.clone(),
            value: None,
        }],
    );

    let results = exact_search(&mut state, 10).unwrap();
    assert!(!results.is_empty());
    assert_eq!(results[0].name.to_string(), "h");
    assert!(results[0].suggestion.contains("exact"));
}

#[test]
fn test_exact_search_no_match() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::with_context(
        env,
        a,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: b,
            value: None,
        }],
    );

    let results = exact_search(&mut state, 10).unwrap();
    // No matching hypothesis in local context
    assert!(results.iter().all(|r| r.name.to_string() != "h"));
}

#[test]
fn test_apply_search_finds_implication() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    // B → A (implication)
    let impl_ty = Expr::pi(BinderInfo::Default, b.clone(), a.clone());

    let mut state = ProofState::with_context(
        env,
        a,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "f".to_string(),
            ty: impl_ty,
            value: None,
        }],
    );

    let results = apply_search(&mut state, 10).unwrap();
    assert!(!results.is_empty());
    // Should find the implication hypothesis
    let found = results.iter().any(|r| r.name.to_string() == "f");
    assert!(found);
}

#[test]
fn test_suggest_equality_goal() {
    let env = setup_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    // Eq.{1} Nat n n (Nat : Type = Sort 1, so Eq needs universe 1)
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            n.clone(),
        ),
        n,
    );
    let mut state = ProofState::new(env, eq_goal);

    let suggestions = suggest(&mut state, 10).unwrap();
    assert!(!suggestions.is_empty());

    // Should suggest rfl for equality
    let has_rfl = suggestions.iter().any(|s| s.tactic == "rfl");
    assert!(has_rfl);
    let has_cert_simp = suggestions.iter().any(|s| s.tactic == "cert_simp");
    assert!(
        has_cert_simp,
        "equality suggestions should include certificate simplification"
    );
}

#[test]
fn test_suggest_conjunction_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    // And A B
    let and_goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
        b,
    );
    let mut state = ProofState::new(env, and_goal);

    let suggestions = suggest(&mut state, 10).unwrap();

    // Should suggest constructor or split for And
    let has_constructor = suggestions.iter().any(|s| s.tactic == "constructor");
    let has_split = suggestions.iter().any(|s| s.tactic == "split");
    assert!(has_constructor || has_split);
}

#[test]
fn test_suggest_disjunction_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    // Or A B
    let or_goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a),
        b,
    );
    let mut state = ProofState::new(env, or_goal);

    let suggestions = suggest(&mut state, 10).unwrap();

    // Should suggest left/right for Or
    let has_left = suggestions.iter().any(|s| s.tactic == "left");
    let has_right = suggestions.iter().any(|s| s.tactic == "right");
    assert!(has_left || has_right);
}

#[test]
fn test_suggest_implication_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    // A → B (Pi type)
    let impl_goal = Expr::pi(BinderInfo::Default, a, b);
    let mut state = ProofState::new(env, impl_goal);

    let suggestions = suggest(&mut state, 10).unwrap();

    // Should suggest intro for implication
    let has_intro = suggestions
        .iter()
        .any(|s| s.tactic == "intro" || s.tactic == "intros");
    assert!(has_intro);
}

#[test]
fn test_hint_equality() {
    let env = setup_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    // Eq.{1} Nat n n (Nat : Type = Sort 1, so Eq needs universe 1)
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            n.clone(),
        ),
        n,
    );
    let state = ProofState::new(env, eq_goal);

    let hints = hint(&state).unwrap();
    assert!(!hints.is_empty());
    // Should mention it's an equality
    let mentions_equality = hints.iter().any(|h| h.contains("equality"));
    assert!(mentions_equality);
    let mentions_cert_simp = hints.iter().any(|h| h.contains("cert_simp"));
    assert!(
        mentions_cert_simp,
        "equality hints should mention certificate simplification"
    );
}

#[test]
fn test_hint_conjunction() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let and_goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
        b,
    );
    let state = ProofState::new(env, and_goal);

    let hints = hint(&state).unwrap();
    assert!(!hints.is_empty());
    let mentions_conjunction = hints.iter().any(|h| h.contains("conjunction"));
    assert!(mentions_conjunction);
}

#[test]
fn test_exact_search_and_apply_closes_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        a.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: a.clone(),
            value: None,
        }],
    );

    exact_search_and_apply(&mut state)
        .expect("exact_search_and_apply should succeed when hypothesis matches goal");
    assert!(state.goals.is_empty());
}

#[test]
fn test_exact_search_and_apply_fails_no_match() {
    let env = setup_env();
    // Use unique names to avoid accidental matches from environment
    let unique_goal_type = Expr::const_(Name::from_string("UniqueGoalType___XXZZ"), vec![]);
    let unique_hyp_type = Expr::const_(Name::from_string("UniqueHypType___YYWW"), vec![]);
    let mut state = ProofState::with_context(
        env,
        unique_goal_type,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: unique_hyp_type,
            value: None,
        }],
    );

    let err = exact_search_and_apply(&mut state).unwrap_err();
    // Should fail because UniqueGoalType___XXZZ != UniqueHypType___YYWW
    assert!(
        matches!(err, TacticError::SearchExhausted { .. }),
        "exact_search_and_apply with type mismatch should produce SearchExhausted, got: {err}"
    );
}

// ==========================================================================
// rw? (rewrite_search / rewrite_search_and_apply) tests
// ==========================================================================

#[test]
fn test_rewrite_search_finds_equality_hypothesis() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: P(x), hypothesis h : x = y — rw? should suggest `rw [h]`.
    let mut state = ProofState::with_context(
        env,
        make_p(x.clone()),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq_n(x.clone(), y.clone()),
            value: None,
        }],
    );

    let results = rewrite_search(&mut state, 10).expect("rewrite_search should run on a goal");
    assert!(
        results.iter().any(|r| r.name.to_string() == "h"),
        "rw? should find the equality hypothesis h : x = y"
    );
    let h = results
        .iter()
        .find(|r| r.name.to_string() == "h")
        .expect("h should be among the results");
    assert_eq!(
        h.suggestion, "rw [h]",
        "suggestion should be the explicit `rw [h]` form"
    );
    // Search must not mutate the live goal: still P(x), still one open goal.
    assert_eq!(state.goals.len(), 1, "rewrite_search must not close goals");
    assert_eq!(
        state.current_goal().expect("goal present").target,
        make_p(x),
        "rewrite_search must leave the goal unchanged"
    );
}

#[test]
fn test_rewrite_search_no_applicable_equality_reports_none() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: P(x). Hypothesis h : y = z — neither y nor z occurs in P(x), so no
    // rewrite applies. rw? must report nothing (and never panic).
    let mut state = ProofState::with_context(
        env,
        make_p(x),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq_n(y, z),
            value: None,
        }],
    );

    let results = rewrite_search(&mut state, 10).expect("rewrite_search should run on a goal");
    assert!(
        results.iter().all(|r| r.name.to_string() != "h"),
        "h : y = z must not be reported as applicable to P(x)"
    );
}

#[test]
fn test_rewrite_search_and_apply_matches_explicit_rw() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let hyp = || LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: make_eq_n(x.clone(), y.clone()),
        value: None,
    };

    // State A: apply via rw?.
    let mut via_rw_q =
        ProofState::with_context(setup_env_with_full_eq(), make_p(x.clone()), vec![hyp()]);
    rewrite_search_and_apply(&mut via_rw_q)
        .expect("rw? should apply the equality hypothesis h : x = y to P(x)");

    // State B: apply via explicit `rw [h]` (forward).
    let mut via_explicit =
        ProofState::with_context(setup_env_with_full_eq(), make_p(x.clone()), vec![hyp()]);
    rewrite(&mut via_explicit, "h", false).expect("explicit rw [h] should succeed");

    // Both should yield the same number of open goals and the same target P(y),
    // proving rw? went through the same kernel-checked Eq.subst rewrite as `rw`.
    assert_eq!(
        via_rw_q.goals.len(),
        via_explicit.goals.len(),
        "rw? and explicit rw should leave the same number of goals"
    );
    assert_eq!(
        via_rw_q.current_goal().expect("rw? goal present").target,
        make_p(y.clone()),
        "rw? should rewrite P(x) to P(y)"
    );
    assert_eq!(
        via_rw_q.current_goal().expect("rw? goal").target,
        via_explicit
            .current_goal()
            .expect("explicit rw goal")
            .target,
        "rw? must produce the identical goal target as explicit rw [h]"
    );
}

#[test]
fn test_rewrite_search_and_apply_no_match_is_search_exhausted() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal P(x) with only h : y = z available — no rewrite applies.
    let mut state = ProofState::with_context(
        env,
        make_p(x),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq_n(y, z),
            value: None,
        }],
    );

    let err = rewrite_search_and_apply(&mut state)
        .expect_err("rw? with no applicable rewrite should error, not panic");
    assert!(
        matches!(err, TacticError::SearchExhausted { ref tactic, .. } if tactic == "rw?"),
        "rw? with no applicable rewrite should produce SearchExhausted, got: {err}"
    );
}

#[test]
fn test_aesop_config_default() {
    let config = AesopConfig::default();
    assert_eq!(config.max_depth, 10);
    assert_eq!(config.max_goals, 100);
    assert!(config.use_simp);
    assert!(config.use_unfold);
}

#[test]
fn test_aesop_rule_kind() {
    let safe = AesopRuleKind::Safe;
    let norm = AesopRuleKind::Norm;
    let unsafe_rule = AesopRuleKind::Unsafe(50);

    // Test pattern matching works
    match safe {
        AesopRuleKind::Safe => {}
        _ => panic!("Expected Safe"),
    }
    match norm {
        AesopRuleKind::Norm => {}
        _ => panic!("Expected Norm"),
    }
    match unsafe_rule {
        AesopRuleKind::Unsafe(p) => assert_eq!(p, 50),
        _ => panic!("Expected Unsafe"),
    }
}

#[test]
fn test_aesop_trivial_goal() {
    let env = setup_env();
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let mut state = ProofState::new(env, true_const);
    let ax = axiom_snapshot();

    // Aesop should close a trivial propositional goal without spending
    // trustedAy. This guards the last known baseline suspect in the #2442 lane.
    aesop(&mut state).expect("aesop should prove True");
    assert!(state.is_complete(), "aesop should close the trivial goal");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "aesop should not use trusted axioms to prove True"
    );
    assert_no_trusted_axiom_usage("aesop", "trivial True goal", ax);
}

#[test]
fn test_aesop_with_hypothesis() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        a.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: a.clone(),
            value: None,
        }],
    );

    // With h : A in context and goal A, aesop must find the proof via assumption.
    // This is the most basic aesop use case — failing here indicates a regression.
    aesop(&mut state).expect("aesop must close goal A when h : A is in context");
    assert!(
        state.goals().is_empty(),
        "all goals should be closed after aesop proves A from h : A"
    );
}

#[test]
fn test_aesop_max_depth_exceeded() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    // Provide `ha : A` as a local hypothesis so assumption can find it
    let mut state = ProofState::with_context(
        env,
        a.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "ha".to_string(),
            ty: a,
            value: None,
        }],
    );

    let config = AesopConfig {
        max_depth: 0,
        max_goals: 100,
        use_simp: true,
        use_unfold: true,
        ..Default::default()
    };

    // max_depth 0 still allows the root goal to be processed at depth 0.
    // ha : A is in local context, so aesop finds it via assumption and succeeds.
    aesop_with_config(&mut state, config)
        .expect("aesop with max_depth 0 should succeed when goal is provable at depth 0");
    assert!(
        state.goals().is_empty(),
        "aesop should close goal A via ha : A"
    );
}

#[test]
fn test_search_result_fields() {
    let result = SearchResult {
        name: Name::from_string("test"),
        expr: Expr::const_(Name::from_string("test"), vec![]),
        suggestion: "exact test".to_string(),
    };

    assert_eq!(result.name.to_string(), "test");
    assert_eq!(result.suggestion, "exact test");
}

#[test]
fn test_tactic_suggestion_fields() {
    let suggestion = TacticSuggestion {
        tactic: "rfl".to_string(),
        confidence: 0.9,
        reason: "Test reason".to_string(),
    };

    assert_eq!(suggestion.tactic, "rfl");
    assert!((suggestion.confidence - 0.9).abs() < 0.001);
    assert_eq!(suggestion.reason, "Test reason");
}

#[test]
fn test_can_apply_to_produce() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // B → A
    let impl_ty = Expr::pi(BinderInfo::Default, b.clone(), a.clone());

    // Create ProofState+Goal so can_apply_to_produce has proper context (#2229)
    let state = ProofState::new(env, a.clone());
    let goal = state.current_goal().expect("should have goal");

    // Should be able to apply B → A to produce A with 1 argument
    let args = can_apply_to_produce(&state, goal, &impl_ty, &a, 5)
        .expect("B → A should be applicable to produce A");
    assert_eq!(args.len(), 1);
}

#[test]
fn test_can_apply_to_produce_no_match() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);

    // B → C
    let impl_ty = Expr::pi(BinderInfo::Default, b, c);

    let state = ProofState::new(env, a.clone());
    let goal = state.current_goal().expect("should have goal");

    // Should not be able to apply B → C to produce A
    assert_eq!(
        can_apply_to_produce(&state, goal, &impl_ty, &a, 5),
        None,
        "B → C should not be applicable to produce A"
    );
}

#[test]
fn test_types_unify_identical() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let state = ProofState::new(env, a.clone());
    let goal = state.current_goal().expect("should have goal");

    assert!(types_unify(&state, goal, &a, &a));
}

#[test]
fn test_types_unify_different() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let state = ProofState::new(env, a.clone());
    let goal = state.current_goal().expect("should have goal");

    assert!(!types_unify(&state, goal, &a, &b));
}
