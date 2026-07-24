// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic reasoning tactic tests (continued): calc_block, wlog,
//! push_neg_at, norm_num_at, suffices_to_show.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::level::Level;

// =========================================================================
// calc_block Tests
// =========================================================================

#[test]
fn test_calc_block_empty_steps() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    let result = calc_block(&mut state, a, vec![]);
    assert!(matches!(result, Err(TacticError::MissingArgument { .. })));
}

#[test]
fn test_calc_rel_enum() {
    assert_eq!(CalcRel::Eq, CalcRel::Eq);
    assert_ne!(CalcRel::Eq, CalcRel::Le);
    assert_ne!(CalcRel::Lt, CalcRel::Gt);
}

#[test]
fn test_calc_justification_variants() {
    let term = CalcJustification::Term(Expr::type_());
    let hyp = CalcJustification::Hyp("h".to_string());
    let refl = CalcJustification::Refl;
    let lemma = CalcJustification::Lemma("my_lemma".to_string());

    // Just verify variants can be constructed
    match term {
        CalcJustification::Term(_) => {}
        _ => panic!("Expected Term"),
    }
    match hyp {
        CalcJustification::Hyp(name) => assert_eq!(name, "h"),
        _ => panic!("Expected Hyp"),
    }
    match refl {
        CalcJustification::Refl => {}
        _ => panic!("Expected Refl"),
    }
    match lemma {
        CalcJustification::Lemma(name) => assert_eq!(name, "my_lemma"),
        _ => panic!("Expected Lemma"),
    }
}

#[test]
fn test_make_calc_rel_eq() {
    let env = setup_env();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let rel = make_calc_rel(CalcRel::Eq, &x, &y, &mut state);
    // Should be an Eq expression
    let head = rel.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Eq");
    } else {
        panic!("Expected Const");
    }
}

#[test]
fn test_make_calc_rel_le() {
    let env = setup_env();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));

    let rel = make_calc_rel(CalcRel::Le, &x, &y, &mut state);
    let head = rel.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "LE.le");
    } else {
        panic!("Expected Const");
    }
}

#[test]
fn test_calc_eq_creates_two_subgoals() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    let nat_ty = Expr::type_();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: nat_ty,
    })
    .unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: a = c
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a,
        ),
        c,
    );
    let mut state = ProofState::new(env, eq_goal);

    calc_eq(&mut state, b).expect("calc_eq should succeed");
    // Should have two subgoals: a = b, b = c
    assert_eq!(state.goals().len(), 2);

    // Verify subgoal targets (not just count) — matches trans test pattern at core.rs:2413
    let eq_levels = vec![Level::succ(Level::zero())];
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let a_ref = Expr::const_(Name::from_string("a"), vec![]);
    let b_ref = Expr::const_(Name::from_string("b"), vec![]);
    let c_ref = Expr::const_(Name::from_string("c"), vec![]);
    // Goal 1: @Eq Nat a b
    let expected_goal1 = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), eq_levels.clone()),
                nat_ref.clone(),
            ),
            a_ref,
        ),
        b_ref.clone(),
    );
    // Goal 2: @Eq Nat b c
    let expected_goal2 = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), eq_levels), nat_ref),
            b_ref,
        ),
        c_ref,
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_goal1,
        "goal1 should be a = b"
    );
    assert_eq!(
        state.goals()[1].target,
        expected_goal2,
        "goal2 should be b = c"
    );
}

/// Regression test for #2154 goal-decomposition: calc_eq must assign a
/// composite Eq.trans proof to the original goal's metavariable so it is
/// not orphaned when subgoals are pushed.
#[test]
fn test_calc_eq_assigns_proof_to_original_meta() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Goal: a = c
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a,
        ),
        c,
    );
    let mut state = ProofState::new(env, eq_goal);

    let original_meta = state.current_goal().unwrap().meta_id;

    calc_eq(&mut state, b).expect("calc_eq should succeed");

    // The original goal's metavariable MUST be assigned (Eq.trans proof)
    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2154: calc_eq pops goal without assigning proof term — \
         original metavariable should be assigned via Eq.trans"
    );

    // Should still have two subgoals
    assert_eq!(state.goals.len(), 2);
}

// =========================================================================
// wlog Tests
// =========================================================================

#[test]
fn test_wlog_creates_two_goals() {
    let env = setup_env_with_and_or();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let assumption = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, target);

    wlog(&mut state, "h", assumption).expect("wlog should succeed");
    // Should create 2 goals: target with h : assumption, target with h_neg : ¬assumption
    assert_eq!(state.goals.len(), 2);
}

/// Regression test for #2189: wlog must assign a proof term to the original
/// goal's metavariable connecting the two sub-goals via Or.elim/Classical.em.
#[test]
fn test_wlog_assigns_proof_to_original_meta() {
    let env = setup_env_with_and_or();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let assumption = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, target);

    let original_meta = state.current_goal().unwrap().meta_id;

    wlog(&mut state, "h", assumption).expect("wlog should succeed");

    // The original goal's metavariable MUST be assigned (Or.elim proof)
    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2189: wlog pops goal without assigning proof term — \
         original metavariable should be assigned via Or.elim(Classical.em ...)"
    );
}

/// Regression test for #2189: convert Strategy 2 must assign a proof term
/// to the original goal's metavariable using Eq.mpr.
#[test]
fn test_convert_strategy2_assigns_proof_to_original_meta() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    // Goal: ⊢ A, proof term has type B — types differ, Strategy 2 kicks in
    let target_a = Expr::const_(Name::from_string("A"), vec![]);
    // Add a proof of type B
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b_proof"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .unwrap();
    let b_proof = Expr::const_(Name::from_string("b_proof"), vec![]);

    let mut state = ProofState::new(env, target_a);
    let original_meta = state.current_goal().unwrap().meta_id;

    // convert with a proof of type B when goal is A — forces Strategy 2
    let result = convert(&mut state, b_proof);
    assert!(result.is_ok(), "convert Strategy 2 should succeed");

    // The original goal's metavariable MUST be assigned (Eq.mpr proof)
    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2189: convert Strategy 2 pops goal without assigning proof term — \
         original metavariable should be assigned via Eq.mpr"
    );

    // Should have one subgoal: prove A = B
    assert_eq!(
        state.goals.len(),
        1,
        "convert Strategy 2 should create exactly 1 subgoal (type equality)"
    );
}

/// Regression test for #2154 goal-decomposition: convert Strategy 1 must assign
/// a composite Eq.trans proof to the original goal's metavariable when both
/// target and proof are equalities with differing components.
#[test]
fn test_convert_strategy1_assigns_proof_to_original_meta() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Declare type N and constants a, b, c, d : N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    let n = Expr::const_(Name::from_string("N"), vec![]);

    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: n.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Helper: @Eq N lhs rhs
    let mk_eq = |lhs: &Expr, rhs: &Expr| -> Expr {
        Expr::app(
            Expr::app(Expr::app(eq_const.clone(), n.clone()), lhs.clone()),
            rhs.clone(),
        )
    };

    // Goal: a = d (target), proof term has type: b = c (both components differ)
    let goal_target = mk_eq(&a, &d);
    let proof_type_expr = mk_eq(&b, &c);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h_bc"),
        level_params: vec![],
        type_: proof_type_expr,
    })
    .unwrap();
    let proof_term = Expr::const_(Name::from_string("h_bc"), vec![]);

    let mut state = ProofState::new(env, goal_target);
    let original_meta = state.current_goal().unwrap().meta_id;

    let result = convert(&mut state, proof_term);
    assert!(
        result.is_ok(),
        "convert Strategy 1 (both sides differ) should succeed: {:?}",
        result.err()
    );

    // Original meta MUST be assigned (composite Eq.trans proof)
    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2154: convert Strategy 1 pops goal without assigning proof term — \
         original metavariable should be assigned via Eq.trans composite"
    );

    // Should have 2 subgoals: a = b, d = c
    assert_eq!(
        state.goals.len(),
        2,
        "convert Strategy 1 should create 2 subgoals when both LHS and RHS differ"
    );
}

/// Regression test for #2154: convert Strategy 1 with only LHS differing
/// must assign Eq.trans proof to the original meta.
#[test]
fn test_convert_strategy1_lhs_only_assigns_meta() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    let n = Expr::const_(Name::from_string("N"), vec![]);

    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: n.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mk_eq = |lhs: &Expr, rhs: &Expr| -> Expr {
        Expr::app(
            Expr::app(Expr::app(eq_const.clone(), n.clone()), lhs.clone()),
            rhs.clone(),
        )
    };

    // Goal: a = c, proof: b = c (only LHS differs)
    let goal_target = mk_eq(&a, &c);
    let proof_type_expr = mk_eq(&b, &c);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h_bc"),
        level_params: vec![],
        type_: proof_type_expr,
    })
    .unwrap();
    let proof_term = Expr::const_(Name::from_string("h_bc"), vec![]);

    let mut state = ProofState::new(env, goal_target);
    let original_meta = state.current_goal().unwrap().meta_id;

    let result = convert(&mut state, proof_term);
    assert!(
        result.is_ok(),
        "convert Strategy 1 (LHS only) should succeed: {:?}",
        result.err()
    );

    assert!(
        state.metas.is_assigned(original_meta),
        "BUG #2154: convert Strategy 1 (LHS only) must assign original meta via Eq.trans"
    );

    // Only 1 subgoal: a = b
    assert_eq!(
        state.goals.len(),
        1,
        "convert Strategy 1 (LHS only) should create 1 subgoal"
    );

    // Verify subgoal target is a = b
    let expected_subgoal = mk_eq(&a, &b);
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_subgoal,
        "subgoal should be a = b"
    );
}

/// Regression test for #2214: convert must use goal's local context for type inference.
///
/// Before the fix, `convert(state, Expr::fvar(h))` where `h` is a hypothesis
/// would fail with "cannot infer type of proof term" because the TypeChecker
/// was created without the goal's local context, so it couldn't resolve the FVar.
#[test]
fn test_convert_with_hypothesis_fvar() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Create a hypothesis h : A in the goal context
    let h_fvar = FVarId::new(1);
    let local_decl = LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    // Goal: ⊢ A with hypothesis h : A
    let mut state = ProofState::with_context(env, a_ty, vec![local_decl]);

    // Use hypothesis as proof term via FVar — this is what `convert h` does
    let proof_term = Expr::fvar(h_fvar);
    convert(&mut state, proof_term)
        .expect("BUG #2214: convert should resolve FVar hypothesis from goal context");

    assert_eq!(
        state.goals.len(),
        0,
        "convert with exact hypothesis should close the goal"
    );
}

/// Regression test for #2214: convert_hyp must resolve hypothesis names.
///
/// This tests the full `convert h` path via convert_hyp, ensuring the
/// hypothesis lookup + FVar resolution works end-to-end with local context.
#[test]
fn test_convert_hyp_with_local_hypothesis() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let h_fvar = FVarId::new(1);
    let local_decl = LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    // Goal: ⊢ A with hypothesis h : A
    let mut state = ProofState::with_context(env, a_ty, vec![local_decl]);

    convert_hyp(&mut state, "h")
        .expect("BUG #2214: convert_hyp should resolve named hypothesis from goal context");

    assert_eq!(
        state.goals.len(),
        0,
        "convert_hyp with exact hypothesis should close the goal"
    );
}

// =========================================================================
// push_neg_at Tests
// =========================================================================

#[test]
fn test_push_neg_at_not_found() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = push_neg_at(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

#[test]
fn test_push_negations_double_neg() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone());
    let not_not_p = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), not_p);

    let result = push_negations_in_expr(&not_not_p);
    assert_eq!(result, p);
}

#[test]
fn test_push_negations_de_morgan_and() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // ¬(P ∧ Q)
    let p_and_q = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p.clone()),
        q.clone(),
    );
    let not_p_and_q = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_and_q);

    let result = push_negations_in_expr(&not_p_and_q);
    // Should be ¬P ∨ ¬Q
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "Or");
    } else {
        panic!("Expected Or");
    }
}

#[test]
fn test_push_negations_de_morgan_or() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // ¬(P ∨ Q)
    let p_or_q = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p.clone()),
        q.clone(),
    );
    let not_p_or_q = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_or_q);

    let result = push_negations_in_expr(&not_p_or_q);
    // Should be ¬P ∧ ¬Q
    let head = result.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "And");
    } else {
        panic!("Expected And");
    }
}

#[test]
fn test_contrapose_hyp_uses_local_proof_carry() {
    let mut env = setup_env_with_prop_ext();
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
    let old_h_fvar = FVarId::new(100);
    let initial_target = p.clone();
    let mut state = ProofState::with_context(
        env,
        initial_target.clone(),
        vec![LocalDecl {
            fvar: old_h_fvar,
            name: "h".to_string(),
            ty: Expr::arrow(p.clone(), q.clone()),
            value: None,
        }],
    );
    let initial_meta = state.current_goal().unwrap().meta_id;

    contrapose_hyp(&mut state, "h").expect("contrapose_hyp should succeed");

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain visible");
    assert_ne!(h.fvar, old_h_fvar);
    assert_eq!(
        h.ty,
        Expr::arrow(
            Expr::arrow(q, Expr::const_(Name::from_string("False"), vec![])),
            Expr::arrow(p, Expr::const_(Name::from_string("False"), vec![])),
        )
    );
    assert_eq!(
        goal.target, initial_target,
        "contrapose_hyp should not rewrite the target"
    );
    assert!(
        state.metas().is_assigned(initial_meta),
        "proof-carry local replacement should close the old goal"
    );
}

// =========================================================================
// norm_num_at Tests
// =========================================================================

#[test]
fn test_norm_num_at_not_found() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = norm_num_at(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

#[test]
fn test_normalize_numerals_literal() {
    let five = Expr::nat_lit(5);
    let result = normalize_numerals(&five);
    assert_eq!(result, five);
}

#[test]
fn test_norm_num_at_uses_defeq_local_replacement() {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_nat().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
    let lhs = Expr::app(Expr::app(nat_add, Expr::nat_lit(2)), Expr::nat_lit(3));
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            lhs,
        ),
        Expr::nat_lit(5),
    );

    let old_h_fvar = FVarId::new(100);
    let mut state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar: old_h_fvar,
            name: "h".to_string(),
            ty: eq_ty,
            value: None,
        }],
    );
    let initial_meta = state.current_goal().unwrap().meta_id;

    norm_num_at(&mut state, "h").expect("norm_num_at should succeed on defeq arithmetic");

    let h = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain visible");
    assert_ne!(h.fvar, old_h_fvar);
    assert_eq!(
        h.ty,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat_ty,
                ),
                Expr::nat_lit(5),
            ),
            Expr::nat_lit(5),
        )
    );
    assert!(
        state.metas().is_assigned(initial_meta),
        "defeq local replacement should close the old goal"
    );
}

#[test]
fn test_norm_num_at_fails_closed_on_non_defeq_rewrite() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    let bad_ty = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add_comm"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(3),
    );
    let old_h_fvar = FVarId::new(100);
    let mut state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar: old_h_fvar,
            name: "h".to_string(),
            ty: bad_ty.clone(),
            value: None,
        }],
    );
    let initial_meta = state.current_goal().unwrap().meta_id;

    let result = norm_num_at(&mut state, "h");
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "non-defeq arithmetic rewrites must fail closed, got: {result:?}"
    );
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx[0].fvar, old_h_fvar);
    assert_eq!(goal.local_ctx[0].ty, bad_ty);
    assert!(
        !state.metas().is_assigned(initial_meta),
        "failed norm_num_at must not assign the original goal"
    );
}

#[test]
fn test_extract_nat_literal_extended() {
    let five = Expr::nat_lit(5);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let unknown = Expr::const_(Name::from_string("unknown"), vec![]);

    assert_eq!(extract_nat_literal(&five), Some(5));
    assert_eq!(extract_nat_literal(&zero), Some(0));
    // unknown names that aren't parseable as numbers return None
    assert_eq!(extract_nat_literal(&unknown), None);
}

// =========================================================================
// suffices_to_show Tests
// =========================================================================

#[test]
fn test_suffices_to_show() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);

    // Need continuation proof B → A, but "cont" is not declared in env
    let cont = Expr::const_(Name::from_string("cont"), vec![]);
    // Should fail: "cont" is undeclared, so type inference fails
    let err = suffices_to_show(&mut state, b, Some(cont)).unwrap_err();
    assert!(matches!(err, TacticError::TypeCheckFailed(_) | TacticError::InvalidTarget { .. }),
        "suffices_to_show with undeclared continuation should produce TypeCheckFailed or InvalidTarget, got: {err}");
}

// NOTE: Search tactics tests moved to search_tactics.rs (#1150)
