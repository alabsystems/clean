// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::cert::ProofCert;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::mode::CleanMode;

#[test]
fn test_exact_simple() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // exact a
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    exact(&mut state, proof).unwrap();

    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "completed proof state should have a proof term"
    );
}

#[test]
fn test_exact_wrong_type() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    // Try exact a (but target is B, not A)
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    let result = exact(&mut state, proof);

    assert!(matches!(result, Err(TacticError::TypeMismatch { .. })));
    assert!(!state.is_complete());
}

#[test]
fn test_intro_basic() {
    let env = setup_env();

    // Goal: A → A
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);

    // intro x
    intro(&mut state, "x").unwrap();

    // Now the goal should be A with x : A in context
    assert!(!state.is_complete());
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, "x");
}

#[test]
fn test_intro_and_assumption() {
    let env = setup_env();

    // Goal: A → A
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);

    // intro x
    intro(&mut state, "x").unwrap();

    // assumption (finds x : A)
    assumption(&mut state).unwrap();

    assert!(state.is_complete());
}

#[test]
fn test_apply_basic() {
    let env = setup_env();

    // Goal: B
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    // apply f (where f : A → B)
    let f = Expr::const_(Name::from_string("f"), vec![]);
    apply(&mut state, f).unwrap();

    // New goal should be A
    assert!(!state.is_complete());
    let goal = state.current_goal().unwrap();
    assert!(matches!(goal.target.kind(), ExprKind::Const(n, _) if n.to_string() == "A"));
}

#[test]
fn test_apply_then_exact() {
    let env = setup_env();

    // Goal: B
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    // apply f
    let f = Expr::const_(Name::from_string("f"), vec![]);
    apply(&mut state, f).unwrap();

    // exact a
    let a = Expr::const_(Name::from_string("a"), vec![]);
    exact(&mut state, a).unwrap();

    assert!(state.is_complete());

    // The proof should be (f a)
    let proof = state.instantiated_proof().unwrap();
    match proof.kind() {
        ExprKind::App(func, arg) => {
            assert!(matches!(func.kind(), ExprKind::Const(n, _) if n.to_string() == "f"));
            assert!(matches!(arg.kind(), ExprKind::Const(n, _) if n.to_string() == "a"));
        }
        _ => panic!("expected App, got {proof:?}"),
    }
}

#[test]
fn test_intros() {
    let env = setup_env();

    // Goal: A → B → A
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a));

    let mut state = ProofState::new(env, target);

    // intros x y
    intros(&mut state, vec!["x".to_string(), "y".to_string()]).unwrap();

    // Now goal is A with x : A, y : B in context
    assert!(!state.is_complete());
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 2);
    assert_eq!(goal.local_ctx[0].name, "x");
    assert_eq!(goal.local_ctx[1].name, "y");
}

#[test]
fn test_complex_proof() {
    let env = setup_env();

    // Goal: A → B → A (prove by intro x, intro y, exact x)
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a));

    let mut state = ProofState::new(env, target);

    // intro x
    intro(&mut state, "x").unwrap();
    // intro y
    intro(&mut state, "y").unwrap();
    // assumption (finds x : A)
    assumption(&mut state).unwrap();

    assert!(state.is_complete());

    // The proof should be fun x y => x
    let proof = state.instantiated_proof().unwrap();

    // Verify the proof has the expected structure (nested lambdas)
    // The exact de Bruijn index depends on how intro/assumption abstracts
    assert!(
        matches!(proof.kind(), ExprKind::Lam(_, _, _)),
        "expected outer lambda, got {proof:?}"
    );

    // Type-check the proof to validate it's correct
    let tc = TypeChecker::new(state.env());
    let proof_ty = tc.infer_type(&proof).unwrap();

    // The proof type should be A → B → A
    assert!(
        matches!(proof_ty.kind(), ExprKind::Pi(_, _, _)),
        "proof type should be Pi, got {proof_ty:?}"
    );
}

// =========================================================================
// check_type verification of completed proofs (#2200, #2197)
// =========================================================================

/// Verify that a multi-binder proof (A → B → A) passes check_type against
/// its original goal type. Exercises both:
/// - fix_pi_leaked_fvars for nested Lambda binders (#2197)
/// - check_type verification path (#2200)
#[test]
fn test_multi_binder_proof_check_type_correct() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a));

    let mut state = ProofState::new(env.clone(), target.clone());
    intro(&mut state, "x").unwrap();
    intro(&mut state, "y").unwrap();
    assumption(&mut state).unwrap();

    assert!(state.is_complete(), "proof should be complete");
    let proof = state.instantiated_proof().unwrap();

    // check_type must succeed: proof inhabits the goal type
    let tc = TypeChecker::new(&env);
    assert!(
        tc.check_type(&proof, &target).is_ok(),
        "well-typed proof of correct goal should pass check_type"
    );
}

/// Verify that a well-typed proof of A → B → A does NOT pass check_type
/// against a different goal type (B → A → B). This tests the #2200 fix:
/// check_type rejects proofs whose inferred type doesn't match the target.
#[test]
fn test_multi_binder_proof_check_type_wrong_target() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b.clone(), a.clone()));

    let mut state = ProofState::new(env.clone(), target);
    intro(&mut state, "x").unwrap();
    intro(&mut state, "y").unwrap();
    assumption(&mut state).unwrap();

    let proof = state.instantiated_proof().unwrap();

    // check_type must FAIL against wrong target: B → A → B
    let wrong_target = Expr::arrow(b.clone(), Expr::arrow(a, b));
    let tc = TypeChecker::new(&env);
    assert!(
        tc.check_type(&proof, &wrong_target).is_err(),
        "proof of A→B→A must NOT pass check_type against B→A→B"
    );
}

/// Verify that goal_type() returns the original target, not a modified one.
/// This is the invariant that the #2200 verification path depends on.
#[test]
fn test_goal_type_stable_after_tactics() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a.clone()));

    let mut state = ProofState::new(env.clone(), target.clone());

    // Before tactics: goal_type should match target
    let gt = state.goal_type().expect("goal_type should exist");
    {
        let tc = TypeChecker::new(state.env());
        assert!(
            tc.is_def_eq(&gt, &target),
            "goal_type before tactics should match target"
        );
    }

    // After intro: goal_type should still match original target (MetaId(0) type)
    intro(&mut state, "x").unwrap();
    let gt2 = state.goal_type().expect("goal_type should still exist");
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&gt2, &target),
        "goal_type after intro should still match original target"
    );
}

// =========================================================================
// Cases tactic tests
// =========================================================================

fn setup_env_with_bool() -> Environment {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env
}

#[test]
fn test_cases_bool_creates_two_goals() {
    let env = setup_env_with_bool();

    // Goal: Bool → Bool
    // After "intro b; cases b" we should have two goals for false and true
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro b
    intro(&mut state, "b").unwrap();

    // Verify we have one goal with hypothesis b : Bool
    assert!(!state.is_complete());
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, "b");

    // cases b
    cases(&mut state, "b").unwrap();

    // Should now have 2 goals (one for false, one for true)
    assert_eq!(
        state.goals().len(),
        2,
        "cases on Bool should produce 2 goals"
    );
}

#[test]
fn test_cases_bool_proof_completion() {
    let env = setup_env_with_bool();

    // Goal: Bool → Bool (identity function via cases)
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro b
    intro(&mut state, "b").unwrap();

    // cases b
    cases(&mut state, "b").unwrap();

    // Now we should have 2 goals, each of type Bool
    assert_eq!(state.goals().len(), 2);

    // For false case: exact Bool.false
    let false_const = Expr::const_(Name::from_string("Bool.false"), vec![]);
    exact(&mut state, false_const).unwrap();

    // For true case: exact Bool.true
    let true_const = Expr::const_(Name::from_string("Bool.true"), vec![]);
    exact(&mut state, true_const).unwrap();

    // Should be complete now
    assert!(
        state.is_complete(),
        "proof should be complete after handling both cases"
    );
}

#[test]
fn test_cases_nonexistent_hypothesis() {
    let env = setup_env_with_bool();

    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = bool_ty;

    let mut state = ProofState::new(env, target);

    // Try cases on a hypothesis that doesn't exist
    let result = cases(&mut state, "nonexistent");

    match result {
        Err(TacticError::UnknownIdent(name)) => {
            assert_eq!(name, "nonexistent");
        }
        _ => panic!("expected UnknownIdent error"),
    }
}

// =========================================================================
// Induction tactic tests
// =========================================================================

#[test]
fn test_induction_nat_creates_two_goals() {
    let env = setup_env_with_nat();

    // Goal: Nat → Nat
    // After "intro n; induction n" we should have two goals:
    // - Base case for zero
    // - Inductive case for succ with IH
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro n
    intro(&mut state, "n").unwrap();

    // Verify we have one goal with hypothesis n : Nat
    assert!(!state.is_complete());
    let goal = state.current_goal().unwrap();
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, "n");

    // induction n
    induction(&mut state, "n").unwrap();

    // Should now have 2 goals (one for zero, one for succ)
    assert_eq!(
        state.goals().len(),
        2,
        "induction on Nat should produce 2 goals"
    );
}

#[test]
fn test_induction_nat_has_ih_in_succ_case() {
    let env = setup_env_with_nat();

    // Goal: Nat → Nat
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro n
    intro(&mut state, "n").unwrap();

    // induction n
    induction(&mut state, "n").unwrap();

    // Check that we have 2 goals
    assert_eq!(state.goals().len(), 2);

    // First goal (zero case) should have empty context (original n was removed)
    let zero_goal = &state.goals()[0];
    assert!(
        zero_goal.local_ctx.is_empty(),
        "zero case should have no hypotheses"
    );

    // Second goal (succ case) should have:
    // - succ_0 : Nat (the predecessor)
    // - ih_succ_0 : Nat (the induction hypothesis - goal with succ_0)
    let succ_goal = &state.goals()[1];
    assert!(
        succ_goal.local_ctx.len() >= 2,
        "succ case should have at least 2 hypotheses (field and IH), got {}",
        succ_goal.local_ctx.len()
    );

    // Find the IH hypothesis
    let ih_hyp = succ_goal
        .local_ctx
        .iter()
        .find(|d| d.name.starts_with("ih_"));
    assert!(ih_hyp.is_some(), "succ case should have an IH hypothesis");
}

#[test]
fn test_induction_nat_proof_completion() {
    let env = setup_env_with_nat();

    // Goal: Nat → Nat (identity function via induction)
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro n
    intro(&mut state, "n").unwrap();

    // induction n
    induction(&mut state, "n").unwrap();

    assert_eq!(state.goals().len(), 2);

    // Zero case: exact Nat.zero
    let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    exact(&mut state, zero_const).unwrap();

    // Succ case: we need to prove Nat when we have succ_0 : Nat and ih_succ_0 : Nat
    // We can use Nat.succ applied to the predecessor field
    let succ_goal = state.current_goal().unwrap().clone();

    // Find the predecessor field
    let pred_field = succ_goal
        .local_ctx
        .iter()
        .find(|d| d.name.starts_with("succ_"))
        .expect("should have succ field");

    // Use Nat.succ pred_field
    let succ_const = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_app = Expr::app(succ_const, Expr::fvar(pred_field.fvar));
    exact(&mut state, succ_app).unwrap();

    assert!(
        state.is_complete(),
        "proof should be complete after handling both cases"
    );
}

#[test]
fn test_induction_nat_using_ih() {
    let env = setup_env_with_nat();

    // Goal: Nat → Nat
    // This time we'll use the IH directly
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);

    intro(&mut state, "n").unwrap();
    induction(&mut state, "n").unwrap();

    // Zero case: exact Nat.zero
    let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    exact(&mut state, zero_const).unwrap();

    // Succ case: use the IH directly (since target is Nat and IH : Nat)
    let succ_goal = state.current_goal().unwrap().clone();

    // Find the IH
    let ih_hyp = succ_goal
        .local_ctx
        .iter()
        .find(|d| d.name.starts_with("ih_"))
        .expect("should have IH");

    // Use the IH directly as the proof term
    exact(&mut state, Expr::fvar(ih_hyp.fvar)).unwrap();

    assert!(state.is_complete());
}

#[test]
fn test_induction_nonexistent_hypothesis() {
    let env = setup_env_with_nat();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = nat_ty;

    let mut state = ProofState::new(env, target);

    // Try induction on a hypothesis that doesn't exist
    let result = induction(&mut state, "nonexistent");

    match result {
        Err(TacticError::UnknownIdent(name)) => {
            assert_eq!(name, "nonexistent");
        }
        _ => panic!("expected UnknownIdent error"),
    }
}

#[test]
fn test_induction_bool_no_ih() {
    // Bool is not recursive, so induction should behave like cases
    let env = setup_env_with_bool();

    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());

    let mut state = ProofState::new(env, target);

    intro(&mut state, "b").unwrap();
    induction(&mut state, "b").unwrap();

    // Should have 2 goals
    assert_eq!(state.goals().len(), 2);

    // Neither goal should have IH since Bool constructors have no recursive fields
    for goal in state.goals() {
        let has_ih = goal.local_ctx.iter().any(|d| d.name.starts_with("ih_"));
        assert!(!has_ih, "Bool goals should not have IH");
    }
}

// =========================================================================
// Induction/cases with-clause alt.args renaming tests (#1836)
// =========================================================================

#[test]
fn test_induction_alt_args_renames_hypotheses() {
    // After induction on Nat, the succ case has auto-generated names:
    // succ_0 (field) and ih_succ_0 (IH). Verify that alt.args can rename them.
    let env = setup_env_with_nat();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);
    intro(&mut state, "n").unwrap();
    induction(&mut state, "n").unwrap();

    assert_eq!(state.goals().len(), 2);

    // The succ goal (index 1) should have succ_0 and ih_succ_0
    let succ_goal = &state.goals()[1];
    let tag = succ_goal.tag.as_deref().unwrap_or("");
    assert_eq!(tag, "succ");

    // Collect auto-generated field names (tag_N pattern)
    let tag_prefix = format!("{tag}_");
    let ih_prefix = format!("ih_{tag}_");
    let mut auto_indices: Vec<usize> = Vec::new();
    for (i, decl) in succ_goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&tag_prefix) {
            auto_indices.push(i);
        }
    }
    for (i, decl) in succ_goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&ih_prefix) {
            auto_indices.push(i);
        }
    }

    // Should have exactly 2 auto-generated hypotheses: succ_0 and ih_succ_0
    assert_eq!(
        auto_indices.len(),
        2,
        "succ case should have 2 auto-generated hypotheses (field + IH), got: {:?}",
        succ_goal
            .local_ctx
            .iter()
            .map(|d| d.name.as_str())
            .collect::<Vec<_>>()
    );

    // Simulate the renaming that eval_induction_alts now performs
    let mut goal = succ_goal.clone();
    let user_args = ["m".to_string(), "ih".to_string()];
    for (arg_idx, user_name) in user_args.iter().enumerate() {
        if arg_idx < auto_indices.len() {
            goal.local_ctx[auto_indices[arg_idx]].name = user_name.clone();
        }
    }

    // Verify the renamed hypotheses
    let has_m = goal.local_ctx.iter().any(|d| d.name == "m");
    let has_ih = goal.local_ctx.iter().any(|d| d.name == "ih");
    assert!(has_m, "field should be renamed to 'm'");
    assert!(has_ih, "IH should be renamed to 'ih'");

    // The old auto-generated names should be gone
    let has_succ_0 = goal.local_ctx.iter().any(|d| d.name == "succ_0");
    let has_ih_succ_0 = goal.local_ctx.iter().any(|d| d.name == "ih_succ_0");
    assert!(!has_succ_0, "old name 'succ_0' should be gone after rename");
    assert!(
        !has_ih_succ_0,
        "old name 'ih_succ_0' should be gone after rename"
    );
}

#[test]
fn test_cases_alt_args_renames_fields() {
    // cases on Nat: zero case has no fields, succ case has succ_0
    let env = setup_env_with_nat();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);
    intro(&mut state, "n").unwrap();
    cases(&mut state, "n").unwrap();

    assert_eq!(state.goals().len(), 2);

    // succ case should have succ_0 (field only, no IH for cases)
    let succ_goal = &state.goals()[1];
    let tag = succ_goal.tag.as_deref().unwrap_or("");
    assert_eq!(tag, "succ");

    let tag_prefix = format!("{tag}_");
    let field_indices: Vec<usize> = succ_goal
        .local_ctx
        .iter()
        .enumerate()
        .filter(|(_, d)| d.name.starts_with(&tag_prefix))
        .map(|(i, _)| i)
        .collect();

    assert_eq!(
        field_indices.len(),
        1,
        "cases succ should have 1 field (succ_0)"
    );

    // Simulate renaming: | succ k =>
    let mut goal = succ_goal.clone();
    goal.local_ctx[field_indices[0]].name = "k".to_string();

    let has_k = goal.local_ctx.iter().any(|d| d.name == "k");
    assert!(has_k, "field should be renamed to 'k'");
}

#[test]
fn test_induction_alt_args_partial_rename() {
    // If user provides fewer args than available hypotheses, only the
    // first N are renamed and the rest keep auto-generated names.
    let env = setup_env_with_nat();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::arrow(nat_ty.clone(), nat_ty.clone());

    let mut state = ProofState::new(env, target);
    intro(&mut state, "n").unwrap();
    induction(&mut state, "n").unwrap();

    let succ_goal = &state.goals()[1];
    let tag = succ_goal.tag.as_deref().unwrap_or("");
    let tag_prefix = format!("{tag}_");
    let ih_prefix = format!("ih_{tag}_");
    let mut auto_indices: Vec<usize> = Vec::new();
    for (i, decl) in succ_goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&tag_prefix) {
            auto_indices.push(i);
        }
    }
    for (i, decl) in succ_goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&ih_prefix) {
            auto_indices.push(i);
        }
    }

    // Only rename the first arg (field), leave IH auto-generated
    let mut goal = succ_goal.clone();
    let user_args = ["m".to_string()]; // only 1 name for 2 hypotheses
    for (arg_idx, user_name) in user_args.iter().enumerate() {
        if arg_idx < auto_indices.len() {
            goal.local_ctx[auto_indices[arg_idx]].name = user_name.clone();
        }
    }

    let has_m = goal.local_ctx.iter().any(|d| d.name == "m");
    let has_ih_auto = goal.local_ctx.iter().any(|d| d.name.starts_with("ih_"));
    assert!(has_m, "first arg should be renamed to 'm'");
    assert!(has_ih_auto, "IH should keep auto-generated name");
}

// =========================================================================
// SMT-based decide tactic tests
// =========================================================================

// setup_env_with_eq and make_eq are now shared helpers in tests/mod.rs

#[test]
fn test_decide_reflexivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // decide should prove reflexivity
    let result = decide(&mut state);
    assert!(result.is_ok(), "decide should prove a = a");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "decide should produce a proof term for a = a"
    );
}

#[test]
fn test_decide_with_hypothesis() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Setup: we have a hypothesis h : a = b
    let hyp_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let local_decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: hyp_ty,
        value: None,
    };

    // Goal: b = a (symmetry)
    let target = make_eq(a_ty, b, a);

    let mut state = ProofState::with_context(env, target, vec![local_decl]);

    // decide should prove b = a from h : a = b
    let result = decide(&mut state);
    assert!(result.is_ok(), "decide should prove b = a from h : a = b");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "decide should produce a proof term for symmetry"
    );
}

#[test]
fn test_decide_transitivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Hypotheses: h1 : a = b, h2 : b = c
    let hyp1 = LocalDecl {
        fvar: FVarId::new(0),
        name: "h1".to_string(),
        ty: make_eq(a_ty.clone(), a.clone(), b.clone()),
        value: None,
    };
    let hyp2 = LocalDecl {
        fvar: FVarId::new(1),
        name: "h2".to_string(),
        ty: make_eq(a_ty.clone(), b, c.clone()),
        value: None,
    };

    // Goal: a = c
    let target = make_eq(a_ty, a, c);

    let mut state = ProofState::with_context(env, target, vec![hyp1, hyp2]);

    // decide should prove transitivity
    let result = decide(&mut state);
    assert!(
        result.is_ok(),
        "decide should prove a = c from a = b, b = c"
    );
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "decide should produce a proof term for transitivity"
    );
}

#[test]
fn test_decide_congruence() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let fa = Expr::app(f.clone(), a.clone());
    let fb = Expr::app(f, b.clone());

    // Hypothesis: h : a = b
    let hyp = LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: make_eq(a_ty.clone(), a, b),
        value: None,
    };

    // Goal: f(a) = f(b)
    let target = make_eq(a_ty, fa, fb);

    let mut state = ProofState::with_context(env, target, vec![hyp]);

    // decide should prove congruence
    let result = decide(&mut state);
    assert!(result.is_ok(), "decide should prove f(a) = f(b) from a = b");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "decide should produce a proof term for congruence"
    );
}

#[test]
fn test_decide_cannot_prove_false() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: a = b (without any hypotheses)
    let target = make_eq(a_ty, a, b);

    let mut state = ProofState::new(env, target);

    // decide should NOT prove a = b without hypotheses
    let result = decide(&mut state);
    assert!(
        result.is_err(),
        "decide should not prove a = b without hypotheses"
    );
    assert!(!state.is_complete());
}

#[test]
fn test_decide_proof_uses_hypothesis_fvar() {
    // Test that the decide tactic produces proof terms that reference
    // the actual hypothesis free variables from the context
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Setup: hypothesis h : a = b with FVarId 42
    let hyp_fvar = FVarId::new(42);
    let hyp_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let local_decl = LocalDecl {
        fvar: hyp_fvar,
        name: "h".to_string(),
        ty: hyp_ty,
        value: None,
    };

    // Goal: a = b (same as hypothesis, should use h directly)
    let target = make_eq(a_ty, a, b);

    let mut state = ProofState::with_context(env, target, vec![local_decl]);

    // decide should prove and produce a proof term
    let result = decide(&mut state);
    assert!(result.is_ok(), "decide should prove a = b from h : a = b");
    assert!(state.is_complete());

    // Get the proof term and verify it uses the hypothesis
    let proof = state
        .instantiated_proof()
        .expect("decide should produce a proof term");
    assert!(
        !proof.has_sorry(),
        "direct hypothesis proof must not fall back to sorry: {proof:?}"
    );
    let proof_fvars = collect_fvars(&proof);
    assert_eq!(
        proof_fvars.len(),
        1,
        "direct hypothesis proof should mention exactly one local hypothesis: {proof:?}"
    );
    assert!(
        proof_fvars.contains(&hyp_fvar),
        "proof should reference hypothesis FVarId::new(42): {proof:?}"
    );
    match proof.kind() {
        ExprKind::FVar(fvar) => {
            assert_eq!(
                *fvar, hyp_fvar,
                "proof should be the direct hypothesis FVarId::new(42)"
            );
        }
        other => {
            panic!("unexpected proof structure from decide (expected FVar(42)): {other:?}");
        }
    }
}

#[test]
fn test_decide_symmetry_proof_structure() {
    // Test that symmetry proofs are constructed correctly
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Hypothesis: h : a = b
    let hyp_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "h".to_string(),
        ty: hyp_ty,
        value: None,
    };

    // Goal: b = a (needs symmetry)
    let target = make_eq(a_ty, b, a);

    let mut state = ProofState::with_context(env, target, vec![local_decl]);

    let result = decide(&mut state);
    assert!(result.is_ok(), "decide should prove b = a from h : a = b");
    assert!(state.is_complete());

    // Check that a proof was produced and has meaningful structure
    let proof = state
        .instantiated_proof()
        .expect("should have a proof term");
    assert!(
        !proof.has_sorry(),
        "symmetry proof must not fall back to sorry: {proof:?}"
    );
    let proof_fvars = collect_fvars(&proof);
    assert_eq!(
        proof_fvars.len(),
        1,
        "symmetry proof should mention exactly one hypothesis: {proof:?}"
    );
    assert!(
        proof_fvars.contains(&FVarId::new(1)),
        "symmetry proof should reference h : a = b: {proof:?}"
    );
    match proof.kind() {
        ExprKind::App(_, _) => {
            let head = proof.get_app_fn();
            assert!(
                matches!(head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq.symm")),
                "symmetry proof should be rooted at Eq.symm, got: {proof:?}"
            );
            let args = proof.get_app_args();
            assert_eq!(
                args.len(),
                4,
                "Eq.symm proof should have type, lhs, rhs, and proof arguments: {proof:?}"
            );
            assert!(
                matches!(args[3].kind(), ExprKind::FVar(fvar) if *fvar == FVarId::new(1)),
                "Eq.symm proof should use h as its final argument: {proof:?}"
            );
        }
        other => {
            panic!(
                "unexpected proof structure for symmetry (expected Eq.symm application): {other:?}"
            );
        }
    }
}

// =========================================================================
// Certificate integration tests for ProofState
// =========================================================================

#[test]
fn test_proof_state_create_cert_verifier() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap();

    // Should succeed with empty local context
    let _verifier = state
        .create_cert_verifier(goal)
        .expect("create_cert_verifier should succeed with empty local context");
}

#[test]
fn test_proof_state_create_cert_verifier_with_context() {
    let env = setup_env();

    // Create a proof state with local hypotheses
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "x".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    let target = a_ty.clone();
    let state = ProofState::with_context(env, target, vec![local_decl]);
    let goal = state.current_goal().unwrap();

    let mut verifier = state
        .create_cert_verifier(goal)
        .expect("create_cert_verifier should register local hypotheses");
    let inferred_type = verifier
        .verify(
            &ProofCert::FVar {
                id: FVarId::new(1),
                type_: Box::new(a_ty.clone()),
            },
            &Expr::fvar(FVarId::new(1)),
        )
        .expect("registered local fvar should verify");
    assert_eq!(inferred_type, a_ty);
}

#[test]
fn test_proof_state_create_cert_verifier_uses_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let target = Expr::sort(Level::succ(Level::zero()));
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap();
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let mut verifier = state
        .create_cert_verifier(goal)
        .expect("create_cert_verifier should preserve cubical mode");
    let verified_ty = verifier
        .verify(&ProofCert::CubicalInterval, &interval)
        .expect("verifier should accept cubical interval in cubical mode");

    assert_eq!(verified_ty, Expr::sort(Level::succ(Level::zero())));
}

#[test]
fn test_proof_state_infer_type_with_cert() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "x".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    let target = a_ty.clone();
    let state = ProofState::with_context(env, target, vec![local_decl]);
    let goal = state.current_goal().unwrap();

    // Infer type of FVar(1) which is "x : A"
    let x_fvar = Expr::fvar(FVarId::new(1));
    let (ty, cert) = state
        .infer_type_with_cert(goal, &x_fvar)
        .expect("infer_type_with_cert should infer local hypothesis types");
    // x : A
    assert_eq!(ty, a_ty);
    assert!(matches!(cert, ProofCert::FVar { .. }));
}

#[test]
fn test_proof_state_infer_type_with_cert_uses_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let target = Expr::sort(Level::succ(Level::zero()));
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap();
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let (ty, cert) = state
        .infer_type_with_cert(goal, &interval)
        .expect("infer_type_with_cert should preserve cubical mode");

    assert_eq!(ty, Expr::sort(Level::succ(Level::zero())));
    assert!(matches!(cert, ProofCert::CubicalInterval));
}

#[test]
fn test_proof_state_verify_proof() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "x".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    // Goal: prove A with hypothesis x : A
    let target = a_ty.clone();
    let state = ProofState::with_context(env, target, vec![local_decl]);
    let goal = state.current_goal().unwrap();

    // The proof is just the FVar x
    let proof = Expr::fvar(FVarId::new(1));
    let cert = state
        .verify_proof(goal, &proof)
        .expect("verify_proof should accept a matching local hypothesis");
    assert!(matches!(cert, ProofCert::FVar { .. }));
}

#[test]
fn test_proof_state_verify_proof_type_mismatch() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "x".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    // Goal: prove B with hypothesis x : A (type mismatch)
    let target = b_ty;
    let state = ProofState::with_context(env, target, vec![local_decl]);
    let goal = state.current_goal().unwrap();

    // Try to use x as proof of B (should fail)
    let proof = Expr::fvar(FVarId::new(1));
    let result = state.verify_proof(goal, &proof);

    match result {
        Err(TacticError::TypeMismatch { .. }) => {}
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
fn test_proof_state_verify_proof_lambda() {
    let env = setup_env();

    // Goal: A -> A
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a_ty.clone(), a_ty.clone());

    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap();

    // Proof: fun (x : A) => x
    let proof = Expr::lam(BinderInfo::Default, a_ty, Expr::bvar(0));

    let cert = state
        .verify_proof(goal, &proof)
        .expect("lambda identity should verify against A -> A goal");
    assert!(matches!(cert, ProofCert::Lam { .. }));
}

// =========================================================================
// Certified tactic tests
// =========================================================================

#[test]
fn test_exact_with_cert() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // exact a (with certificate)
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    let cert = exact_with_cert(&mut state, proof)
        .expect("exact_with_cert should close goal when proof has matching type");
    assert!(state.is_complete());
    // Certificate should be for a constant
    assert!(matches!(cert, ProofCert::Const { .. }));
}

#[test]
fn test_intro_with_cert() {
    let env = setup_env();

    // Goal: A → A
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);

    // intro x (with certificate)
    let cert = intro_with_cert(&mut state, "x")
        .expect("intro_with_cert should introduce binder for function goals");
    assert!(!state.is_complete()); // Still have goal A to prove
                                   // Certificate is for the domain type (A : Type)
    assert!(matches!(cert, ProofCert::Const { .. }));
}

#[test]
fn test_intro_with_cert_prop() {
    let env = setup_env();

    // Goal: Prop → Prop
    let prop = Expr::prop();
    let target = Expr::arrow(prop.clone(), prop);

    let mut state = ProofState::new(env, target);

    // intro h (with certificate)
    let cert =
        intro_with_cert(&mut state, "h").expect("intro_with_cert should introduce Prop binders");
    // Certificate is for Prop : Type (Sort(0) : Sort(1))
    assert!(matches!(cert, ProofCert::Sort { .. }));
}

#[test]
fn test_assumption_with_cert() {
    let env = setup_env();

    // Goal: A with hypothesis x : A
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let local_decl = LocalDecl {
        fvar: FVarId::new(1),
        name: "x".to_string(),
        ty: a_ty.clone(),
        value: None,
    };

    let target = a_ty.clone();
    let mut state = ProofState::with_context(env, target, vec![local_decl]);

    // assumption (with certificate)
    let cert = assumption_with_cert(&mut state)
        .expect("assumption_with_cert should close goal from matching hypothesis");
    assert!(state.is_complete());
    // Certificate should be for FVar x : A
    assert!(matches!(cert, ProofCert::FVar { .. }));
}

#[test]
fn test_apply_with_cert() {
    let env = setup_env();

    // Goal: B (will apply f : A → B)
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, target);

    // apply f (with certificate)
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let cert = apply_with_cert(&mut state, f)
        .expect("apply_with_cert should transform goal using function type");
    assert!(!state.is_complete()); // Need to prove A
                                   // Certificate is for f : A → B
    assert!(matches!(cert, ProofCert::Const { .. }));
}

#[test]
fn test_certified_proof_chain() {
    use super::*;

    let env = setup_env();

    // Goal: A → A (prove with intro + assumption, collecting certs)
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);

    let mut state = ProofState::new(env, target);
    let mut certs = Vec::new();

    // intro x (with cert)
    let cert1 = intro_with_cert(&mut state, "x").unwrap();
    certs.push(cert1);

    // assumption (with cert)
    let cert2 = assumption_with_cert(&mut state).unwrap();
    certs.push(cert2);

    assert!(state.is_complete());
    assert_eq!(certs.len(), 2);

    // Both certificates should be valid
    assert!(matches!(certs[0], ProofCert::Const { .. })); // A : Type
    assert!(matches!(certs[1], ProofCert::FVar { .. })); // x : A
}

// =========================================================================
// Ay Integration tactic tests
// =========================================================================

#[test]
fn test_ay_config_default() {
    use crate::tactic::smt::SmtVerifyPolicy;

    let config = AyConfig::default();
    assert_eq!(config.timeout_ms(), Some(5000));
    assert!(!config.is_verbose());
    assert!(
        config.logic_override().is_none(),
        "default AyConfig should have no logic set"
    );
    assert!(!config.produces_proofs());
    assert_eq!(config.verify_policy(), SmtVerifyPolicy::TrustSolver);
}

#[test]
fn test_smt_verify_policy() {
    use crate::tactic::smt::SmtVerifyPolicy;

    // Test default is TrustSolver
    assert_eq!(SmtVerifyPolicy::default(), SmtVerifyPolicy::TrustSolver);

    // Test all variants exist and are distinct
    let policies = [
        SmtVerifyPolicy::TrustSolver,
        SmtVerifyPolicy::ExtractOnly,
        SmtVerifyPolicy::VerifyCarcara,
        SmtVerifyPolicy::VerifyStrict,
    ];

    for (i, p1) in policies.iter().enumerate() {
        for (j, p2) in policies.iter().enumerate() {
            if i == j {
                assert_eq!(p1, p2);
            } else {
                assert_ne!(p1, p2);
            }
        }
    }

    // Test Copy
    let policy = SmtVerifyPolicy::VerifyCarcara;
    let copied = policy;
    assert_eq!(policy, copied);
}

#[test]
fn test_ay_config_custom() {
    let config = AyConfig::default()
        .with_timeout_ms(10000)
        .verbose()
        .with_logic(clean_auto::bridge::ay_contract::AyLogic::QfLia)
        .enable_proofs();
    assert_eq!(config.timeout_ms(), Some(10000));
    assert!(config.is_verbose());
    assert_eq!(
        config.logic_override(),
        Some(clean_auto::bridge::ay_contract::AyLogic::QfLia)
    );
    assert!(config.produces_proofs());
}

#[cfg(feature = "ay-smt")]
#[test]
fn test_smt_solver_non_trust_policy_creates_verifiable() {
    use crate::tactic::smt::{SmtSolver, SmtVerifyPolicy};
    use clean_auto::bridge::ay_contract::AyLogic;

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyCarcara);
    let solver = SmtSolver::from_config(&config, AyLogic::QfLia);

    match solver {
        SmtSolver::Verifiable { policy, .. } => {
            assert_eq!(policy, SmtVerifyPolicy::VerifyCarcara);
        }
        _ => panic!("expected Verifiable solver"),
    }
}

/// Verify that SmtVerifyPolicy is correctly translated to ProofProfile on the
/// AyBackendConfig, so verify_proof_if_required() actually calls
/// verify_alethe_proof for tier 1+ policies. Part of #2427.
#[cfg(feature = "ay-smt")]
#[test]
fn test_smt_solver_policy_wires_proof_profile() {
    use crate::tactic::smt::{SmtSolver, SmtVerifyPolicy};
    use clean_auto::bridge::ay_contract::{AyLogic, ProofProfile};

    // VerifyCarcara → tier 1, all theories accepted
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyCarcara);
    let solver = SmtSolver::from_config(&config, AyLogic::QfLia);
    match &solver {
        SmtSolver::Verifiable { backend, .. } => {
            let profile = backend
                .config()
                .profile()
                .expect("VerifyCarcara should set proof_profile");
            assert_eq!(profile, &ProofProfile::carcara_verified());
            assert!(
                profile.accepts_all_theories(),
                "carcara_verified accepts all theories"
            );
        }
        _ => panic!("expected Verifiable"),
    }

    // VerifyStrict → tier 1, only verified theories
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict);
    let solver = SmtSolver::from_config(&config, AyLogic::QfLia);
    match &solver {
        SmtSolver::Verifiable { backend, .. } => {
            let profile = backend
                .config()
                .profile()
                .expect("VerifyStrict should set proof_profile");
            assert!(
                !profile.accepts_all_theories(),
                "VerifyStrict should restrict theories to the supported strict set"
            );
            assert!(profile.accepts_theory("QF_LIA"));
            assert!(profile.accepts_theory("QF_UF"));
            assert!(
                !profile.accepts_theory("QF_BV"),
                "BV should be rejected by strict profile"
            );
            assert!(
                !profile.accepts_theory("QF_UFLIA"),
                "combined logics should stay outside the current strict rollout"
            );
        }
        _ => panic!("expected Verifiable"),
    }

    // ExtractOnly → no proof profile (tier 0)
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let solver = SmtSolver::from_config(&config, AyLogic::QfLia);
    match &solver {
        SmtSolver::Verifiable { backend, .. } => {
            assert!(
                backend.config().profile().is_none(),
                "ExtractOnly should not set proof_profile"
            );
        }
        _ => panic!("expected Verifiable"),
    }
}

#[test]
fn test_ay_omega_reflexivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity - decidable by SMT)
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // ay_omega should prove reflexivity (falls back to native SMT)
    ay_omega(&mut state, AyConfig::default()).expect("ay_omega should prove reflexive equalities");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_omega should produce a proof term"
    );
}

#[test]
fn test_ay_omega_reflexivity_non_trust_policy() {
    use crate::tactic::smt::SmtVerifyPolicy;

    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let target = make_eq(a_ty, a.clone(), a);
    let mut state = ProofState::new(env, target);

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyCarcara);

    ay_omega(&mut state, config).expect("ay_omega should support non-trust verify policy");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_omega with VerifyCarcara should produce a proof term"
    );
}

#[test]
fn test_ay_bv_reflexivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity - decidable by SMT)
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // ay_bv should prove reflexivity (falls back to native SMT)
    ay_bv(&mut state, AyConfig::default()).expect("ay_bv should prove reflexive equalities");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_bv should produce a proof term"
    );
}

#[test]
fn test_ay_smt_reflexivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity - decidable by SMT)
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // ay_smt should prove reflexivity (falls back to native SMT)
    ay_smt(&mut state, AyConfig::default()).expect("ay_smt should prove reflexive equalities");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_smt should produce a proof term"
    );
}

#[test]
fn test_ay_decide_reflexivity() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (reflexivity - decidable by SMT)
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // ay_decide should prove reflexivity (falls back to native CDCL)
    ay_decide(&mut state, AyConfig::default())
        .expect("ay_decide should prove reflexive equalities");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_decide should produce a proof term"
    );
}

#[test]
fn test_ay_omega_with_hypothesis() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Hypothesis: a = b
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let h_fvar = FVarId::new(0);
    let h_decl = LocalDecl {
        fvar: h_fvar,
        name: "h".to_string(),
        ty: h_ty,
        value: None,
    };

    // Goal: a = b (provable with hypothesis)
    let target = make_eq(a_ty, a, b);

    let mut state = ProofState::with_context(env, target, vec![h_decl]);

    // ay_omega should prove using hypothesis
    ay_omega(&mut state, AyConfig::default())
        .expect("ay_omega should use hypotheses to close matching goals");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_omega with hypothesis should produce a proof term"
    );
}

#[test]
fn test_ay_smt_with_custom_logic() {
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);

    // Test with custom logic setting
    let config = AyConfig::default().with_logic(clean_auto::bridge::ay_contract::AyLogic::QfUf);

    ay_smt(&mut state, config).expect("ay_smt should run with explicit logic setting");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "ay_smt with custom logic should produce a proof term"
    );
}

// =========================================================================
// have tactic tests
// =========================================================================

#[test]
fn test_have_with_proof_adds_hypothesis() {
    // Setup: Goal is B, and we have a : A
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty.clone());

    // have h : A := a
    let result = have_(&mut state, "h", a_ty.clone(), Some(a));
    assert!(result.is_ok(), "have with proof should succeed");

    // Should still have 1 goal (the original B)
    assert_eq!(state.goals().len(), 1);

    // New goal should have h in context
    let new_goal = state.current_goal().unwrap();
    assert_eq!(new_goal.local_ctx.len(), 1);
    assert_eq!(new_goal.local_ctx[0].name, "h");

    // Goal should still be B
    assert!(matches!(new_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "B"));
}

#[test]
fn test_have_without_proof_creates_two_goals() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty.clone());

    // have h : A (without proof)
    let result = have_(&mut state, "h", a_ty.clone(), None);
    assert!(result.is_ok(), "have without proof should succeed");

    // Should have 2 goals
    assert_eq!(state.goals().len(), 2);

    // First goal should be: prove A
    let first_goal = &state.goals()[0];
    assert!(
        matches!(first_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "A"),
        "first goal should be A"
    );

    // Second goal should be: prove B with h : A available
    let second_goal = &state.goals()[1];
    assert!(
        matches!(second_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "B"),
        "second goal should be B"
    );
    assert_eq!(second_goal.local_ctx.len(), 1);
    assert_eq!(second_goal.local_ctx[0].name, "h");
}

#[test]
fn test_have_wrong_type_fails() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: A
    let mut state = ProofState::new(env, a_ty.clone());

    // have h : B := a (wrong - a has type A, not B)
    let result = have_(&mut state, "h", b_ty, Some(a));
    assert!(result.is_err(), "have with wrong type should fail");
}

#[test]
fn test_have_complete_proof() {
    // Prove B using have h : A := a, then apply f
    let env = setup_env();

    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // have h : A := a
    have_(&mut state, "h", a_ty, Some(a)).unwrap();

    // Now goal is still B with h : A in context
    // Apply f : A → B to get goal A
    apply(&mut state, f).unwrap();

    // Now we need to prove A - use h from context
    let h_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    exact(&mut state, Expr::fvar(h_fvar)).unwrap();

    assert!(state.is_complete(), "proof should be complete");
}

// =========================================================================
// suffices tactic tests
// =========================================================================

#[test]
fn test_suffices_with_proof_fn() {
    // Goal: B
    // suffices h : A by f (where f : A → B)
    // Should reduce to: just prove A
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // suffices h : A by f
    let result = suffices_(&mut state, "h", a_ty.clone(), Some(f));
    assert!(
        result.is_ok(),
        "suffices with valid proof fn should succeed"
    );

    // Should have 1 goal: prove A
    assert_eq!(state.goals().len(), 1);
    let goal = state.current_goal().unwrap();
    assert!(
        matches!(goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "A"),
        "goal should be A"
    );
}

#[test]
fn test_suffices_without_proof_fn() {
    // Goal: B
    // suffices h : A (without proof)
    // Should create: 1) prove A, 2) prove A → B
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty.clone());

    // suffices h : A (no proof function)
    let result = suffices_(&mut state, "h", a_ty.clone(), None);
    assert!(result.is_ok(), "suffices without proof fn should succeed");

    // Should have 2 goals
    assert_eq!(state.goals().len(), 2);

    // First goal: prove A
    let first_goal = &state.goals()[0];
    assert!(
        matches!(first_goal.target.kind(), ExprKind::Const(name, _) if name.to_string() == "A"),
        "first goal should be A"
    );

    // Second goal: prove A → B
    let second_goal = &state.goals()[1];
    match second_goal.target.kind() {
        ExprKind::Pi(_, domain, codomain) => {
            assert!(
                matches!(domain.kind(), ExprKind::Const(name, _) if name.to_string() == "A"),
                "domain should be A"
            );
            assert!(
                matches!(codomain.kind(), ExprKind::Const(name, _) if name.to_string() == "B"),
                "codomain should be B"
            );
        }
        _ => panic!("second goal should be A → B"),
    }
}

#[test]
fn test_suffices_wrong_type_fails() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // suffices h : A by a (wrong - a : A, not A → B)
    let result = suffices_(&mut state, "h", a_ty, Some(a));
    assert!(
        result.is_err(),
        "suffices with wrong proof type should fail"
    );
}

#[test]
fn test_suffices_complete_proof() {
    // Prove B using suffices + intro + exact
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal: B
    let mut state = ProofState::new(env, b_ty);

    // suffices h : A (no proof function)
    suffices_(&mut state, "h", a_ty, None).unwrap();

    // Goal 1: prove A
    exact(&mut state, a).unwrap();

    // Goal 2: prove A → B
    // intro to get h : A, then apply f h
    intro(&mut state, "h").unwrap();

    // Now goal is B with h : A in context
    // Apply f : A → B
    apply(&mut state, f).unwrap();

    // Goal is A, use h
    let h_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    exact(&mut state, Expr::fvar(h_fvar)).unwrap();

    assert!(state.is_complete(), "proof should be complete");
}

#[test]
fn test_suffices_no_goals_fails() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Create and immediately complete a state
    let mut state = ProofState::new(env, a_ty.clone());
    exact(&mut state, a.clone()).unwrap();

    // Now try suffices on completed proof
    let result = suffices_(&mut state, "h", a_ty, None);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "suffices on complete proof should fail with NoGoals"
    );
}

#[test]
fn test_have_no_goals_fails() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Create and immediately complete a state
    let mut state = ProofState::new(env, a_ty.clone());
    exact(&mut state, a.clone()).unwrap();

    // Now try have on completed proof
    let result = have_(&mut state, "h", a_ty, Some(a));
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "have on complete proof should fail with NoGoals"
    );
}

// =========================================================================
// Tests for tactic combinators
// =========================================================================

#[test]
fn test_try_tactic_succeeds_on_success() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: target,
            value: None,
        }],
    );

    // try assumption should succeed
    try_tactic(&mut state, assumption).unwrap();
    assert!(state.is_complete());
}

#[test]
fn test_try_tactic_succeeds_on_failure() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // try assumption should succeed even though assumption fails
    // (no hypothesis matches)
    try_tactic(&mut state, assumption).unwrap();
    assert!(!state.is_complete(), "state should be unchanged");
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_first_tactic_picks_first_success() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);

    let mut state = ProofState::new(env, target);

    // First assumption fails (no hyp), then exact(a) succeeds
    // Use boxed closures for heterogeneous tactics
    let tactics: Vec<Tactic> = vec![
        Box::new(assumption),
        Box::new(move |s| exact(s, a_expr.clone())),
    ];

    first_tactic(&mut state, tactics).unwrap();
    assert!(state.is_complete());
}

#[test]
fn test_first_tactic_all_fail() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, target);

    // All tactics fail - use boxed closures
    let tactics: Vec<Tactic> = vec![Box::new(assumption), Box::new(rfl)];

    let result = first_tactic(&mut state, tactics);
    assert!(result.is_err(), "first should fail when all tactics fail");
}

#[test]
fn test_first_tactic_last_branch_error_propagates() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let tactics: Vec<Tactic> = vec![Box::new(assumption), Box::new(rfl)];

    let result = first_tactic(&mut state, tactics);

    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "rfl"),
        "last branch should preserve its concrete error, got {result:?}"
    );
}

#[test]
fn test_first_tactic_stops_on_type_check_failure() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let a_expr = Expr::const_(Name::from_string("a"), vec![]);
    let mut state = ProofState::new(env, target);

    let tactics: Vec<Tactic> = vec![
        Box::new(|_| Err(TacticError::TypeCheckFailed("fatal".into()))),
        Box::new(move |s| exact(s, a_expr.clone())),
    ];

    let result = first_tactic(&mut state, tactics);

    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg == "fatal"),
        "fatal first-branch errors should stop immediately, got {result:?}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "fatal error should restore the original goal"
    );
    assert!(
        !state.is_complete(),
        "later branches must not run after a fatal error"
    );
}

#[test]
fn test_trivial_uses_assumption() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: target,
            value: None,
        }],
    );

    trivial(&mut state).unwrap();
    assert!(state.is_complete());
}

#[test]
fn test_trivial_fails_when_nothing_works() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = trivial(&mut state);
    assert!(result.is_err(), "trivial should fail with no hypotheses");
}

#[test]
fn test_focus_only_affects_first_goal() {
    let env = setup_env_with_and_or();

    // Create state with two goals (via split on And)
    let target = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("And"), vec![]),
            Expr::const_(Name::from_string("P"), vec![]),
        ),
        Expr::const_(Name::from_string("Q"), vec![]),
    );

    let mut state = ProofState::new(env, target);
    split_(&mut state).unwrap();
    assert_eq!(state.goals().len(), 2);

    // Focus on first goal and prove it
    focus(&mut state, |s| {
        exact(s, Expr::const_(Name::from_string("p"), vec![]))
    })
    .unwrap();

    // Should have one goal remaining (Q)
    assert_eq!(state.goals().len(), 1);
    assert_eq!(
        state.goals()[0].target,
        Expr::const_(Name::from_string("Q"), vec![])
    );
}

// =========================================================================
// solve_by_elim tests
// =========================================================================

#[test]
fn test_solve_by_elim_direct_match() {
    // Goal: A with hypothesis h : A
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let fvar_h = FVarId::new(100);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: fvar_h,
            name: "h".to_string(),
            ty: target,
            value: None,
        }],
    );

    solve_by_elim(&mut state, 5).unwrap();
    assert!(state.is_complete());
    // Direct match: proof should be an FVar (the hypothesis h : A)
    let proof = state
        .proof_term()
        .expect("solve_by_elim should produce a proof term");
    assert!(
        matches!(proof.kind(), ExprKind::FVar(_)),
        "direct match proof should be FVar, got: {proof:?}"
    );
}

#[test]
fn test_solve_by_elim_one_step() {
    // Goal: B with hypotheses h1 : A, h2 : A → B
    let env = setup_env();
    let type_a = Expr::const_(Name::from_string("A"), vec![]);
    let type_b = Expr::const_(Name::from_string("B"), vec![]);
    let fvar_h1 = FVarId::new(100);
    let fvar_h2 = FVarId::new(101);

    let mut state = ProofState::with_context(
        env,
        type_b.clone(),
        vec![
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: type_a.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: Expr::arrow(type_a, type_b),
                value: None,
            },
        ],
    );

    solve_by_elim(&mut state, 5).unwrap();
    assert!(state.is_complete());
    // One step: proof should be App(FVar(_), FVar(_)) i.e. h2(h1)
    let proof = state
        .proof_term()
        .expect("solve_by_elim should produce a proof term");
    assert!(
        matches!(proof.kind(), ExprKind::App(f, arg)
        if matches!(f.kind(), ExprKind::FVar(_))
        && matches!(arg.kind(), ExprKind::FVar(_))),
        "one-step proof should be App(FVar, FVar), got: {proof:?}"
    );
}

#[test]
fn test_solve_by_elim_chain() {
    // Goal: C with hypotheses h1 : A, h2 : A → B, h3 : B → C
    let env = setup_env();
    let type_a = Expr::const_(Name::from_string("A"), vec![]);
    let type_b = Expr::const_(Name::from_string("B"), vec![]);
    let type_c = Expr::const_(Name::from_string("C"), vec![]);

    // Add type C first
    let mut env_with_c = env;
    env_with_c
        .add_decl(Declaration::Axiom {
            name: Name::from_string("C"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();

    let fvar_h1 = FVarId::new(100);
    let fvar_h2 = FVarId::new(101);
    let fvar_h3 = FVarId::new(102);

    let mut state = ProofState::with_context(
        env_with_c,
        type_c.clone(),
        vec![
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: type_a.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: Expr::arrow(type_a, type_b.clone()),
                value: None,
            },
            LocalDecl {
                fvar: fvar_h3,
                name: "h3".to_string(),
                ty: Expr::arrow(type_b, type_c),
                value: None,
            },
        ],
    );

    solve_by_elim(&mut state, 5).unwrap();
    assert!(state.is_complete());
    // Chain: proof should be App(FVar, App(FVar, FVar)) i.e. h3(h2(h1))
    let proof = state
        .proof_term()
        .expect("solve_by_elim should produce a proof term for chain");
    // Verify the outermost structure is App(FVar, _)
    match proof.kind() {
        ExprKind::App(f, _) => assert!(
            matches!(f.kind(), ExprKind::FVar(_)),
            "chain proof should apply an FVar outermost, got: {proof:?}"
        ),
        _ => panic!("chain proof should be App, got: {proof:?}"),
    }
}

#[test]
fn test_solve_by_elim_fails_without_proof() {
    // Goal: A with no hypotheses
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, target);

    let result = solve_by_elim(&mut state, 5);
    assert!(result.is_err(), "should fail without applicable hypotheses");
}

#[test]
fn test_solve_by_elim_respects_depth_limit() {
    // Goal: B with h1 : A, h2 : A → B but depth = 0
    let env = setup_env();
    let type_a = Expr::const_(Name::from_string("A"), vec![]);
    let type_b = Expr::const_(Name::from_string("B"), vec![]);
    let fvar_h1 = FVarId::new(100);
    let fvar_h2 = FVarId::new(101);

    let mut state = ProofState::with_context(
        env,
        type_b.clone(),
        vec![
            LocalDecl {
                fvar: fvar_h1,
                name: "h1".to_string(),
                ty: type_a.clone(),
                value: None,
            },
            LocalDecl {
                fvar: fvar_h2,
                name: "h2".to_string(),
                ty: Expr::arrow(type_a, type_b),
                value: None,
            },
        ],
    );

    // Depth 0 should fail (can apply h2 but can't recurse to solve A)
    let result = solve_by_elim(&mut state, 0);
    assert!(result.is_err(), "should fail with depth 0");
}

// =========================================================================
// clear tests
// =========================================================================

#[test]
fn test_clear_removes_hypothesis() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let fvar_h = FVarId::new(100);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: fvar_h,
            name: "h".to_string(),
            ty: target,
            value: None,
        }],
    );

    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 1);
    clear(&mut state, "h").unwrap();
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 0);
}

#[test]
fn test_clear_fails_for_nonexistent() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = clear(&mut state, "nonexistent");
    if let Err(TacticError::HypothesisNotFound(name)) = result {
        assert_eq!(name, "nonexistent");
    } else {
        panic!("Expected HypothesisNotFound error");
    }
}

// =========================================================================
// rename tests
// =========================================================================

#[test]
fn test_rename_changes_name() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let fvar_h = FVarId::new(100);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: fvar_h,
            name: "old_name".to_string(),
            ty: target,
            value: None,
        }],
    );

    rename(&mut state, "old_name", "new_name").unwrap();
    assert_eq!(state.current_goal().unwrap().local_ctx[0].name, "new_name");
}

#[test]
fn test_rename_fails_for_nonexistent() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = rename(&mut state, "nonexistent", "new");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

// =========================================================================
// duplicate tests
// =========================================================================

#[test]
fn test_duplicate_adds_copy() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let fvar_h = FVarId::new(100);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: fvar_h,
            name: "h".to_string(),
            ty: target.clone(),
            value: None,
        }],
    );

    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 1);
    duplicate(&mut state, "h", "h_copy").unwrap();
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 2);
    assert_eq!(state.current_goal().unwrap().local_ctx[1].name, "h_copy");
    // Both should reference the same fvar
    assert_eq!(
        state.current_goal().unwrap().local_ctx[0].fvar,
        state.current_goal().unwrap().local_ctx[1].fvar
    );
}

#[test]
fn test_duplicate_fails_for_nonexistent() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = duplicate(&mut state, "nonexistent", "copy");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

// ==========================================================================
// Tests for specialize tactic
// ==========================================================================

#[test]
fn test_specialize_reduces_pi_type() {
    let env = setup_env();

    // Add a hypothesis type: A → B
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let arrow_ty = Expr::arrow(a_ty.clone(), b_ty.clone());

    // Goal is just B, we'll specialize a hypothesis
    let mut state = ProofState::new(env, b_ty.clone());

    // Add hypothesis h : A → B
    let fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: arrow_ty.clone(),
        value: None,
    });

    // Specialize h with 'a'
    let a_term = Expr::const_(Name::from_string("a"), vec![]);
    specialize(&mut state, "h", a_term).unwrap();

    // After specialization, the hypothesis named `h` (the most-recent binding,
    // which shadows the original `A → B` via the `have`/`let_named` mechanism)
    // should have type B.
    let hyp = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .rev()
        .find(|decl| decl.name == "h")
        .expect("specialized hypothesis should remain visible")
        .clone();
    assert_eq!(hyp.name, "h");
    // The specialized type should be B
    assert!(matches!(hyp.ty.kind(), ExprKind::Const(n, _) if n == &Name::from_string("B")));
}

#[test]
fn test_specialize_inserts_after_later_dependencies_and_hides_old_hypothesis() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let old_h_fvar = FVarId::new(100);
    let n_fvar = FVarId::new(101);
    let mut state = ProofState::with_context(
        env,
        make_p(x.clone()),
        vec![
            LocalDecl {
                fvar: old_h_fvar,
                name: "h".into(),
                ty: Expr::pi(BinderInfo::Default, n_ty.clone(), make_p(Expr::bvar(0))),
                value: None,
            },
            LocalDecl {
                fvar: n_fvar,
                name: "n".into(),
                ty: n_ty,
                value: None,
            },
        ],
    );

    specialize(&mut state, "h", Expr::fvar(n_fvar)).expect("specialize should succeed");

    // `specialize` re-binds the same name via the shared `have`/`let_named`
    // mechanism (Lean semantics: `have h := h n` shadows the old `h`). The new
    // `h` is appended after the dependency `n`, and the original `h` (fvar 100)
    // remains in context but is shadowed by name.
    let goal = state.current_goal().unwrap();

    // The most-recent decl named `h` is the specialized one.
    let visible_h = goal
        .local_ctx
        .iter()
        .rev()
        .find(|decl| decl.name == "h")
        .expect("specialized hypothesis should be present");
    assert_eq!(visible_h.ty, make_p(Expr::fvar(n_fvar)));
    assert_eq!(
        visible_h.value,
        Some(Expr::app(Expr::fvar(old_h_fvar), Expr::fvar(n_fvar))),
        "specialize should record the new hypothesis value as the original proof applied to the argument"
    );
    assert_ne!(
        visible_h.fvar, old_h_fvar,
        "the specialized hypothesis is a fresh local, not the original"
    );

    // The specialized hypothesis must be inserted after the dependency `n`.
    let visible_h_pos = goal
        .local_ctx
        .iter()
        .rposition(|decl| decl.name == "h")
        .expect("specialized hypothesis should be present");
    let n_pos = goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == "n")
        .expect("dependency local should remain present");
    assert!(
        visible_h_pos > n_pos,
        "specialized hypothesis must be inserted after the latest dependency"
    );

    // The original hypothesis stays in context (shadowed by name) so its proof
    // term remains available for the recorded `let`-binding value.
    assert!(
        goal.local_ctx.iter().any(|decl| decl.fvar == old_h_fvar),
        "the original hypothesis stays in context (shadowed) for the recorded value"
    );
}

#[test]
fn test_specialize_fails_on_non_pi() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a_ty.clone());

    // Add hypothesis h : A (not a Pi type)
    let fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a_ty.clone(),
        value: None,
    });

    // Try to specialize - should fail
    let arg = Expr::const_(Name::from_string("a"), vec![]);
    let result = specialize(&mut state, "h", arg);
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("specialize")));
}

#[test]
fn test_specialize_fails_on_wrong_arg_type() {
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let arrow_ty = Expr::arrow(a_ty.clone(), b_ty.clone());

    let mut state = ProofState::new(env, b_ty.clone());

    // Add hypothesis h : A → B
    let fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: arrow_ty,
        value: None,
    });

    // Try to specialize with wrong type - should fail
    // We need something of type B, not A
    let wrong_arg = Expr::const_(Name::from_string("f"), vec![]); // f : A → B, wrong type
    let result = specialize(&mut state, "h", wrong_arg);
    assert!(matches!(result, Err(TacticError::TypeMismatch { .. })));
}

#[test]
fn test_specialize_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let arg = Expr::const_(Name::from_string("a"), vec![]);
    let result = specialize(&mut state, "nonexistent", arg);
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

// ==========================================================================
// Tests for revert tactic
// ==========================================================================

#[test]
fn test_revert_moves_hyp_to_goal() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    // Start with goal B and hypothesis h : A
    let mut state = ProofState::new(env, b_ty.clone());

    let fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a_ty.clone(),
        value: None,
    });

    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 1);

    // Revert h
    revert(&mut state, "h").unwrap();

    // Context should be empty, goal should be A → B
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 0);
    // Target should be a Pi type
    match state.current_goal().unwrap().target.kind() {
        ExprKind::Pi(_, domain, _) => {
            assert!(matches!(domain.kind(), ExprKind::Const(n, _) if n == &Name::from_string("A")));
        }
        _ => panic!("Expected Pi type after revert"),
    }
}

#[test]
fn test_revert_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = revert(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_intro_revert_roundtrip() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let arrow_ty = Expr::arrow(a_ty.clone(), b_ty.clone());

    // Goal: A → B
    let mut state = ProofState::new(env, arrow_ty.clone());

    // intro h gives us h : A, goal B
    intro(&mut state, "h").unwrap();
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 1);

    // revert h gives us goal A → B again (but with fresh meta)
    revert(&mut state, "h").unwrap();
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 0);

    // Target should be Pi again
    assert!(matches!(
        state.current_goal().unwrap().target.kind(),
        ExprKind::Pi(..)
    ));
}

// ==========================================================================
// Tests for congr tactic
// ==========================================================================

#[test]
fn test_congr_fails_on_non_equality() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a_ty);

    let result = congr(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_congr_with_different_functions_fails() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Add two different functions
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        ),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();

    // Goal: f x = g x (different functions)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let fx = Expr::app(f, x.clone());
    let gx = Expr::app(g, x);

    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            fx,
        ),
        gx,
    );

    let mut state = ProofState::new(env, eq);

    let result = congr(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

// ==========================================================================
// Tests for obtain tactic
// ==========================================================================

#[test]
fn test_obtain_fails_on_non_exists() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a_ty.clone());

    // Add hypothesis h : A (not an Exists type)
    let fvar = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a_ty,
        value: None,
    });

    let result = obtain(&mut state, "h", "x", "hx");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_obtain_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = obtain(&mut state, "nonexistent", "x", "hx");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

// ==========================================================================
// Tests for subst tactic
// ==========================================================================

#[test]
fn test_subst_replaces_fvar_in_goal() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    // Add type N for our term
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constant for 5
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    // Add predicate P
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    let x_fvar = FVarId::new(0);
    let h_fvar = FVarId::new(1);
    let five = Expr::const_(Name::from_string("five"), vec![]);

    // h : x = 5, goal: P x
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n_ty.clone(),
            ),
            Expr::fvar(x_fvar),
        ),
        five.clone(),
    );

    let goal_ty = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(x_fvar),
    );

    let mut state = ProofState::with_context(
        env,
        goal_ty,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: h_fvar,
                name: "h".to_string(),
                ty: eq_ty,
                value: None,
            },
        ],
    );

    // Apply subst
    subst(&mut state, "h").unwrap();

    // Check that goal is now P 5
    let new_goal = state.current_goal().unwrap();
    let expected_target = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five);
    assert_eq!(new_goal.target, expected_target);

    // Check that h and x are removed from context
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "h"),
        "h should be removed"
    );
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "x"),
        "x should be removed"
    );
}

#[test]
fn test_subst_reverse_equality() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    let x_fvar = FVarId::new(0);
    let h_fvar = FVarId::new(1);
    let five = Expr::const_(Name::from_string("five"), vec![]);

    // h : 5 = x (reversed), goal: P x
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n_ty.clone(),
            ),
            five.clone(),
        ),
        Expr::fvar(x_fvar),
    );

    let goal_ty = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(x_fvar),
    );

    let mut state = ProofState::with_context(
        env,
        goal_ty,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: h_fvar,
                name: "h".to_string(),
                ty: eq_ty,
                value: None,
            },
        ],
    );

    // Apply subst - should handle reverse equality
    subst(&mut state, "h").unwrap();

    // Check that goal is now P 5
    let new_goal = state.current_goal().unwrap();
    let expected_target = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five);
    assert_eq!(new_goal.target, expected_target);
}

#[test]
fn test_subst_not_equality_fails() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let h_fvar = FVarId::new(0);

    let mut state = ProofState::with_context(
        env,
        a_ty.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: a_ty, // Not an equality
            value: None,
        }],
    );

    let result = subst(&mut state, "h");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_subst_no_fvar_fails() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x_val"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("y_val"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    let h_fvar = FVarId::new(0);
    let a = Expr::const_(Name::from_string("x_val"), vec![]);
    let b = Expr::const_(Name::from_string("y_val"), vec![]);

    // h : a = b (neither is a free variable in context)
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n_ty.clone(),
            ),
            a,
        ),
        b,
    );

    let mut state = ProofState::with_context(
        env,
        n_ty,
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: eq_ty,
            value: None,
        }],
    );

    let result = subst(&mut state, "h");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_subst_hypothesis_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = subst(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

// ==========================================================================
// Tests for subst_vars tactic
// ==========================================================================

#[test]
fn test_subst_vars_substitutes_multiple() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x_val"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("y_val"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty.clone(),
            Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
        ),
    })
    .unwrap();

    let x_fvar = FVarId::new(0);
    let y_fvar = FVarId::new(1);
    let h1_fvar = FVarId::new(2);
    let h2_fvar = FVarId::new(3);
    let a = Expr::const_(Name::from_string("x_val"), vec![]);
    let b = Expr::const_(Name::from_string("y_val"), vec![]);

    // x : N, y : N, h1 : x = a, h2 : y = b, goal: P x y
    let eq_x_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n_ty.clone(),
            ),
            Expr::fvar(x_fvar),
        ),
        a.clone(),
    );

    let eq_y_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n_ty.clone(),
            ),
            Expr::fvar(y_fvar),
        ),
        b.clone(),
    );

    let goal_ty = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::fvar(x_fvar),
        ),
        Expr::fvar(y_fvar),
    );

    let mut state = ProofState::with_context(
        env,
        goal_ty,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_fvar,
                name: "y".to_string(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: h1_fvar,
                name: "h1".to_string(),
                ty: eq_x_a,
                value: None,
            },
            LocalDecl {
                fvar: h2_fvar,
                name: "h2".to_string(),
                ty: eq_y_b,
                value: None,
            },
        ],
    );

    // Apply subst_vars
    subst_vars(&mut state).unwrap();

    // Check that goal is now P a b
    let new_goal = state.current_goal().unwrap();
    let expected_target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("P"), vec![]), a),
        b,
    );
    assert_eq!(new_goal.target, expected_target);

    // Check that all equality hypotheses and variables are removed
    assert!(
        new_goal.local_ctx.is_empty(),
        "all locals should be removed"
    );
}

#[test]
fn test_subst_vars_no_op_when_no_equalities() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let h_fvar = FVarId::new(0);

    let mut state = ProofState::with_context(
        env,
        a_ty.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: a_ty,
            value: None,
        }],
    );

    subst_vars(&mut state).unwrap();

    // Context should be unchanged
    assert_eq!(state.current_goal().unwrap().local_ctx.len(), 1);
}

// ==========================================================================
// Tests for generalize tactic
// ==========================================================================

#[test]
fn test_generalize_abstracts_term() {
    let mut env = setup_env();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    // Goal: P 5
    let five = Expr::const_(Name::from_string("five"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());

    let mut state = ProofState::new(env, goal_ty);

    // Generalize 5 as n
    generalize(&mut state, five, "n").unwrap();

    // Check that goal is now P n with n : N in context
    let new_goal = state.current_goal().unwrap();
    assert_eq!(new_goal.local_ctx.len(), 1);
    assert_eq!(new_goal.local_ctx[0].name, "n");
    assert_eq!(new_goal.local_ctx[0].ty, n_ty);

    // Target should contain the free variable
    let expected_target = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(new_goal.local_ctx[0].fvar),
    );
    assert_eq!(new_goal.target, expected_target);
}

#[test]
fn test_generalize_term_not_in_goal() {
    let mut env = setup_env();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("six"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    // Goal: P 5
    let five = Expr::const_(Name::from_string("five"), vec![]);
    let six = Expr::const_(Name::from_string("six"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());

    let mut state = ProofState::new(env, goal_ty);

    // Generalize `six`, which does NOT occur in the goal. Matching Lean 4,
    // this is NOT an error: the variable `n : N` is still introduced and the
    // goal target is left unchanged (no occurrence to abstract).
    generalize(&mut state, six, "n")
        .expect("generalize over an absent term should still introduce n (Lean 4 semantics)");

    let new_goal = state
        .current_goal()
        .expect("a goal should remain after generalize");
    assert_eq!(
        new_goal.local_ctx.last().map(|d| d.name.as_str()),
        Some("n"),
        "generalize should still introduce the fresh variable n"
    );
    let expected_target = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five);
    assert_eq!(
        new_goal.target, expected_target,
        "with no occurrence to abstract, the goal target is unchanged"
    );
}

// ==========================================================================
// Tests for generalize_eq tactic
// ==========================================================================

#[test]
fn test_generalize_eq_creates_equality_hyp() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    // Goal: P 5
    let five = Expr::const_(Name::from_string("five"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());

    let mut state = ProofState::new(env, goal_ty);

    // Generalize 5 as n with equality heq
    generalize_eq(&mut state, five.clone(), "n", "heq").unwrap();

    // Check that context has n : N and heq : n = 5
    let new_goal = state.current_goal().unwrap();
    assert_eq!(new_goal.local_ctx.len(), 2);
    assert_eq!(new_goal.local_ctx[0].name, "n");
    assert_eq!(new_goal.local_ctx[1].name, "heq");

    // Check heq type is @Eq.{u} N n five (universe-polymorphic since #2225)
    let n_fvar = new_goal.local_ctx[0].fvar;
    let heq_ty = &new_goal.local_ctx[1].ty;
    // Verify structure: App(App(App(Const("Eq", [_]), N), fvar(n)), five)
    // Universe level is a fresh metavar (not hardcoded), so check shape not level.
    let eq_fn = heq_ty.get_app_fn();
    let args = heq_ty.get_app_args();
    match eq_fn.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Eq"),
        other => panic!("expected Eq constant, got: {other:?}"),
    }
    // Direction matches Lean 4 `generalize h : e = x`: original term `five` on
    // the LHS, fresh variable `n` on the RHS (heq : five = n).
    assert_eq!(args.len(), 3, "Eq should have 3 args: type, lhs, rhs");
    assert_eq!(*args[0], n_ty, "type arg should be N");
    assert_eq!(*args[1], five, "lhs should be the original term (five)");
    assert!(
        matches!(args[2].kind(), ExprKind::FVar(id) if *id == n_fvar),
        "rhs should be fvar(n)"
    );

    let expected_target = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::fvar(n_fvar),
    );
    assert_eq!(
        new_goal.target, expected_target,
        "generalize_eq should rewrite the goal target to use the introduced variable"
    );
}

#[test]
fn test_generalize_eq_completes_goal() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("allP"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n_ty.clone(),
            Expr::app(Expr::const_(Name::from_string("P"), vec![]), Expr::bvar(0)),
        ),
    })
    .unwrap();

    let five = Expr::const_(Name::from_string("five"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());
    let mut state = ProofState::new(env.clone(), goal_ty.clone());

    generalize_eq(&mut state, five.clone(), "n", "heq").unwrap();
    let n_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    let proof = Expr::app(
        Expr::const_(Name::from_string("allP"), vec![]),
        Expr::fvar(n_fvar),
    );
    exact(&mut state, proof).unwrap();

    assert!(
        state.is_complete(),
        "generalize_eq goal should be completable"
    );
    let proof = state
        .instantiated_proof()
        .expect("completed proof state should expose the final proof");
    let tc = TypeChecker::new(&env);
    assert!(
        tc.check_type(&proof, &goal_ty).is_ok(),
        "generalize_eq proof should type-check against the original goal"
    );
}

#[test]
fn test_generalize_eq_requires_eq() {
    let mut env = setup_env(); // No Eq initialized

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    let five = Expr::const_(Name::from_string("five"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());

    let mut state = ProofState::new(env, goal_ty);

    let result = generalize_eq(&mut state, five, "n", "heq");
    assert!(matches!(
        result,
        Err(TacticError::InvalidTarget { .. } | TacticError::EnvironmentMissing { .. })
    ));
}

#[test]
fn test_generalize_eq_requires_eq_refl() {
    let mut env = setup_env();

    let u = Name::from_string("u");
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let eq_type = Expr::pi(
        BinderInfo::Implicit,
        sort_u,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![u],
        type_: eq_type,
    })
    .unwrap();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("five"),
        level_params: vec![],
        type_: n_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n_ty.clone(), Expr::prop()),
    })
    .unwrap();

    let five = Expr::const_(Name::from_string("five"), vec![]);
    let goal_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), five.clone());

    let mut state = ProofState::new(env, goal_ty);
    let result = generalize_eq(&mut state, five, "n", "heq");
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "Eq.refl"),
        "missing Eq.refl should be reported explicitly, got: {result:?}"
    );
}

// ==========================================================================
// Tests for funext tactic
// ==========================================================================

fn setup_funext_goal_env() -> (Environment, Expr, Expr, Expr, Expr) {
    let mut env = setup_env();
    env.init_eq().unwrap();
    env.init_funext().unwrap();

    let nat = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let fn_ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());
    for name in ["fn1", "fn2"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: fn_ty.clone(),
        })
        .unwrap();
    }

    let f = Expr::const_(Name::from_string("fn1"), vec![]);
    let g = Expr::const_(Name::from_string("fn2"), vec![]);
    let goal_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                fn_ty,
            ),
            f.clone(),
        ),
        g.clone(),
    );

    (env, nat, f, g, goal_ty)
}

#[test]
fn test_funext_creates_pointwise_goal() {
    let (env, nat, f, g, goal_ty) = setup_funext_goal_env();
    let mut state = ProofState::new(env, goal_ty);

    funext(&mut state, "x").unwrap();

    let goal = state
        .current_goal()
        .expect("funext should leave one pointwise subgoal");
    assert_eq!(goal.local_ctx.len(), 1, "funext should intro one binder");
    assert_eq!(goal.local_ctx[0].name, "x");
    assert_eq!(goal.local_ctx[0].ty, nat.clone());

    let x = Expr::fvar(goal.local_ctx[0].fvar);
    let expected = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            Expr::app(f, x.clone()),
        ),
        Expr::app(g, x),
    );
    assert_eq!(
        goal.target, expected,
        "funext should reduce equality of functions to pointwise equality"
    );
}

// ==========================================================================
// Tests for ext tactic
// ==========================================================================

#[test]
fn test_ext_requires_funext() {
    let mut env = setup_env();
    env.init_eq().unwrap();
    // Note: NOT calling env.init_funext()

    let nat = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let f_ty = Expr::pi(BinderInfo::Default, nat.clone(), nat.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("fn1"),
        level_params: vec![],
        type_: f_ty.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("fn2"),
        level_params: vec![],
        type_: f_ty.clone(),
    })
    .unwrap();

    let f = Expr::const_(Name::from_string("fn1"), vec![]);
    let g = Expr::const_(Name::from_string("fn2"), vec![]);

    // Goal: f = g
    let goal_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                f_ty,
            ),
            f,
        ),
        g,
    );

    let mut state = ProofState::new(env, goal_ty);

    let result = ext(&mut state, "x");
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant.contains("funext"))
    );
}

#[test]
fn test_ext_goal_not_equality() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, a_ty);

    let result = ext(&mut state, "x");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_ext_creates_pointwise_goal() {
    let (env, nat, f, g, goal_ty) = setup_funext_goal_env();
    let mut state = ProofState::new(env, goal_ty);

    ext(&mut state, "x").unwrap();

    let goal = state
        .current_goal()
        .expect("ext should leave one pointwise subgoal");
    assert_eq!(goal.local_ctx.len(), 1, "ext should intro one binder");
    assert_eq!(goal.local_ctx[0].name, "x");
    assert_eq!(goal.local_ctx[0].ty, nat.clone());

    let x = Expr::fvar(goal.local_ctx[0].fvar);
    let expected = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            Expr::app(f, x.clone()),
        ),
        Expr::app(g, x),
    );
    assert_eq!(
        goal.target, expected,
        "ext should reduce equality of functions to pointwise equality"
    );
}

#[test]
fn test_ext_lhs_not_function() {
    let mut env = setup_env();
    env.init_eq().unwrap();
    env.init_funext().unwrap();

    let nat = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x_val"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("y_val"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("x_val"), vec![]);
    let b = Expr::const_(Name::from_string("y_val"), vec![]);

    // Goal: x_val = y_val (where x_val and y_val are not functions)
    let goal_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a,
        ),
        b,
    );

    let mut state = ProofState::new(env, goal_ty);

    let result = ext(&mut state, "x");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

// ==========================================================================
// Tests for injection tactic
// ==========================================================================

#[test]
fn test_injection_nat_succ() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Add axioms for a and b
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    // Add a predicate P
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    // Goal: (Nat.succ a = Nat.succ b) → P
    let succ_a = Expr::app(succ.clone(), a.clone());
    let succ_b = Expr::app(succ.clone(), b.clone());

    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            succ_a,
        ),
        succ_b,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(eq_ty, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro h
    intro(&mut state, "h").unwrap();

    // Apply injection on h
    injection(&mut state, "h").unwrap();

    // After injection, we should have a new hypothesis h_inj : a = b
    let goal = state.current_goal().unwrap();
    let inj_hyp = goal.local_ctx.iter().find(|d| d.name.contains("inj"));
    assert!(
        inj_hyp.is_some(),
        "injection should create an injected hypothesis"
    );
}

#[test]
fn test_injection_different_constructors_fails() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_n = Expr::app(succ, n);

    // Goal: (Nat.zero = Nat.succ n) → P
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero,
        ),
        succ_n,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(eq_ty, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro h
    intro(&mut state, "h").unwrap();

    // injection should fail because constructors are different
    let result = injection(&mut state, "h");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_injection_not_equality_fails() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Goal: Nat → P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(nat, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro n
    intro(&mut state, "n").unwrap();

    // injection should fail because n is not an equality
    let result = injection(&mut state, "n");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_injection_hypothesis_not_found() {
    let env = setup_env_with_nat();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut state = ProofState::new(env, nat);

    let result = injection(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_injection_no_fields_fails() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Goal: (Nat.zero = Nat.zero) → P
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        zero,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(eq_ty, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro h
    intro(&mut state, "h").unwrap();

    // injection should fail because Nat.zero has no fields
    let result = injection(&mut state, "h");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

// ==========================================================================
// Tests for discriminate tactic
// ==========================================================================

#[test]
fn test_discriminate_different_constructors() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let succ_n = Expr::app(succ, n);

    // Goal: (Nat.zero = Nat.succ n) → P
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero,
        ),
        succ_n,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(eq_ty, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro h
    intro(&mut state, "h").unwrap();

    // discriminate should succeed: Nat.zero ≠ Nat.succ n (different constructors)
    discriminate(&mut state, "h")
        .expect("discriminate should close goal for different constructors");
    assert!(
        state.is_complete(),
        "all goals should be discharged after discriminate"
    );
}

#[test]
fn test_discriminate_same_constructor_fails() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let succ_a = Expr::app(succ.clone(), a);
    let succ_b = Expr::app(succ, b);

    // Goal: (Nat.succ a = Nat.succ b) → P
    let eq_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            succ_a,
        ),
        succ_b,
    );

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(eq_ty, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro h
    intro(&mut state, "h").unwrap();

    // discriminate should fail because constructors are the same
    let result = discriminate(&mut state, "h");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_discriminate_hypothesis_not_found() {
    let env = setup_env_with_nat();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut state = ProofState::new(env, nat);

    let result = discriminate(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

#[test]
fn test_discriminate_not_equality_fails() {
    let mut env = setup_env_with_nat();
    env.init_true_false().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    // Goal: Nat → P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal_ty = Expr::arrow(nat, p);

    let mut state = ProofState::new(env, goal_ty);

    // intro n
    intro(&mut state, "n").unwrap();

    // discriminate should fail because n is not an equality
    let result = discriminate(&mut state, "n");
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

// ==========================================================================
// Tests for rcases tactic
// ==========================================================================

#[test]
fn test_rcases_basic() {
    let env = setup_env_with_bool();

    // Goal: Bool → Bool
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro b
    intro(&mut state, "b").unwrap();

    // rcases b (with max depth 1)
    rcases(&mut state, "b", 1).unwrap();

    // Should have 2 goals (same as cases for Bool)
    assert_eq!(state.goals().len(), 2);
}

#[test]
fn test_rcases_depth_zero_noop() {
    let env = setup_env_with_bool();

    // Goal: Bool → Bool
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let target = Expr::arrow(bool_ty.clone(), bool_ty.clone());

    let mut state = ProofState::new(env, target);

    // intro b
    intro(&mut state, "b").unwrap();

    let goals_before = state.goals().len();

    // rcases with depth 0 should do nothing
    rcases(&mut state, "b", 0).unwrap();

    assert_eq!(state.goals().len(), goals_before);
}

// ==========================================================================
// Tests for TypeChecker cache reuse (#1671)
// ==========================================================================

#[test]
fn test_tc_cache_reuse_within_same_goal() {
    // Multiple whnf/is_def_eq calls on the same goal should produce correct
    // results while reusing the internal TypeChecker caches (#1671).
    let env = setup_env();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let prop = Expr::sort(Level::zero());

    let state = ProofState::new(env, a_ty.clone());
    let goal = state.current_goal().unwrap().clone();

    // First call: creates fresh TC, populates cache
    let whnf1 = state.whnf(&goal, &a_ty);
    // Second call: should reuse cached TC state
    let whnf2 = state.whnf(&goal, &a_ty);

    assert_eq!(
        whnf1, whnf2,
        "repeated whnf on same expression/goal should produce identical results"
    );

    // is_def_eq: reflexivity should hold with cached state
    assert!(state.is_def_eq(&goal, &a_ty, &a_ty));
    // is_def_eq: distinct constants should not be equal
    assert!(!state.is_def_eq(&goal, &a_ty, &b_ty));
    // Prop = Sort(0) should be reflexive
    assert!(state.is_def_eq(&goal, &prop, &prop));
}

#[test]
fn test_tc_cache_invalidated_on_goal_switch() {
    // After intro (which creates a new goal with a new meta_id), the TC
    // cache should be invalidated so the new goal gets a fresh context (#1671).
    let env = setup_env();

    // Goal: A → A (need to intro to get a new goal)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a_ty.clone(), a_ty.clone());

    let mut state = ProofState::new(env, target);
    let goal_before = state.current_goal().unwrap().clone();

    // Warm up the cache with a whnf call — A is already in WHNF
    let whnf_warm = state.whnf(&goal_before, &a_ty);
    assert_eq!(whnf_warm, a_ty, "whnf of A should be A (already in WHNF)");

    // intro creates a new goal with different meta_id
    intro(&mut state, "h").unwrap();

    let goal_after = state.current_goal().unwrap().clone();
    assert_ne!(
        goal_before.meta_id, goal_after.meta_id,
        "intro should create a new goal with different meta_id"
    );

    // whnf on the new goal should work correctly (cache invalidated)
    let result = state.whnf(&goal_after, &a_ty);
    assert_eq!(result, a_ty, "whnf of A should be A in new goal context");
}

#[test]
fn test_tc_cache_invalidated_on_current_goal_mut() {
    // current_goal_mut() should invalidate the TC cache so that subsequent
    // type-checking operations see the mutated context (#1671).
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);

    let mut state = ProofState::new(env, a_ty.clone());
    let goal = state.current_goal().unwrap().clone();

    // Warm up the cache — A is already in WHNF
    let whnf_warm = state.whnf(&goal, &a_ty);
    assert_eq!(whnf_warm, a_ty, "whnf of A should be A");
    assert!(state.is_def_eq(&goal, &a_ty, &a_ty));

    // Mutate the goal target via current_goal_mut (this triggers invalidation)
    state.current_goal_mut().unwrap().target = b_ty.clone();

    // After mutation, TC operations should still work correctly on the new target
    let goal_after = state.current_goal().unwrap().clone();
    assert_eq!(goal_after.target, b_ty);
    let whnf_result = state.whnf(&goal_after, &b_ty);
    assert_eq!(whnf_result, b_ty, "whnf should work on mutated goal target");
    assert!(
        state.is_def_eq(&goal_after, &b_ty, &b_ty),
        "is_def_eq should work on mutated goal"
    );
}

#[test]
fn test_tc_cache_invalidated_on_pop_current_goal() {
    // pop_current_goal should invalidate the TC cache so the next goal
    // gets a fresh TypeChecker context (#1671).
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let prop = Expr::sort(Level::zero());

    let target = Expr::arrow(a_ty.clone(), prop.clone());
    let mut state = ProofState::new(env, target);

    // Warm up cache on first goal — A is already in WHNF
    let goal0 = state.current_goal().unwrap().clone();
    let whnf_warm = state.whnf(&goal0, &a_ty);
    assert_eq!(whnf_warm, a_ty, "whnf of A should be A");

    // intro creates a new goal and pops the old one
    intro(&mut state, "h").unwrap();
    let goal1 = state.current_goal().unwrap().clone();

    // The new goal should have the hypothesis in its local context
    assert!(
        !goal1.local_ctx.is_empty(),
        "intro should add hypothesis to goal context"
    );

    // TC operations should work correctly with the new context
    let whnf_result = state.whnf(&goal1, &prop);
    assert_eq!(whnf_result, prop, "whnf of Prop should be Prop in new goal");
}

#[test]
fn test_proof_state_scope_with_context_root_is_exact() {
    let env = setup_env();
    let local_ty = Expr::const_(Name::from_string("A"), vec![]);
    let local_fvar = clean_kernel::FVarId::new(17);
    let local_ctx = vec![LocalDecl {
        fvar: local_fvar,
        name: "x".to_string(),
        ty: local_ty.clone(),
        value: None,
    }];

    let state = ProofState::with_context(env, Expr::prop(), local_ctx);
    let root = state
        .metas()
        .get(state.root_meta_id)
        .expect("with_context must register its root metavariable");

    assert_eq!(
        root.locals,
        vec![("x".to_string(), local_fvar, local_ty)],
        "the root metavariable must capture exactly the supplied local context"
    );
}

#[test]
fn test_proof_state_scope_fresh_child_is_exact_elab_union() {
    let env = setup_env();
    let elab_ty = Expr::type_();
    let elab_fvar = clean_kernel::FVarId::new(10);
    let elab_decl = LocalDecl {
        fvar: elab_fvar,
        name: "alpha".to_string(),
        ty: elab_ty.clone(),
        value: None,
    };
    let mut state = ProofState::with_elab_context(env, Expr::prop(), vec![elab_decl.clone()]);

    let parent_only_fvar = clean_kernel::FVarId::new(11);
    state
        .current_goal_mut()
        .expect("initial goal")
        .local_ctx
        .push(LocalDecl {
            fvar: parent_only_fvar,
            name: "parent_only".to_string(),
            ty: Expr::prop(),
            value: None,
        });

    let child_fvar = clean_kernel::FVarId::new(12);
    let child_ty = Expr::const_(Name::from_string("A"), vec![]);
    let child_ctx = vec![
        elab_decl,
        LocalDecl {
            fvar: child_fvar,
            name: "child".to_string(),
            ty: child_ty.clone(),
            value: None,
        },
    ];
    let child_meta = state.fresh_meta_in_context(Expr::prop(), &child_ctx);
    let child = state
        .metas()
        .get(child_meta)
        .expect("fresh child metavariable");

    assert_eq!(
        child.locals,
        vec![
            ("alpha".to_string(), elab_fvar, elab_ty),
            ("child".to_string(), child_fvar, child_ty),
        ],
        "the child scope must be the de-duplicated elaborator/child union, not the focused parent"
    );
    assert!(
        child
            .locals
            .iter()
            .all(|(_, fvar, _)| *fvar != parent_only_fvar),
        "a current-goal-only local must not leak into a supplied child context"
    );
}

#[test]
fn test_proof_state_scope_clone_imports_missing_meta_exactly() {
    let env = setup_env();
    let elab_fvar = clean_kernel::FVarId::new(20);
    let elab_ty = Expr::type_();
    let elab_decl = LocalDecl {
        fvar: elab_fvar,
        name: "alpha".to_string(),
        ty: elab_ty.clone(),
        value: None,
    };
    let parent = ProofState::with_elab_context(env, Expr::prop(), vec![elab_decl.clone()]);

    let child_fvar = clean_kernel::FVarId::new(21);
    let child_ty = Expr::const_(Name::from_string("A"), vec![]);
    let goal = Goal {
        meta_id: crate::unify::MetaId(1_000),
        target: Expr::prop(),
        local_ctx: vec![
            elab_decl,
            LocalDecl {
                fvar: child_fvar,
                name: "child".to_string(),
                ty: child_ty.clone(),
                value: None,
            },
        ],
        tag: None,
    };

    let focused = parent.clone_with_goal(goal);
    let imported = focused
        .metas()
        .get(crate::unify::MetaId(1_000))
        .expect("clone_with_goal must import a missing goal metavariable");
    assert_eq!(
        imported.locals,
        vec![
            ("alpha".to_string(), elab_fvar, elab_ty),
            ("child".to_string(), child_fvar, child_ty),
        ],
        "an imported goal metavariable must use the exact goal scope"
    );
}

#[test]
#[should_panic(
    expected = "focused goal context must be a type-compatible subset of its metavariable scope"
)]
fn test_proof_state_scope_clone_mismatch_fails_closed() {
    let env = setup_env();
    let original_fvar = clean_kernel::FVarId::new(30);
    let original_ty = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar: original_fvar,
            name: "original".to_string(),
            ty: original_ty,
            value: None,
        }],
    );

    let mismatched_goal = Goal {
        meta_id: state.root_meta_id,
        target: Expr::prop(),
        local_ctx: vec![LocalDecl {
            fvar: clean_kernel::FVarId::new(31),
            name: "different".to_string(),
            ty: Expr::prop(),
            value: None,
        }],
        tag: None,
    };

    let _ = state.clone_with_goal(mismatched_goal);
}

#[test]
#[should_panic(
    expected = "focused goal context must be a type-compatible subset of its metavariable scope"
)]
fn test_proof_state_scope_clone_retype_mismatch_fails_closed() {
    let env = setup_env();
    let fvar = clean_kernel::FVarId::new(32);
    let state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar,
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        }],
    );

    let retyped_goal = Goal {
        meta_id: state.root_meta_id,
        target: Expr::prop(),
        local_ctx: vec![LocalDecl {
            fvar,
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("B"), vec![]),
            value: None,
        }],
        tag: None,
    };

    let _ = state.clone_with_goal(retyped_goal);
}

#[test]
#[should_panic(expected = "focused goal target must be definitionally equal")]
fn test_proof_state_scope_clone_target_mismatch_fails_closed() {
    let env = setup_env();
    let state = ProofState::new(env, Expr::prop());
    let retargeted_goal = Goal {
        meta_id: state.root_meta_id,
        target: Expr::const_(Name::from_string("A"), vec![]),
        local_ctx: Vec::new(),
        tag: None,
    };

    let _ = state.clone_with_goal(retargeted_goal);
}

#[test]
fn test_proof_state_scope_clone_accepts_narrowed_context() {
    let env = setup_env();
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let kept_fvar = clean_kernel::FVarId::new(40);
    let cleared_fvar = clean_kernel::FVarId::new(41);
    let mut state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![
            LocalDecl {
                fvar: kept_fvar,
                name: "kept".to_string(),
                ty: ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: cleared_fvar,
                name: "cleared".to_string(),
                ty: ty.clone(),
                value: None,
            },
        ],
    );

    clear(&mut state, "cleared").expect("clear should narrow the visible context");
    let narrowed_goal = state.current_goal().expect("narrowed goal").clone();
    let focused = state.clone_with_goal(narrowed_goal);
    let root = focused
        .metas()
        .get(state.root_meta_id)
        .expect("focused root metavariable");

    assert_eq!(
        root.locals.len(),
        2,
        "narrowing must not widen or rewrite the immutable creation scope"
    );
    assert_eq!(focused.current_goal().unwrap().local_ctx.len(), 1);
    assert_eq!(focused.current_goal().unwrap().local_ctx[0].fvar, kept_fvar);
}

#[test]
fn test_proof_state_scope_clone_accepts_renamed_context() {
    let env = setup_env();
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let fvar = clean_kernel::FVarId::new(50);
    let mut state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar,
            name: "before".to_string(),
            ty,
            value: None,
        }],
    );

    rename(&mut state, "before", "after").expect("rename should preserve local identity");
    let renamed_goal = state.current_goal().expect("renamed goal").clone();
    let focused = state.clone_with_goal(renamed_goal);

    assert_eq!(focused.current_goal().unwrap().local_ctx[0].name, "after");
    assert_eq!(
        focused
            .metas()
            .get(state.root_meta_id)
            .expect("focused root metavariable")
            .locals[0]
            .0,
        "before",
        "surface renaming must not mutate the immutable creation scope"
    );
}

#[test]
fn test_proof_state_scope_fresh_scratch_clone_uses_explicit_context() {
    let env = setup_env();
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let front_fvar = clean_kernel::FVarId::new(60);
    let state = ProofState::with_context(
        env,
        Expr::prop(),
        vec![LocalDecl {
            fvar: front_fvar,
            name: "front".to_string(),
            ty: ty.clone(),
            value: None,
        }],
    );

    let scratch_fvar = clean_kernel::FVarId::new(61);
    let scratch_ctx = vec![LocalDecl {
        fvar: scratch_fvar,
        name: "scratch".to_string(),
        ty: ty.clone(),
        value: None,
    }];
    let scratch = state.clone_with_fresh_goal_target_in_context(Expr::prop(), &scratch_ctx);
    let scratch_goal = scratch.current_goal().expect("scratch root goal");
    let scratch_meta = scratch
        .metas()
        .get(scratch_goal.meta_id)
        .expect("scratch root metavariable");

    assert_eq!(scratch_goal.local_ctx.len(), 1);
    assert_eq!(scratch_goal.local_ctx[0].fvar, scratch_fvar);
    assert_eq!(scratch_goal.local_ctx[0].name, "scratch");
    assert_eq!(scratch_goal.local_ctx[0].ty, scratch_ctx[0].ty);
    assert_eq!(
        scratch_meta.locals,
        vec![("scratch".to_string(), scratch_fvar, ty)]
    );
    assert!(
        scratch_meta
            .locals
            .iter()
            .all(|(_, fvar, _)| *fvar != front_fvar),
        "the parent front context must not leak into an explicit scratch goal"
    );
}

#[test]
fn test_assert_continuation_uses_hypothesis_and_closed_proof_checks() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target.clone());

    assert_(&mut state, "h", target.clone()).expect("assert should create two goals");
    exact(&mut state, Expr::const_(Name::from_string("a"), vec![]))
        .expect("the assertion proof goal should close with a");
    assumption(&mut state).expect("the continuation must close using asserted hypothesis h");

    assert!(state.is_complete(), "both assert goals should be closed");
    let closed = state
        .closed_proof()
        .expect("assert must expose a fully closed proof term");
    let checker = clean_kernel::TypeChecker::new(state.env());
    assert!(
        checker.check_type(&closed, &target).is_ok(),
        "the closed assert proof must pass the kernel type checker"
    );
}

// ==========================================================================
// ProofState::merge_meta_state tests (#1802)
// ==========================================================================

#[test]
fn test_merge_meta_state_copies_new_assignments() {
    // Create a proof state with two goals sharing the meta state
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut ps = ProofState::new(env, Expr::arrow(a.clone(), b.clone()));

    // Create a focused clone and assign a metavariable in it
    let goal = ps.current_goal().unwrap().clone();
    let mut focused = ps.clone_with_goal(goal);
    let fresh_meta = focused.metas_mut().fresh(a.clone());
    focused.metas_mut().assign(fresh_meta, a.clone());

    // Before merge, ps doesn't know about the new meta
    assert!(!ps.metas().is_assigned(fresh_meta));

    // After merge, the assignment should be visible
    ps.merge_meta_state(&focused);
    assert!(
        ps.metas().is_assigned(fresh_meta),
        "merge_meta_state should copy new assignments from focused state"
    );
}

#[test]
fn test_merge_meta_state_preserves_existing() {
    // Ensure merge doesn't overwrite existing assignments
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let _b = Expr::const_(Name::from_string("B"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let meta = ps.metas_mut().fresh(a.clone());
    ps.metas_mut().assign(meta, a.clone());

    // focused state has same meta but we won't reassign (already assigned in clone)
    let goal = ps.current_goal().unwrap().clone();
    let focused = ps.clone_with_goal(goal);

    ps.merge_meta_state(&focused);
    // Original assignment should still be A, not changed
    let assignment = ps.metas().get_assignment(meta).unwrap();
    assert_eq!(
        assignment, &a,
        "merge should not overwrite existing assignments"
    );
}

#[test]
fn test_merge_meta_state_syncs_next_fvar() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = ProofState::new(env, a.clone());

    let goal = ps.current_goal().unwrap().clone();
    let mut focused = ps.clone_with_goal(goal);

    // Allocate some fvars in focused
    let _fv1 = focused.fresh_fvar();
    let _fv2 = focused.fresh_fvar();

    let old_fvar = ps.next_fvar;
    ps.merge_meta_state(&focused);
    assert!(
        ps.next_fvar > old_fvar,
        "merge should sync next_fvar to avoid collisions"
    );
}

#[test]
fn test_sub_proof_state_merge_keeps_parent_root_meta_unassigned() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut parent = ProofState::new(env, target.clone());
    let parent_root = parent.root_meta_id;

    let mut sub = builtins_phase3d_elab::create_sub_proof_state(&parent, target);
    assert_ne!(
        sub.root_meta_id, parent_root,
        "nested proof state must use a fresh root metavariable"
    );

    exact(&mut sub, Expr::const_(Name::from_string("a"), vec![]))
        .expect("nested proof state should close with exact a");
    assert!(sub.is_complete(), "nested proof should be complete");
    assert!(
        sub.closed_proof().is_some(),
        "nested proof extraction must use the nested root metavariable"
    );

    parent.merge_meta_state(&sub);

    assert!(
        parent.current_goal().is_some(),
        "merging a nested proof must not pop the parent goal"
    );
    assert!(
        parent.metas().get_assignment(parent_root).is_none(),
        "nested proof merge must not assign the parent root metavariable"
    );
    assert!(
        parent.metas().get_assignment(sub.root_meta_id).is_some(),
        "merge should still import the nested proof assignment under its fresh meta"
    );
    assert!(
        parent.proof_term().is_none(),
        "parent proof_term() must remain None while the parent goal is still open"
    );
}

#[test]
fn test_all_goals_pattern_propagates_meta_across_goals() {
    // Simulates the all_goals pattern from elab_tactic_compound.rs:
    // drain goals, clone_with_goal per goal, process, merge back.
    // Verifies that a metavariable assigned during goal 1's processing
    // is visible during goal 2's processing (#1802 AC3).
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());

    // Create a shared metavariable (simulates a hole that appears in both goals)
    let shared_meta = ps.metas_mut().fresh(a.clone());

    // Create two goals that both reference the shared meta
    let goal1_meta = ps.metas_mut().fresh(a.clone());
    let goal2_meta = ps.metas_mut().fresh(a.clone());
    ps.goals.clear();
    ps.goals.push_back(Goal {
        meta_id: goal1_meta,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("goal1".to_string()),
    });
    ps.goals.push_back(Goal {
        meta_id: goal2_meta,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("goal2".to_string()),
    });

    // Simulate all_goals pattern: drain, clone_with_goal, process, merge
    let goals: Vec<_> = ps.goals.drain(..).collect();
    for (i, goal) in goals.into_iter().enumerate() {
        let mut focused = ps.clone_with_goal(goal);
        if i == 0 {
            // Goal 1: assign the shared metavariable
            focused.metas_mut().assign(shared_meta, a.clone());
        } else {
            // Goal 2: verify the assignment from goal 1 is visible
            assert!(
                focused.metas().is_assigned(shared_meta),
                "shared metavariable assigned in goal 1 must be visible in goal 2 after merge"
            );
        }
        ps.merge_meta_state(&focused);
        ps.goals.append(&mut focused.goals);
    }

    // After all_goals, the shared meta should still be assigned in the parent state
    assert!(
        ps.metas().is_assigned(shared_meta),
        "shared metavariable must be assigned in parent state after all_goals"
    );
    assert_eq!(ps.goals.len(), 2, "both goals should be preserved");
}

#[test]
fn test_try_combinator_rollback_preserves_original_state() {
    // Verifies that the try combinator pattern (clone + rollback on failure)
    // correctly restores state including metavariable assignments (#1802 AC4).
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let meta = ps.metas_mut().fresh(a.clone());

    // Simulate try combinator: clone, attempt tactic, rollback on failure
    let saved = ps.clone();

    // Simulate a "failing" tactic that mutates state before failing:
    // assign the meta and add a spurious goal
    ps.metas_mut().assign(meta, b.clone());
    let spurious_meta = ps.metas_mut().fresh(b.clone());
    ps.goals.push_back(Goal {
        meta_id: spurious_meta,
        target: b,
        local_ctx: vec![],
        tag: None,
    });

    // Rollback: restore saved state (as try combinator does)
    ps = saved;

    // Original state should be fully restored
    assert!(
        !ps.metas().is_assigned(meta),
        "try rollback must undo metavariable assignments"
    );
    assert_eq!(
        ps.goals.len(),
        1,
        "try rollback must restore original goal count"
    );
}

// ==========================================================================
// merge_meta_state level unification tests (#1847)
// ==========================================================================

#[test]
fn test_merge_meta_state_propagates_level_constraints() {
    // Verifies that level constraints discovered during focused tactic
    // execution are propagated back through merge_meta_state (#1847).
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());

    // Create two goals simulating an all_goals scenario
    let goal1_meta = ps.metas_mut().fresh(a.clone());
    let goal2_meta = ps.metas_mut().fresh(a.clone());
    ps.goals.clear();
    ps.goals.push_back(Goal {
        meta_id: goal1_meta,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("goal1".to_string()),
    });
    ps.goals.push_back(Goal {
        meta_id: goal2_meta,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("goal2".to_string()),
    });

    let u0 = Name::from_string("u_0");
    let u1 = Name::from_string("u_1");
    let level_one = Level::succ(Level::zero());

    // Simulate all_goals: drain goals, process each in focused state, merge back
    let goals: Vec<_> = ps.goals.drain(..).collect();
    for (i, goal) in goals.into_iter().enumerate() {
        let mut focused = ps.clone_with_goal(goal);
        if i == 0 {
            // Goal 1: add level constraint u_0 = 1
            focused
                .metas_mut()
                .add_level_constraint(u0.clone(), level_one.clone())
                .expect("level constraint should succeed");
        } else {
            // Goal 2: add level constraint u_1 = u_0 (param-to-param union)
            // After merge from goal 1, u_0 should already be constrained to 1
            assert!(
                focused.metas().get_level_constraint(&u0).is_some(),
                "u_0 constraint from goal 1 must be visible in goal 2 after merge"
            );
            focused
                .metas_mut()
                .add_level_constraint(u1.clone(), Level::Param(u0.clone()))
                .expect("param-to-param constraint should succeed");
        }
        ps.merge_meta_state(&focused);
        ps.goals.append(&mut focused.goals);
    }

    // After all_goals, both constraints should be present in the parent state
    assert!(
        ps.metas().get_level_constraint(&u0).is_some(),
        "u_0 level constraint must survive merge into parent"
    );
    assert!(
        ps.metas().get_level_constraint(&u1).is_some(),
        "u_1 level constraint must survive merge into parent"
    );
}

// ==========================================================================
// Case tactic goal focusing tests (#1809)
// ==========================================================================

#[test]
fn test_case_tactic_focuses_matching_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());

    // Manually create two tagged goals
    let meta1 = ps.metas_mut().fresh(a.clone());
    let meta2 = ps.metas_mut().fresh(a.clone());
    ps.goals.clear();
    ps.goals.push_back(Goal {
        meta_id: meta1,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("inl".to_string()),
    });
    ps.goals.push_back(Goal {
        meta_id: meta2,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("inr".to_string()),
    });

    // Simulate case tag focusing: find "inr" and swap to front
    let tag = "inr";
    let idx = ps
        .goals
        .iter()
        .position(|g| g.tag.as_deref() == Some(tag))
        .expect("should find goal with tag 'inr'");
    ps.goals.swap(0, idx);

    assert_eq!(
        ps.goals[0].tag.as_deref(),
        Some("inr"),
        "first goal should be the one matching the case tag"
    );
    assert_eq!(
        ps.goals[1].tag.as_deref(),
        Some("inl"),
        "second goal should be the remaining one"
    );
}

#[test]
fn test_case_suffix_matching_component_boundary() {
    // Lean 4 suffix matching works on Name components, not characters.
    // "zero" matches "Nat.zero" (component match),
    // but "ero" should NOT match "Nat.zero" (mid-component).
    let goal_tag = "Nat.zero";

    // "zero" is a valid suffix (component boundary at '.')
    let tag = "zero";
    let suffix_ok = goal_tag.ends_with(tag)
        && (goal_tag.len() == tag.len()
            || goal_tag.as_bytes()[goal_tag.len() - tag.len() - 1] == b'.');
    assert!(suffix_ok, "'zero' should suffix-match 'Nat.zero'");

    // "ero" is NOT a valid suffix (no '.' before it)
    let bad_tag = "ero";
    let suffix_bad = goal_tag.ends_with(bad_tag)
        && (goal_tag.len() == bad_tag.len()
            || goal_tag.as_bytes()[goal_tag.len() - bad_tag.len() - 1] == b'.');
    assert!(
        !suffix_bad,
        "'ero' should NOT suffix-match 'Nat.zero' (mid-component)"
    );

    // "Nat" is a valid prefix
    let prefix_tag = "Nat";
    let prefix_ok = goal_tag.starts_with(prefix_tag)
        && (goal_tag.len() == prefix_tag.len() || goal_tag.as_bytes()[prefix_tag.len()] == b'.');
    assert!(prefix_ok, "'Nat' should prefix-match 'Nat.zero'");
}

// =============================================================================
// close_goal_unchecked ratchet (#2159)
// =============================================================================

/// Static ratchet: prevents `close_goal_unchecked` call site regression (#2159).
///
/// Counts production `close_goal_unchecked(` call sites in non-test Rust files
/// under `crates/clean-elab/src/tactic/`. Excludes the function definition in
/// core.rs and the internal delegation call. When an unchecked site is migrated
/// to the checked `close_goal`, decrease `CLOSE_GOAL_UNCHECKED_RATCHET`.
#[test]
fn close_goal_unchecked_site_count_ratchet() {
    use crate::tactic::core::CLOSE_GOAL_UNCHECKED_RATCHET;
    use std::path::PathBuf;

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tactic_dir = manifest_dir.join("src").join("tactic");

    let output = std::process::Command::new("grep")
        .args(["-r", "-F", "--include=*.rs", "-n", "close_goal_unchecked("])
        .arg(&tactic_dir)
        .output()
        .expect("grep should be available");

    assert!(
        !output.stdout.is_empty(),
        "grep found 0 matches for close_goal_unchecked in {tactic_dir:?} — \
         this likely means the path is wrong or grep failed (exit code: {})",
        output.status.code().unwrap_or(-1)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let production_sites: Vec<&str> = stdout
        .lines()
        .filter(|line| {
            let is_test = line.contains("/tests/") || line.contains("/tests.rs:");
            let is_definition = line.contains("pub(crate) fn close_goal_unchecked(");
            let is_delegation = line.contains("self.close_goal_unchecked(proof)");
            let is_doc = line.contains("//!") || line.contains("///");
            let is_ratchet_const = line.contains("CLOSE_GOAL_UNCHECKED_RATCHET");
            // Exclude matches inside inline #[cfg(test)] modules (#2533 regression)
            let is_inline_test = is_inside_cfg_test_block(line);
            !is_test
                && !is_definition
                && !is_delegation
                && !is_doc
                && !is_ratchet_const
                && !is_inline_test
        })
        .collect();

    assert!(
        production_sites.len() == CLOSE_GOAL_UNCHECKED_RATCHET,
        "close_goal_unchecked ratchet VIOLATED: {} production call sites found (max: {})\n\
         If you migrated a site to checked close_goal, decrease CLOSE_GOAL_UNCHECKED_RATCHET in core.rs.\n\
         If you added an unchecked site, reconsider — can you use the checked close_goal instead?\n\
         Sites found:\n{}",
        production_sites.len(),
        CLOSE_GOAL_UNCHECKED_RATCHET,
        production_sites.join("\n")
    );
}

/// Check if a grep output line (format: `path:line_num:content`) comes from
/// inside a `#[cfg(test)] mod` block. Reads the source file and finds the
/// inline test module range, then checks whether the match line falls
/// inside it. Distinguishes `#[cfg(test)] mod tests` (test module) from
/// `#[cfg(test)] use ...` (conditional import). (#2533 regression)
fn is_inside_cfg_test_block(grep_line: &str) -> bool {
    // grep -n output format: "path:line_num:content"
    let parts: Vec<&str> = grep_line.splitn(3, ':').collect();
    if parts.len() < 2 {
        return false;
    }
    let file_path = parts[0];
    let match_line_num: usize = match parts[1].parse() {
        Ok(n) => n,
        Err(_) => return false,
    };
    let content = match std::fs::read_to_string(file_path) {
        Ok(c) => c,
        Err(_) => return false,
    };
    let test_mod_ranges = crate::test_support::source_scan::cfg_test_mod_line_ranges(&content);
    let line_idx = match_line_num.saturating_sub(1);
    crate::test_support::source_scan::line_is_inside_cfg_test_mod(&test_mod_ranges, line_idx)
}

/// Ratchet test: count direct `metas.assign(` call sites in production tactic code.
///
/// Direct `metas.assign` calls bypass both the checked `close_goal` and the
/// ratcheted `close_goal_unchecked`. Each site should eventually migrate to
/// `close_goal` (checked). When a site is migrated, decrease
/// `METAS_ASSIGN_BYPASS_RATCHET` in core.rs.
///
/// Excludes: tests, inline `#[cfg(test)]` modules, the delegation call inside
/// `close_goal_unchecked`, doc comments, and the ratchet constant itself. (#2202)
#[test]
fn metas_assign_bypass_site_count_ratchet() {
    use crate::tactic::core::METAS_ASSIGN_BYPASS_RATCHET;
    use std::path::PathBuf;

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tactic_dir = manifest_dir.join("src").join("tactic");

    let output = std::process::Command::new("grep")
        .args(["-r", "-F", "--include=*.rs", "-n", "metas.assign("])
        .arg(&tactic_dir)
        .output()
        .expect("grep should be available");

    assert!(
        !output.stdout.is_empty(),
        "grep found 0 matches for metas.assign in {tactic_dir:?} — \
         this likely means the path is wrong or grep failed (exit code: {})",
        output.status.code().unwrap_or(-1)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let production_sites: Vec<&str> = stdout
        .lines()
        .filter(|line| {
            let is_test = line.contains("/tests/") || line.contains("/tests.rs:");
            let is_close_goal_delegation = line.contains("self.metas.assign(goal_meta_id, proof)");
            let is_doc = line.contains("//!") || line.contains("///");
            let is_ratchet_const = line.contains("METAS_ASSIGN_BYPASS_RATCHET");
            // Exclude matches inside inline #[cfg(test)] modules (#2533 regression)
            let is_inline_test = is_inside_cfg_test_block(line);
            !is_test && !is_close_goal_delegation && !is_doc && !is_ratchet_const && !is_inline_test
        })
        .collect();

    match METAS_ASSIGN_BYPASS_RATCHET {
        0 => assert_eq!(
            production_sites.len(),
            0,
            "metas.assign bypass ratchet VIOLATED: {} production call sites found (max: 0)\n\
             If you added a direct metas.assign site, reconsider — use close_goal (checked) instead.\n\
             Sites found:\n{}",
            production_sites.len(),
            production_sites.join("\n")
        ),
        ratchet => {
            assert!(
                production_sites.len() <= ratchet,
                "metas.assign bypass ratchet VIOLATED: {} production call sites found (max: {})\n\
                 If you migrated a site to close_goal, decrease METAS_ASSIGN_BYPASS_RATCHET in core.rs.\n\
                 If you added a direct metas.assign site, reconsider — use close_goal (checked) instead.\n\
                 Sites found:\n{}",
                production_sites.len(),
                ratchet,
                production_sites.join("\n")
            );

            if production_sites.len() < ratchet {
                eprintln!(
                    "NOTE: metas.assign bypass site count ({}) is below ratchet ({}). \
                     Consider lowering METAS_ASSIGN_BYPASS_RATCHET in core.rs.",
                    production_sites.len(),
                    ratchet,
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// prune_solved_goals tests (Part of #1803)
// ---------------------------------------------------------------------------

#[test]
fn test_prune_solved_goals_removes_assigned_goal() {
    // AC1/AC2 regression: prune_solved_goals should remove goals whose
    // metavariable is already assigned, leaving unassigned goals intact.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let m0 = ps.current_goal().unwrap().meta_id;

    // Add a second goal with a fresh meta
    let m1 = ps.metas_mut().fresh(a.clone());
    ps.goals.push_back(Goal {
        meta_id: m1,
        target: a.clone(),
        local_ctx: vec![],
        tag: None,
    });
    assert_eq!(ps.goals.len(), 2);

    // Assign M1 (simulates a tactic solving the second goal)
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    ps.metas_mut().assign(m1, proof);

    // Before prune: still 2 goals
    assert_eq!(ps.goals.len(), 2);

    ps.prune_solved_goals();

    // M1 is assigned → removed. M0 is unassigned → remains.
    assert_eq!(ps.goals.len(), 1, "prune should remove the assigned goal");
    assert_eq!(
        ps.goals[0].meta_id, m0,
        "the remaining goal should be M0 (unassigned)"
    );
}

#[test]
fn test_prune_solved_goals_transitive_shared_mvar() {
    // AC3: when solving one goal transitively solves another via a shared
    // metavariable, prune_solved_goals should remove both.
    //
    // Scenario: M0's assignment references M1 (shared meta). When M1 is
    // assigned, both M0 and M1 are "assigned" in MetaState, so both goals
    // should be pruned. M2 is unrelated and should survive.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let m0 = ps.current_goal().unwrap().meta_id;

    // Create two additional goals
    let m1 = ps.metas_mut().fresh(a.clone());
    let m2 = ps.metas_mut().fresh(a.clone());
    ps.goals.clear();
    ps.goals.push_back(Goal {
        meta_id: m0,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("m0".to_string()),
    });
    ps.goals.push_back(Goal {
        meta_id: m1,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("m1".to_string()),
    });
    ps.goals.push_back(Goal {
        meta_id: m2,
        target: a.clone(),
        local_ctx: vec![],
        tag: Some("m2_unrelated".to_string()),
    });
    assert_eq!(ps.goals.len(), 3);

    // Step 1: Assign M0 := FVar(M1) — M0 depends on M1 transitively.
    // This simulates `apply` producing a term that contains a sub-meta.
    let m1_fvar = crate::unify::MetaState::to_fvar(m1);
    ps.metas_mut().assign(m0, Expr::fvar(m1_fvar));

    // Step 2: Assign M1 := a (the actual proof)
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    ps.metas_mut().assign(m1, proof);

    // Both M0 and M1 are now assigned. M2 is not.
    assert!(ps.metas().is_assigned(m0), "M0 should be assigned");
    assert!(ps.metas().is_assigned(m1), "M1 should be assigned");
    assert!(!ps.metas().is_assigned(m2), "M2 should NOT be assigned");

    ps.prune_solved_goals();

    // Only M2 should remain
    assert_eq!(
        ps.goals.len(),
        1,
        "prune should remove both M0 and M1 (transitively solved)"
    );
    assert_eq!(
        ps.goals[0].meta_id, m2,
        "the remaining goal should be M2 (unrelated, unassigned)"
    );
}

#[test]
fn test_prune_solved_goals_no_change_when_none_assigned() {
    // Prune on a state with no assigned metas should be a no-op.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    let mut ps = ProofState::new(env, a.clone());
    let m1 = ps.metas_mut().fresh(a.clone());
    ps.goals.push_back(Goal {
        meta_id: m1,
        target: a,
        local_ctx: vec![],
        tag: None,
    });
    assert_eq!(ps.goals.len(), 2);

    ps.prune_solved_goals();

    assert_eq!(
        ps.goals.len(),
        2,
        "prune should not remove any goals when none are assigned"
    );
}

// ---------------------------------------------------------------------------
// Superposition fallback in decide tactic (Part of #1164)
// ---------------------------------------------------------------------------

/// Test that the superposition fallback produces a valid proof term for
/// a reflexivity goal. This verifies the wiring from the tactic layer
/// through AutomationEngine → GoalClausifier → SuperpositionProver →
/// SuperpositionReconstructor → kernel TypeChecker.
#[test]
fn test_superposition_fallback_reflexivity() {
    use crate::tactic::smt::try_superposition_fallback;

    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target.clone());
    let goal = state.current_goal().unwrap().clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_reflexivity");
    assert!(
        matches!(result, Ok(Some(_))),
        "superposition fallback should produce a proof for a = a"
    );
}

/// Test that the superposition fallback produces a valid proof for
/// symmetry with a hypothesis: h : a = b |- b = a.
#[test]
fn test_superposition_fallback_symmetry_with_hypothesis() {
    use clean_auto::AutomationEngine;

    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let hyp_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let target = make_eq(a_ty, b, a);

    // Step 1: verify that AutomationEngine can prove this with the hypothesis
    let engine = AutomationEngine::new();
    let hyps_with_fvar: Vec<(Expr, FVarId)> = vec![(hyp_ty.clone(), FVarId::new(0))];
    let direct = engine.try_superposition_prove_with_fvars(&env, &target, &hyps_with_fvar);
    assert!(
        direct.is_some(),
        "AutomationEngine should prove b = a from h : a = b; got None"
    );

    // Step 2: verify the proof term type-checks with a local context
    let proof_term = direct.unwrap().proof_term.clone();
    let mut check_env = env.clone();
    let _ = check_env.init_classical();
    let mut lctx = clean_kernel::LocalContext::new();
    lctx.push_with_id(
        FVarId::new(0),
        Name::from_string("h"),
        hyp_ty.clone(),
        BinderInfo::Default,
    );
    let tc = TypeChecker::with_context(&check_env, lctx);
    let inferred = tc.infer_type(&proof_term);
    assert!(
        inferred.is_ok(),
        "proof term should type-check; error: {:?}",
        inferred.err()
    );

    // Step 3: verify the tactic-level fallback
    use crate::tactic::smt::try_superposition_fallback;

    let local_decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: hyp_ty,
        value: None,
    };

    let mut state = ProofState::with_context(env, target.clone(), vec![local_decl]);
    let goal = state.current_goal().unwrap().clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_symmetry");
    assert!(
        matches!(result, Ok(Some(_))),
        "superposition fallback should produce a proof for b = a from h : a = b"
    );
}

/// Test that the superposition fallback produces a valid proof for
/// transitivity: h1 : a = b, h2 : b = c |- a = c.
#[test]
fn test_superposition_fallback_transitivity() {
    use crate::tactic::smt::try_superposition_fallback;

    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let hyp1 = LocalDecl {
        fvar: FVarId::new(0),
        name: "h1".to_string(),
        ty: make_eq(a_ty.clone(), a.clone(), b.clone()),
        value: None,
    };
    let hyp2 = LocalDecl {
        fvar: FVarId::new(1),
        name: "h2".to_string(),
        ty: make_eq(a_ty.clone(), b, c.clone()),
        value: None,
    };

    // Goal: a = c
    let target = make_eq(a_ty, a, c);

    let mut state = ProofState::with_context(env, target.clone(), vec![hyp1, hyp2]);
    let goal = state.current_goal().unwrap().clone();

    let result = try_superposition_fallback(&mut state, &goal, &target, "test_transitivity");
    assert!(
        matches!(result, Ok(Some(_))),
        "superposition fallback should produce a proof for a = c from h1 : a = b, h2 : b = c"
    );
}

// =========================================================================
// apply multi-argument-head → one subgoal per unsolved argument (#apply-multigoal)
//
// Regression coverage for the bug where `apply <head needing N explicit args>`
// left only the LAST argument metavariable as a goal. `apply_aux` now threads
// an accumulator of every argument metavariable it creates and, on the final
// unification success, turns EVERY still-unassigned argument meta into a goal
// (in argument order), matching Lean 4. Implicit args solved by unification
// stay assigned and are skipped.
// =========================================================================

/// Helper: build the target `@And P Q` for the multi-goal apply tests.
fn and_pq_target() -> Expr {
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty),
        q_ty,
    )
}

/// TOOTH 1 (unit level): `apply And.intro` on `P ∧ Q` must leave TWO subgoals
/// — `⊢ P` first, then `⊢ Q` — not just the last argument. Both are then
/// discharged and the completed proof term is kernel re-checked by close_goal /
/// instantiated_proof, producing exactly `And.intro P Q p q`.
#[test]
fn test_apply_and_intro_leaves_both_premise_goals_in_order() {
    let env = setup_env_with_and_or();
    let mut state = ProofState::new(env, and_pq_target());

    // Raw constructor const — this exercises apply_aux directly (unlike
    // `constructor`, which special-cases And through split_).
    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    apply(&mut state, and_intro).expect("apply And.intro should succeed");

    // Both premise metavariables must have become goals, in argument order.
    assert_eq!(
        state.goals().len(),
        2,
        "apply And.intro must leave one subgoal per unsolved premise (was only the last)"
    );
    assert_eq!(
        state.goals()[0].target,
        Expr::const_(Name::from_string("P"), vec![]),
        "first subgoal should be the first premise ⊢ P"
    );
    assert_eq!(
        state.goals()[1].target,
        Expr::const_(Name::from_string("Q"), vec![]),
        "second subgoal should be the second premise ⊢ Q"
    );

    // Discharge both; each close_goal kernel-checks its proof term.
    exact(&mut state, Expr::const_(Name::from_string("p"), vec![]))
        .expect("first bullet: exact p closes ⊢ P");
    exact(&mut state, Expr::const_(Name::from_string("q"), vec![]))
        .expect("second bullet: exact q closes ⊢ Q");

    assert!(
        state.is_complete(),
        "proof should complete once both premises are discharged"
    );

    // The assembled, kernel-checked proof term is exactly And.intro P Q p q.
    let mut expected = Expr::const_(Name::from_string("And.intro"), vec![]);
    expected = Expr::app(expected, Expr::const_(Name::from_string("P"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("Q"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("p"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("q"), vec![]));
    assert_eq!(
        state
            .instantiated_proof()
            .expect("completed proof should have a term"),
        expected,
        "apply And.intro then exact p / exact q should build And.intro P Q p q"
    );
}

/// TOOTH 2 (unit level, apply half): `apply Iff.intro` on `Iff P P` must leave
/// TWO subgoals `⊢ P → P` and `⊢ P → P`, not just the last. Both are closed
/// with `fun h => h` and the proof is kernel re-checked.
#[test]
fn test_apply_iff_intro_leaves_both_direction_goals() {
    let mut env = Environment::new();
    env.init_iff().expect("init_iff");

    // P : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P");

    // Target: @Iff P P
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p_ty.clone()),
        p_ty.clone(),
    );
    let mut state = ProofState::new(env, target);

    let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
    apply(&mut state, iff_intro).expect("apply Iff.intro should succeed");

    assert_eq!(
        state.goals().len(),
        2,
        "apply Iff.intro must leave both direction subgoals (mp and mpr), not just the last"
    );
    // Each direction goal is `P → P`.
    let arrow_pp = Expr::arrow(p_ty.clone(), p_ty.clone());
    assert_eq!(state.goals()[0].target, arrow_pp);
    assert_eq!(state.goals()[1].target, arrow_pp);

    // Close each direction with the identity proof `fun h : P => h`.
    let id_proof = Expr::lam(BinderInfo::Default, p_ty.clone(), Expr::bvar(0));
    exact(&mut state, id_proof.clone()).expect("close mp direction");
    exact(&mut state, id_proof).expect("close mpr direction");

    assert!(
        state.is_complete(),
        "Iff.intro proof should complete once both directions are discharged"
    );
    assert!(
        state.instantiated_proof().is_some(),
        "completed Iff.intro proof should have a kernel-checked term"
    );
}

/// TOOTH 6 (unit level, must-fail / no over-accept): `apply And.intro` with NO
/// discharge leaves TWO genuinely-unsolved goals. The proof state must NOT be
/// complete and must expose exactly 2 open goals — no dangling first-premise
/// metavariable silently swallowed into the term.
#[test]
fn test_apply_and_intro_without_discharge_leaves_two_open_goals() {
    let env = setup_env_with_and_or();
    let mut state = ProofState::new(env, and_pq_target());

    let and_intro = Expr::const_(Name::from_string("And.intro"), vec![]);
    apply(&mut state, and_intro).expect("apply And.intro should succeed");

    assert_eq!(
        state.goals().len(),
        2,
        "apply And.intro alone must leave TWO unsolved goals (regression: was 1)"
    );
    assert!(
        !state.is_complete(),
        "apply And.intro with no discharge must NOT be accepted as a complete proof"
    );
}
