// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality and conversion tactic tests: change/show, rfl_closure, norm_beta,
//! assert, set extensionality, quot extensionality, simp_rw, decide_eq.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;

// =========================================================================
// Change/Show Tactic Tests
// =========================================================================

#[test]
fn test_change_updates_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // change to the same type should succeed (trivially def-eq)
    change(&mut state, a.clone()).unwrap();
    assert_eq!(state.goals[0].target, a);
}

#[test]
fn test_change_rejects_non_defeq() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);

    // change to a non-definitionally-equal type must fail (soundness)
    let result = change(&mut state, b);
    assert!(result.is_err(), "change must reject non-defeq types");
}

#[test]
fn test_show_is_alias_for_change() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // show (alias for change) with the same type should succeed
    show(&mut state, a.clone()).unwrap();
    assert_eq!(state.goals[0].target, a);
}

#[test]
fn test_change_at_updates_hypothesis() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // Add a hypothesis
    let fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a.clone(),
        value: None,
    });

    // Changing to the same type (trivially def-eq) should succeed
    change_at(&mut state, "h", a.clone()).unwrap();
    assert_eq!(state.goals[0].local_ctx[0].ty, a);
}

#[test]
fn test_change_at_rejects_non_defeq() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // Add a hypothesis with type A
    let fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a,
        value: None,
    });

    // Changing to unrelated type B must fail
    let result = change_at(&mut state, "h", b);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("not definitionally equal"))
    );
}

#[test]
fn test_change_at_fails_on_missing_hyp() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = change_at(&mut state, "nonexistent", b);
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(_))));
}

// =========================================================================
// change/change_at boundary condition tests (#1846)
// =========================================================================

#[test]
fn test_change_at_soundness_rejects_false_injection() {
    // Regression test for the soundness hole fixed in W3 commit e65252c87.
    // Before the fix, change_at allowed replacing any hypothesis type with
    // an arbitrary type (e.g., False), enabling unsound proofs.
    let mut env = setup_env();
    env.init_true_false().unwrap();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // Add hypothesis h : A
    let fvar = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: a,
        value: None,
    });

    // Attempting to change h to False must fail — False is not def-eq to A
    let result = change_at(&mut state, "h", false_ty);
    assert!(
        result.is_err(),
        "change_at must reject False injection (soundness)"
    );
}

#[test]
fn test_change_accepts_beta_reducible_type() {
    // (fun x : Type => x) A is beta-equivalent to A.
    // The WHNF check should reduce the beta redex and accept this.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    // Goal target: A
    let mut state = ProofState::new(env, a.clone());

    // Build (fun x : Type => x) A — beta-reduces to A
    use clean_kernel::BinderInfo;
    let id_fn = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let beta_a = Expr::app(id_fn, a.clone());

    // change to beta-equivalent type should succeed
    let result = change(&mut state, beta_a.clone());
    assert!(result.is_ok(), "change should accept beta-equivalent types");
    // After change, goal target should be the beta-redex form, not the reduced A
    assert_eq!(state.goals.len(), 1, "change should preserve single goal");
    assert_eq!(
        state.goals[0].target, beta_a,
        "change should update goal target to the new (beta-equivalent) type"
    );
}

#[test]
fn test_change_at_with_multiple_hypotheses_targets_correct_one() {
    // Verify that change_at only modifies the named hypothesis, not others
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    // Add two hypotheses
    let fvar1 = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: fvar1,
        name: "h1".to_string(),
        ty: a.clone(),
        value: None,
    });
    let fvar2 = state.fresh_fvar();
    state.goals[0].local_ctx.push(LocalDecl {
        fvar: fvar2,
        name: "h2".to_string(),
        ty: b.clone(),
        value: None,
    });

    // Change h1 to same type (trivially def-eq)
    change_at(&mut state, "h1", a.clone()).unwrap();

    // Verify h1 was changed and h2 was NOT touched
    assert_eq!(state.goals[0].local_ctx[0].ty, a);
    assert_eq!(state.goals[0].local_ctx[1].ty, b);

    // Attempting to change h2 to type A (not def-eq to B) must fail
    let err =
        change_at(&mut state, "h2", a).expect_err("change_at with non-def-eq type should fail");
    assert!(
        matches!(err, TacticError::GoalMismatch(_)),
        "expected GoalMismatch for non-def-eq type change, got: {err:?}"
    );
}

/// Regression test for #1846: change should accept types that are
/// definitionally equal via delta reduction of nested subexpressions,
/// even when WHNF structural comparison fails.
///
/// Before #1846 fix, `change` used `old_whnf == new_whnf` which only
/// compares WHNF forms structurally. WHNF only reduces the head, so
/// `f MyA` and `f A` (where `def MyA := A`) have different WHNF forms
/// despite being definitionally equal. The fix uses `is_def_eq` which
/// handles delta reduction at all positions.
#[test]
fn test_change_accepts_delta_reducible_nested_subexpr() {
    let mut env = setup_env();

    // Add a definition: MyA := A (delta-reducible)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyA"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::const_(Name::from_string("A"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // Goal target: f MyA (where f : A → B)
    let f_my_a = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("MyA"), vec![]),
    );
    let mut state = ProofState::new(env, f_my_a);

    // change to f A — def-eq via delta(MyA) = A, but different WHNF structure
    let f_a = Expr::app(
        Expr::const_(Name::from_string("f"), vec![]),
        Expr::const_(Name::from_string("A"), vec![]),
    );
    let result = change(&mut state, f_a.clone());
    assert!(
        result.is_ok(),
        "change should accept delta-reducible nested subexpressions (#1846), got: {result:?}"
    );
    assert_eq!(state.goals[0].target, f_a);
}

/// Same regression test for change_at: delta-reducible hypothesis types.
#[test]
fn test_change_at_accepts_delta_reducible_nested_subexpr() {
    let mut env = setup_env();

    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyA"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::const_(Name::from_string("A"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Fam"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let goal_ty = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, goal_ty);

    // Hypothesis h : Fam MyA
    let fvar = state.fresh_fvar();
    let f_my_a = Expr::app(
        Expr::const_(Name::from_string("Fam"), vec![]),
        Expr::const_(Name::from_string("MyA"), vec![]),
    );
    state.goals[0].local_ctx.push(LocalDecl {
        fvar,
        name: "h".to_string(),
        ty: f_my_a,
        value: None,
    });

    // change_at h to Fam A
    let f_a = Expr::app(
        Expr::const_(Name::from_string("Fam"), vec![]),
        Expr::const_(Name::from_string("A"), vec![]),
    );
    let result = change_at(&mut state, "h", f_a.clone());
    assert!(
        result.is_ok(),
        "change_at should accept delta-reducible nested subexpressions (#1846), got: {result:?}"
    );
    assert_eq!(state.goals[0].local_ctx[0].ty, f_a);
}

/// Regression test for #1846 AC3: change should accept eta-equivalent types.
///
/// `(fun x : A => f x)` is eta-equivalent to `f` (where `f : A -> B`).
/// The old WHNF structural check rejected this because WHNF does NOT
/// perform eta reduction — `f` and `fun x => f x` have different WHNF
/// forms. The kernel's `is_def_eq` handles this via `try_eta_expansion_impl`.
#[test]
fn test_change_accepts_eta_equivalent_type() {
    let env = setup_env();
    use clean_kernel::BinderInfo;

    // f : A -> B (axiom, not delta-reducible)
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // Goal target: f (a term of type A → B)
    let mut state = ProofState::new(env, f.clone());

    // Eta-expanded form: fun (x : A) => f x
    // WHNF of f = f (no reduction)
    // WHNF of (fun x : A => f x) = (fun x : A => f x) (lambda is WHNF)
    // Old code: f != (fun x : A => f x) structurally → REJECTS
    // New code: is_def_eq uses eta expansion → ACCEPTS
    let eta_f = Expr::lam(BinderInfo::Default, a_type, Expr::app(f, Expr::bvar(0)));

    let result = change(&mut state, eta_f.clone());
    assert!(
        result.is_ok(),
        "change should accept eta-equivalent types (#1846 AC3), got: {result:?}"
    );
    assert_eq!(state.goals[0].target, eta_f);
}

// =========================================================================
// Rfl Closure Tests
// =========================================================================

#[test]
fn test_rfl_closure_succeeds_on_rfl() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let eq_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Goal: a = a
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                eq_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let mut state = ProofState::new(env, eq_goal);
    // rfl_closure should try rfl first
    rfl_closure(&mut state).expect("rfl_closure should succeed on a = a");
    // rfl on a = a should close the goal completely
    assert!(state.is_complete(), "rfl_closure should close a = a goal");
}

#[test]
fn test_rfl_closure_fails_on_non_equality() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = rfl_closure(&mut state);
    assert!(matches!(result, Err(TacticError::NoProgress { .. })));
}

/// Regression test for #2474: rfl_closure must not leak state on failure.
///
/// The old rfl_closure called rfl()/exact() directly without
/// try_tactic_preserving_state. If rfl internally mutates the proof state
/// (e.g., via apply) before failing, the mutation leaked into subsequent
/// Iff/HEq branches. This test verifies that on failure the goals list,
/// next_fvar counter, and meta scope depth are all restored.
#[test]
fn test_rfl_closure_preserves_state_on_failure() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // Goal: a = B — ill-typed equality that rfl cannot close.
    // This forces all three rfl_closure branches (rfl, Iff.rfl, HEq.rfl)
    // to attempt and fail.
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("A"), vec![]),
            ),
            a,
        ),
        b,
    );

    let mut state = ProofState::new(env, goal);

    // Snapshot pre-call state
    let goals_before = state.goals.len();
    let goal_target_before = state.goals[0].target.clone();
    let scope_depth_before = state.metas().scope_depth();
    let next_fvar_before = state.next_fvar;

    let result = rfl_closure(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoProgress { .. })),
        "rfl_closure should fail on a = B"
    );

    // Verify state restoration
    assert_eq!(
        state.goals.len(),
        goals_before,
        "goals list length must be preserved after rfl_closure failure"
    );
    assert_eq!(
        state.goals[0].target, goal_target_before,
        "goal target must be preserved after rfl_closure failure"
    );
    assert_eq!(
        state.metas().scope_depth(),
        scope_depth_before,
        "meta scope depth must be preserved (no leaked scopes)"
    );
    assert_eq!(
        state.next_fvar, next_fvar_before,
        "next_fvar counter must be preserved"
    );
}

/// Regression test for #2474: trivial must not leak state on failure.
///
/// The old trivial called assumption() then rfl() directly without
/// try_tactic_preserving_state. If assumption internally mutates state
/// before failing, rfl runs on corrupted state.
#[test]
fn test_trivial_preserves_state_on_failure() {
    let env = setup_env();
    // Goal: A (a type, not a provable Prop) — neither assumption nor rfl can close this.
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let goals_before = state.goals.len();
    let goal_target_before = state.goals[0].target.clone();
    let scope_depth_before = state.metas().scope_depth();
    let next_fvar_before = state.next_fvar;

    let result = trivial(&mut state);
    assert!(result.is_err(), "trivial should fail on non-provable goal");

    assert_eq!(
        state.goals.len(),
        goals_before,
        "goals list length must be preserved after trivial failure"
    );
    assert_eq!(
        state.goals[0].target, goal_target_before,
        "goal target must be preserved after trivial failure"
    );
    assert_eq!(
        state.metas().scope_depth(),
        scope_depth_before,
        "meta scope depth must be preserved (no leaked scopes)"
    );
    assert_eq!(
        state.next_fvar, next_fvar_before,
        "next_fvar counter must be preserved"
    );
}

/// Regression test for #2474: tauto must not leak state on failure.
///
/// tauto calls rfl, trivial, assumption in its fallback chain. Without
/// try_tactic_preserving_state wrapping, each failed tactic can leak
/// partial mutations to subsequent branches.
#[test]
fn test_tauto_preserves_state_on_failure() {
    let env = setup_env();
    // Goal: A (a type, not a Prop) — rfl, trivial, assumption all fail.
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let goals_before = state.goals.len();
    let goal_target_before = state.goals[0].target.clone();
    let scope_depth_before = state.metas().scope_depth();
    let next_fvar_before = state.next_fvar;

    let result = tauto(&mut state);
    assert!(result.is_err(), "tauto should fail on non-Prop goal");

    assert_eq!(
        state.goals.len(),
        goals_before,
        "goals list length must be preserved after tauto failure"
    );
    assert_eq!(
        state.goals[0].target, goal_target_before,
        "goal target must be preserved after tauto failure"
    );
    assert_eq!(
        state.metas().scope_depth(),
        scope_depth_before,
        "meta scope depth must be preserved (no leaked scopes)"
    );
    assert_eq!(
        state.next_fvar, next_fvar_before,
        "next_fvar counter must be preserved"
    );
}

// =========================================================================
// Norm Beta Tests
// =========================================================================

#[test]
fn test_norm_beta_fails_on_irreducible() {
    let env = setup_env();
    // A simple constant cannot be beta-reduced
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = norm_beta(&mut state);
    assert!(matches!(result, Err(TacticError::NoProgress { .. })));
}

// =========================================================================
// Assert Tactic Tests
// =========================================================================

#[test]
fn test_assert_creates_two_goals() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);

    assert_eq!(state.goals.len(), 1);

    assert_(&mut state, "h", b.clone()).unwrap();

    // Should have 2 goals: first to prove B, second the original with h : B
    assert_eq!(state.goals.len(), 2);
    assert_eq!(state.goals[0].target, b);
}

#[test]
fn test_assert_after_creates_goals_in_reverse_order() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a.clone());

    assert_after(&mut state, "h", b.clone()).unwrap();

    // Should have 2 goals: first the original with h : B, second to prove B
    assert_eq!(state.goals.len(), 2);
    // After swap, original goal (with h added) should be first
    // The assertion's target is the original plus hyp, proof goal is B
    assert_eq!(state.goals[1].target, b);
}

#[test]
fn test_assert_adds_hypothesis() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);

    assert_(&mut state, "h", b.clone()).unwrap();

    // The second goal (continuation) should have h in context
    let cont_goal = &state.goals[1];
    assert!(cont_goal
        .local_ctx
        .iter()
        .any(|d| d.name == "h" && d.ty == b));
}

// =========================================================================
// Set Extensionality Tests
// =========================================================================

#[test]
fn test_set_ext_fails_on_non_equality() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = set_ext(&mut state, "x");
    assert!(matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("equality")));
}

fn setup_set_ext_checked_env() -> (Environment, Expr, Expr, Expr) {
    let mut env = Environment::with_prelude();
    env.init_funext().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("propext"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)),
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        Name::from_string("Eq"),
                                        vec![Level::succ(Level::zero())],
                                    ),
                                    Expr::prop(),
                                ),
                                Expr::bvar(3),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    })
    // `propext` is now provided by `with_prelude` (the quotient `Rat` carrier
    // uses it), so tolerate the duplicate registration here.
    .ok();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let set_ty = Expr::pi(BinderInfo::Default, a_ty.clone(), Expr::prop());
    for name in ["s", "t"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: set_ty.clone(),
        })
        .unwrap();
    }

    (
        env,
        a_ty,
        Expr::const_(Name::from_string("s"), vec![]),
        Expr::const_(Name::from_string("t"), vec![]),
    )
}

#[test]
fn test_set_ext_creates_pointwise_iff_goal() {
    let (env, a_ty, s, t) = setup_set_ext_checked_env();
    let set_ty = Expr::pi(BinderInfo::Default, a_ty.clone(), Expr::prop());
    let goal_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                set_ty,
            ),
            s.clone(),
        ),
        t.clone(),
    );

    let mut state = ProofState::new(env, goal_ty);
    set_ext(&mut state, "x").unwrap();

    let goal = state
        .current_goal()
        .expect("set_ext should leave one subgoal");
    assert_eq!(goal.local_ctx.len(), 1, "set_ext should intro one binder");
    assert_eq!(goal.local_ctx[0].name, "x");
    assert_eq!(goal.local_ctx[0].ty, a_ty);

    let x = Expr::fvar(goal.local_ctx[0].fvar);
    let expected = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Iff"), vec![]),
            Expr::app(s, x.clone()),
        ),
        Expr::app(t, x),
    );
    assert_eq!(
        goal.target, expected,
        "set_ext should reduce to the pointwise iff goal"
    );
}

// =========================================================================
// Quot Ext Tests
// =========================================================================

#[test]
fn test_quot_ext_fails_without_quotient() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = quot_ext(&mut state);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref s)) if s.contains("quotient") || s.contains("equality"))
    );
}

// =========================================================================
// Simp_rw Tests
// =========================================================================

#[test]
fn test_simp_rw_fails_with_no_lemmas() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    // No lemmas and no simp rules apply
    let result = simp_rw(&mut state, vec![]);
    assert!(matches!(result, Err(TacticError::NoProgress { .. })));
}

#[test]
fn test_simp_rw_hyps_conversion() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    // Test that string slice conversion works
    let result = simp_rw_hyps(&mut state, vec!["h1", "h2"]);
    // Will fail because lemmas don't exist, but conversion should work
    assert!(matches!(result, Err(TacticError::NoProgress { .. })));
}

// Conv position tests: see conv.rs

// =========================================================================
// decide_eq Tests
// =========================================================================

#[test]
fn test_decide_eq_fails_on_non_equality_non_decidable() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = decide_eq(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_decide_eq_on_equal_nat_literals() {
    // setup_env() lacks Eq/rfl infrastructure, so decide_eq must fail even on 5 = 5
    let env = setup_env();
    let five = Expr::nat_lit(5);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            five.clone(),
        ),
        five.clone(),
    );
    let mut state = ProofState::new(env, eq_goal);

    let result = decide_eq(&mut state);
    // Without Eq.refl in the environment, decide_eq cannot construct a reflexivity proof
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "rfl" || constant == "Eq.refl"),
        "decide_eq should fail without Eq infrastructure, got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after decide_eq failure"
    );
}

#[test]
fn test_decide_eq_on_different_nat_literals() {
    let env = setup_env();
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            five,
        ),
        six,
    );
    let mut state = ProofState::new(env, eq_goal);

    let result = decide_eq(&mut state);
    assert!(
        matches!(result, Err(TacticError::ArithmeticFailed { ref tactic, .. }) if tactic == "decide_eq"),
        "should be ArithmeticFailed from decide_eq, got: {result:?}"
    );
}

#[test]
fn test_match_decidable_eq_pattern() {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);

    // Build: Decidable (Eq Nat 5 6)
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            five.clone(),
        ),
        six.clone(),
    );
    let decidable_expr = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );

    let result = match_decidable_eq(&decidable_expr);
    let result = result.expect("expected Some");
    let (ty, lhs, rhs) = result;
    assert_eq!(ty, nat_ty);
    assert_eq!(lhs, five);
    assert_eq!(rhs, six);
}

#[test]
fn test_decide_eq_is_false_has_implicit_prop_arg() {
    // Regression test for #2461 F3: Decidable.isFalse must include the implicit
    // {p : Prop} argument. Without it, the proof term is ill-typed:
    //   App(Decidable.isFalse, ne_proof)                — 1 arg, WRONG
    //   App(App(Decidable.isFalse, eq_prop), ne_proof)  — 2 args, CORRECT
    //
    // Part of #302: decide_eq now requires the kernel noConfusion path for
    // Nat disequality instead of falling back to trustedAy.
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_nat().unwrap();
    env.init_decidable().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            five,
        ),
        six,
    );
    let decidable_goal = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );
    let mut state = ProofState::new(env, decidable_goal);

    let result = decide_eq(&mut state);
    assert!(result.is_ok(), "decide_eq should solve Decidable (5 = 6)");
    assert!(state.is_complete(), "goal should be closed");

    let proof = state
        .proof_term()
        .expect("completed state should have proof term");
    let head = proof.get_app_fn();
    let args = proof.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isFalse",
            "proof head should be Decidable.isFalse, got: {name}",
        );
    } else {
        panic!(
            "proof head should be Const (Decidable.isFalse), got: {:?}",
            head.kind()
        );
    }

    assert_eq!(
        args.len(),
        2,
        "Decidable.isFalse needs 2 args (implicit {{p}} + ne_proof), got {} (#2461 F3)",
        args.len()
    );
}

#[test]
fn test_decidable_type_check() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let custom = Expr::const_(Name::from_string("CustomType"), vec![]);

    assert!(decidable_type_check(&nat));
    assert!(decidable_type_check(&bool_ty));
    assert!(!decidable_type_check(&custom));
}

#[test]
fn test_eval_to_nat_literals() {
    let five = Expr::nat_lit(5);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    assert_eq!(eval_to_nat(&five), Some(5));
    assert_eq!(eval_to_nat(&zero), Some(0));
}

#[test]
fn test_eval_to_nat_succ() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);

    assert_eq!(eval_to_nat(&succ_zero), Some(1));
}

/// Smoke test for decide_eq with FVar hypotheses in the goal context.
///
/// Verifies that decide_eq doesn't crash or produce wrong errors when the
/// goal target contains FVars from local hypotheses. The is_def_eq check
/// for `n = n` passes via structural identity (def_eq.rs:238: `a == b`)
/// regardless of context, so this test exercises the overall code path
/// (match_equality → is_def_eq → rfl) rather than specifically testing
/// local context availability.
///
/// A stronger test of the #2212 fix would need non-identical expressions
/// that are definitionally equal only with FVar type information (e.g.,
/// eta-expanded FVars or projection reduction over FVar types).
///
/// Re: #2212, #2229
#[test]
fn test_decide_eq_equality_with_fvar_hypothesis() {
    let env = setup_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Create hypothesis n : Nat in goal context
    let n_fvar = FVarId::new(42);
    let local_decl = LocalDecl {
        fvar: n_fvar,
        name: "n".to_string(),
        ty: nat_ty.clone(),
        value: None,
    };

    // Goal: ⊢ n = n (where n is a local FVar)
    let n_expr = Expr::fvar(n_fvar);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            n_expr.clone(),
        ),
        n_expr,
    );
    let mut state = ProofState::with_context(env, eq_goal, vec![local_decl]);

    let result = decide_eq(&mut state);
    // is_def_eq(n, n) passes via structural identity, then rfl() is called.
    // rfl fails because setup_env() lacks Eq.refl infrastructure, but the
    // error should come from the rfl path, not the "cannot evaluate equality"
    // fallthrough (which would indicate is_def_eq returned false).
    if let Err(ref e) = result {
        let msg = e.to_string();
        assert!(
            !msg.contains("cannot evaluate equality"),
            "decide_eq fell through to eval_to_nat instead of taking rfl path: {msg}"
        );
    }
}
