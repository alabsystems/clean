// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for close_goal guard and close_fvars FVar->BVar conversion (#1700).
#![allow(deprecated)]

use super::*;
use crate::tactic::core::close_fvars;
use crate::MetaState;
use clean_kernel::expr::{ExprKind, ZFCSetExpr};
use clean_kernel::FVarId;
use std::sync::Arc;

#[test]
fn test_close_goal_empty_goals_returns_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    // Close the first (and only) goal
    let proof = Expr::const_(Name::from_string("a"), vec![]);
    state.close_goal_unchecked(proof.clone()).unwrap();

    // Now goals are empty — close_goal should return NoGoals, not panic
    let result = state.close_goal_unchecked(proof);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "close_goal on empty goals should return NoGoals, got: {result:?}"
    );
}

#[test]
fn test_close_goal_assign_failure_returns_error_and_preserves_goal() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    let proof = Expr::const_(Name::from_string("a"), vec![]);

    let goal_meta_id = state.current_goal().unwrap().meta_id;
    assert!(
        state.metas.assign(goal_meta_id, proof.clone()),
        "setup should pre-assign main metavariable"
    );

    let result = state.close_goal_unchecked(proof);
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("failed to assign proof")),
        "close_goal should return TypeCheckFailed error, got: {result:?}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "failed assignment should not drop the active goal"
    );
}

#[test]
fn test_close_goal_rejects_goal_context_widening() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target.clone());
    let escaped = state.fresh_fvar();
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: escaped,
        name: "forged".into(),
        ty: target,
        value: None,
    });

    let result = state.close_goal_unchecked(Expr::fvar(escaped));
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("widens metavariable")),
        "post-creation goal widening must fail closed, got: {result:?}"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "failed close must preserve the goal"
    );
}

#[test]
fn test_close_goal_rejects_retyped_creation_local() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let local = LocalDecl {
        fvar: FVarId::new(100),
        name: "h".into(),
        ty: a.clone(),
        value: None,
    };
    let mut state = ProofState::with_context(env, a, vec![local]);
    state.current_goal_mut().unwrap().local_ctx[0].ty = b;

    let result = state.close_goal_unchecked(Expr::fvar(FVarId::new(100)));
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("retypes local")),
        "post-creation local retyping must fail closed, got: {result:?}"
    );
}

#[test]
fn test_close_goal_rejects_wider_nested_metavariable() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target.clone());
    let escaped = FVarId::new(100);
    let nested = state
        .metas
        .fresh_with_locals(target.clone(), vec![("escaped".into(), escaped, target)]);

    let result = state.close_goal_unchecked(Expr::fvar(MetaState::to_fvar(nested)));
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("nested metavariable") && msg.contains("out-of-scope")),
        "a delayed nested-meta escape must fail closed, got: {result:?}"
    );
}

#[test]
fn test_close_goal_rejects_retargeted_goal() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::new(env, a);
    state.current_goal_mut().unwrap().target = b;

    let result = state.close_goal_unchecked(Expr::const_(Name::from_string("a"), vec![]));
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("target is not definitionally equal")),
        "post-creation retargeting must fail closed, got: {result:?}"
    );
}

#[test]
fn test_closed_proof_closes_intro_assumption_fvar() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    assumption(&mut state).unwrap();
    assert!(
        state.is_complete(),
        "intro/assumption should complete A -> A"
    );

    let instantiated = state
        .instantiated_proof()
        .expect("complete proof state should have instantiated_proof");
    assert!(
        matches!(instantiated.kind(), ExprKind::Lam(_, _, body) if matches!(body.kind(), ExprKind::FVar(_))),
        "instantiated proof should still contain an FVar in lambda body: {instantiated:?}"
    );

    let closed = state
        .closed_proof()
        .expect("complete proof state should have closed_proof");
    assert!(
        matches!(closed.kind(), ExprKind::Lam(_, _, body) if matches!(body.kind(), ExprKind::BVar(0))),
        "closed proof should convert lambda body to BVar(0): {closed:?}"
    );
}

#[test]
fn test_close_fvars_identity() {
    // A constant expression should be unchanged
    let c = Expr::const_(Name::from_string("Nat"), vec![]);
    let result = close_fvars(&c, 0);
    assert_eq!(result, c);
}

#[test]
fn test_close_fvars_single_binder() {
    // FVar(0) at depth 1 should become BVar(0) (the innermost binder)
    let fvar = Expr::fvar(FVarId::new(0));
    let result = close_fvars(&fvar, 1);
    assert_eq!(result, Expr::from_kind(ExprKind::BVar(0)));
}

#[test]
fn test_close_fvars_nested_binders() {
    // FVar(0) at depth 3 -> BVar(2) (outermost binder of 3)
    let fvar0 = Expr::fvar(FVarId::new(0));
    assert_eq!(close_fvars(&fvar0, 3), Expr::from_kind(ExprKind::BVar(2)));

    // FVar(1) at depth 3 -> BVar(1) (middle binder)
    let fvar1 = Expr::fvar(FVarId::new(1));
    assert_eq!(close_fvars(&fvar1, 3), Expr::from_kind(ExprKind::BVar(1)));

    // FVar(2) at depth 3 -> BVar(0) (innermost binder)
    let fvar2 = Expr::fvar(FVarId::new(2));
    assert_eq!(close_fvars(&fvar2, 3), Expr::from_kind(ExprKind::BVar(0)));
}

#[test]
fn test_close_fvars_out_of_scope_preserved() {
    // FVar(5) at depth 2 should be preserved (5 >= 2, not introduced by any enclosing binder)
    let fvar5 = Expr::fvar(FVarId::new(5));
    let result = close_fvars(&fvar5, 2);
    assert_eq!(result, fvar5);
}

#[test]
fn test_close_fvars_app() {
    // App(FVar(0), FVar(1)) at depth 2 -> App(BVar(1), BVar(0))
    let app = Expr::from_kind(ExprKind::App(
        Arc::new(Expr::fvar(FVarId::new(0))),
        Arc::new(Expr::fvar(FVarId::new(1))),
    ));
    let result = close_fvars(&app, 2);

    let expected = Expr::from_kind(ExprKind::App(
        Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    assert_eq!(result, expected);
}

#[test]
fn test_close_fvars_lambda_increments_depth() {
    use clean_kernel::BinderInfo;

    // Lambda body: FVar(0) at depth 0+1=1 -> BVar(0)
    let lam = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(Expr::type_()),
        Arc::new(Expr::fvar(FVarId::new(0))),
    ));
    let result = close_fvars(&lam, 0);

    let expected = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(Expr::type_()),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    assert_eq!(result, expected);
}

#[test]
fn test_close_fvars_pi_increments_depth() {
    use clean_kernel::BinderInfo;

    // Pi body should close under the binder depth increment
    let pi = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(Expr::type_()),
        Arc::new(Expr::fvar(FVarId::new(0))),
    ));
    let result = close_fvars(&pi, 0);

    let expected = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(Expr::type_()),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    assert_eq!(result, expected);
}

#[test]
fn test_close_fvars_sprop_and_squash() {
    let sprop = Expr::from_kind(ExprKind::SProp);
    assert_eq!(close_fvars(&sprop, 0), sprop);

    let squash = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::fvar(FVarId::new(0)))));
    let expected = Expr::from_kind(ExprKind::Squash(Arc::new(Expr::from_kind(ExprKind::BVar(
        0,
    )))));
    assert_eq!(close_fvars(&squash, 1), expected);
}

#[test]
fn test_close_fvars_cubical_paths_and_hcomp() {
    let path_lam = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(Expr::fvar(FVarId::new(0))),
    });
    let path_lam_expected = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    });
    assert_eq!(close_fvars(&path_lam, 0), path_lam_expected);

    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::fvar(FVarId::new(0))),
        phi: Arc::new(Expr::fvar(FVarId::new(1))),
        u: Arc::new(Expr::fvar(FVarId::new(0))),
        base: Arc::new(Expr::fvar(FVarId::new(2))),
    });
    let hcomp_expected = Expr::from_kind(ExprKind::CubicalHComp {
        ty: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        phi: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
        u: Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        base: Arc::new(Expr::fvar(FVarId::new(2))),
    });
    assert_eq!(close_fvars(&hcomp, 2), hcomp_expected);
}

#[test]
fn test_close_fvars_zfc_separation_and_comprehension() {
    let separation = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: Arc::new(Expr::fvar(FVarId::new(0))),
        pred: Arc::new(Expr::fvar(FVarId::new(1))),
    }));
    let separation_expected = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
        pred: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    }));
    assert_eq!(close_fvars(&separation, 1), separation_expected);

    let comprehension = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::fvar(FVarId::new(0))),
        pred: Arc::new(Expr::fvar(FVarId::new(1))),
    });
    let comprehension_expected = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
        pred: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    });
    assert_eq!(close_fvars(&comprehension, 1), comprehension_expected);
}

#[test]
fn test_close_fvars_bvar_unchanged() {
    // BVar(3) should pass through unchanged regardless of depth
    let bvar = Expr::from_kind(ExprKind::BVar(3));
    assert_eq!(close_fvars(&bvar, 0), bvar.clone());
    assert_eq!(close_fvars(&bvar, 10), bvar);
}

#[test]
fn test_close_fvars_depth_zero_preserves_all_fvars() {
    // At depth 0, no FVar can satisfy n < 0, so all FVars are preserved
    let fvar = Expr::fvar(FVarId::new(0));
    assert_eq!(close_fvars(&fvar, 0), fvar);
}

#[test]
fn test_close_fvars_gap_in_fvar_ids_preserves_unbound_gap() {
    // Gap case: FVar(2) at depth 2 is out-of-scope and should remain an FVar.
    let expr = Expr::from_kind(ExprKind::App(
        Arc::new(Expr::fvar(FVarId::new(0))),
        Arc::new(Expr::fvar(FVarId::new(2))),
    ));
    let expected = Expr::from_kind(ExprKind::App(
        Arc::new(Expr::from_kind(ExprKind::BVar(1))),
        Arc::new(Expr::fvar(FVarId::new(2))),
    ));
    assert_eq!(close_fvars(&expr, 2), expected);
}

/// Regression test for #1602: deeply nested expressions (1000+ depth) must not
/// stack overflow thanks to `stack_safe` guards in `close_fvars`.
#[test]
fn test_close_fvars_deep_nesting_no_stack_overflow() {
    // Build a deeply nested App chain: App(App(App(..., leaf), leaf), leaf)
    // with depth 2000 — well beyond typical default stack limits.
    let leaf = Expr::fvar(FVarId::new(0));
    let mut expr = leaf.clone();
    for _ in 0..2000 {
        expr = Expr::from_kind(ExprKind::App(Arc::new(expr), Arc::new(leaf.clone())));
    }

    // This should complete without stack overflow due to stack_safe guard.
    // At depth 1, FVar(0) -> BVar(0).
    let result = close_fvars(&expr, 1);

    // Verify the result is an App (we don't need to check the full structure,
    // just that it completed successfully and has the right shape).
    assert!(
        matches!(result.kind(), ExprKind::App(_, _)),
        "deeply nested close_fvars should produce an App, got: {:?}",
        result.kind()
    );
}

// =============================================================================
// Post-hoc type check at elaboration boundary (#2154)
// =============================================================================

/// Verify that a correct proof from goal-transforming tactics (intro +
/// assumption) produces a closed proof that type-checks against the target.
/// intro uses checked close_goal via fix_pi_leaked_fvars (#2197).
/// This is a regression test for the post-hoc type check in elab_by_tactic.
/// Part of #2154.
#[test]
fn test_posthoc_typecheck_intro_assumption_valid() {
    use clean_kernel::tc::TypeChecker;

    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);
    let mut state = ProofState::new(env.clone(), target.clone());

    // intro x; assumption — intro uses checked close_goal (#2197 fix)
    intro(&mut state, "x").unwrap();
    assumption(&mut state).unwrap();
    assert!(state.is_complete());

    let proof = state.closed_proof().expect("should produce closed proof");

    // Post-hoc type check: the same logic as elab_by_tactic
    let tc = TypeChecker::new(&env);
    let inferred_ty = tc.infer_type(&proof).expect("proof should be well-typed");
    assert!(
        tc.is_def_eq(&inferred_ty, &target),
        "proof type {inferred_ty:?} should match target {target:?}"
    );
}

/// Verify that the post-hoc type check logic rejects a deliberately
/// ill-typed proof. Constructs a proof of the wrong type and confirms
/// that the type check fails. Part of #2154.
#[test]
fn test_posthoc_typecheck_rejects_wrong_proof_type() {
    use clean_kernel::tc::TypeChecker;

    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a.clone()); // A → A

    // Construct a wrong proof: λ (x : A), f x  (which has type A → B, not A → A)
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let wrong_proof = Expr::lam(BinderInfo::Default, a, Expr::app(f, Expr::bvar(0)));

    let tc = TypeChecker::new(&env);
    let inferred_ty = tc
        .infer_type(&wrong_proof)
        .expect("wrong proof is still well-typed");

    // The inferred type should be A → B, NOT A → A
    assert!(
        !tc.is_def_eq(&inferred_ty, &target),
        "wrong proof type {inferred_ty:?} should NOT match target {target:?} — \
         post-hoc check would reject this"
    );
}

// =============================================================================
// fix_pi_leaked_fvars regression test (#2197)
// =============================================================================

/// Regression test for #2197: infer_type(Lambda) FVar leak (single binder).
///
/// The intro tactic constructs a Lambda proof term. Before the fix, the
/// tactic-level `infer_type` returned a Pi with FVars from the tactic
/// context instead of BVars, causing checked `close_goal` to fail with
/// a false type mismatch (Pi(FVar) != Pi(BVar)).
///
/// The `fix_pi_leaked_fvars` post-processing step in `ProofState::infer_type`
/// abstracts leaked FVars back to BVars, allowing the checked path to succeed.
///
/// See also: `test_intro_uses_checked_close_goal_nested_binders` for the
/// multi-binder case.
#[test]
fn test_intro_uses_checked_close_goal_single_binder() {
    // intro on A → A constructs Lambda(Default, A, ?meta) — a top-level Lambda.
    // close_goal infers its type via infer_type, which must return Pi(Default, A, A)
    // with BVars (not FVars). fix_pi_leaked_fvars ensures this.
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a.clone(), a);
    let mut state = ProofState::new(env, target);

    // intro calls close_goal (checked) — would fail without fix_pi_leaked_fvars
    intro(&mut state, "x").expect("intro should succeed with checked close_goal (#2197 fix)");

    // The new goal should be provable by assumption
    assumption(&mut state).expect("assumption should close the goal");
    assert!(
        state.is_complete(),
        "proof should be complete after intro + assumption"
    );
}

/// Same as above but with nested binders: A → B → A.
/// This exercises the recursive case in fix_pi_leaked_fvars where
/// inner Pi types also need FVar→BVar fixup.
#[test]
fn test_intro_uses_checked_close_goal_nested_binders() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let target = Expr::arrow(a.clone(), Expr::arrow(b, a));
    let mut state = ProofState::new(env, target);

    // Two intros → two Lambda constructions, each going through checked close_goal
    intro(&mut state, "x").expect("first intro should succeed (#2197 fix)");
    intro(&mut state, "y").expect("second intro should succeed (#2197 nested fix)");
    assumption(&mut state).expect("assumption should close the goal");
    assert!(state.is_complete());
}

// =============================================================================
// fix_pi_leaked_fvars: dependent Pi types (regression tests for #2459 fix)
// =============================================================================

/// Intro on `(A : Type) → A → A` — the polymorphic identity function's type.
///
/// This is a DEPENDENT Pi where the codomain `A → A` references the binder
/// variable `A` via BVar. The kernel's infer_type on the Lambda proof returns
/// a Pi with leaked FVars (FVar(fv_A) instead of BVar) that fix_pi_leaked_fvars
/// must re-abstract. The previous inside-out recursion in fix_pi_leaked_fvars
/// corrupted de Bruijn indices: it produced Pi(BVar(0), BVar(0)) instead of
/// Pi(BVar(0), BVar(1)), causing a TypeMismatch in close_goal.
#[test]
fn test_intro_dependent_pi_identity_type() {
    let env = setup_env();
    // (A : Type) → A → A  in de Bruijn: Pi(Type, Pi(BVar(0), BVar(1)))
    let target = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let mut state = ProofState::new(env, target);

    // intro A — this triggers fix_pi_leaked_fvars on the resulting Pi
    intro(&mut state, "A").expect(
        "intro on (A : Type) → A → A should succeed — \
         fix_pi_leaked_fvars must produce Pi(BVar(0), BVar(1)) not Pi(BVar(0), BVar(0))",
    );

    // The new goal should be `A → A` where A is a local FVar
    assert_eq!(
        state.goals().len(),
        1,
        "should have exactly one remaining goal"
    );

    // intro a — introduces the `a : A` hypothesis
    intro(&mut state, "a").expect("intro a on A → A should succeed");

    // assumption — closes with hypothesis `a : A`
    assumption(&mut state).expect("assumption should close the goal");
    assert!(
        state.is_complete(),
        "proof of (A : Type) → A → A should be complete"
    );
}

/// Intro on `(A : Type) → (B : Type) → (A → B) → A → B` — polymorphic
/// function application, with multiple dependent binders.
///
/// Tests that fix_pi_leaked_fvars correctly handles multiple BVar depths
/// in the codomain.
#[test]
fn test_intro_dependent_pi_multi_binder() {
    let env = setup_env();
    // (A : Type) → (B : Type) → (A → B) → A → B
    // In de Bruijn:
    //   Pi(Type,            -- A
    //     Pi(Type,          -- B
    //       Pi(Pi(BVar(1), BVar(1)),  -- A → B (BVar(1)=A, BVar(1)=B at this depth)
    //         Pi(BVar(2),   -- A (shifted by 3 binders from outermost)
    //           BVar(2))))) -- B
    let target = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(2)),
            ),
        ),
    );
    let mut state = ProofState::new(env, target);

    // Four intros: A, B, f, a
    intro(&mut state, "A").expect("intro A");
    intro(&mut state, "B").expect("intro B");
    intro(&mut state, "f").expect("intro f");
    intro(&mut state, "a").expect("intro a");

    // Goal should be B, provable by `f a` (apply f then exact a)
    // We can test with just assumption if goal is a hypothesis type
    assert_eq!(state.goals().len(), 1);
    // B is a local type, not directly an assumption — but this validates
    // that all 4 intros succeeded without de Bruijn corruption
}

// =============================================================================
// fix_pi_leaked_fvars error path (#2227)
// =============================================================================

/// When all leaked FVars in a Pi body also appear in the domain, the
/// disambiguation heuristic cannot determine which FVar is the binder
/// variable. Before #2227, this silently returned the Pi with leaked FVars.
/// Now it returns an error.
#[test]
fn test_fix_pi_leaked_fvars_error_on_ambiguous_multi_leak() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap().clone();

    // Construct two FVars that are NOT in the goal's local context,
    // NOT elab locals, and NOT meta-FVars (regular FVarIds).
    let fv1 = FVarId::new(9000);
    let fv2 = FVarId::new(9001);

    // Build a Pi where BOTH leaked FVars appear in the domain AND body:
    //   Pi(App(FVar(9000), FVar(9001)), App(FVar(9000), FVar(9001)))
    // Both fv1 and fv2 are leaked (not in context), and both appear in
    // the domain, so the heuristic cannot find one NOT in the domain.
    let domain = Expr::app(Expr::fvar(fv1), Expr::fvar(fv2));
    let body = Expr::app(Expr::fvar(fv1), Expr::fvar(fv2));
    let pi = Expr::pi(BinderInfo::Default, domain, body);

    let result = state.fix_pi_leaked_fvars(&goal, &pi);
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref msg)) if msg.contains("cannot disambiguate")),
        "fix_pi_leaked_fvars should error when all leaked FVars appear in domain, got: {result:?}"
    );
}

/// `clear` removes a local from the goal's context but does NOT re-mint the
/// goal's metavariable, so the cleared local stays in that meta's immutable
/// scope AND stays bound by a live `lambda` in the already-committed parent
/// assignment. A subsequent `intro` must therefore not reuse its id: the
/// id-to-depth arithmetic in `close_fvars` would resolve the new local to the
/// cleared binder, and `assignment_scope_violation` cannot object because the
/// reused id reads as the local it aliases.
#[test]
fn test_intro_after_clear_does_not_reuse_the_cleared_binder_id() {
    let env = setup_env();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let b_ty = Expr::const_(Name::from_string("B"), vec![]);
    let goal_ty = Expr::arrow(
        a_ty,
        Expr::arrow(b_ty, Expr::const_(Name::from_string("A"), vec![])),
    );
    let mut state = ProofState::new(env, goal_ty);

    intro(&mut state, "a").expect("intro a");
    intro(&mut state, "b").expect("intro b");
    let b_id = state.current_goal().unwrap().local_ctx[1].fvar;
    let meta_before = state.current_goal().unwrap().meta_id;

    clear(&mut state, "b").expect("clear b");

    let goal = state.current_goal().unwrap().clone();
    assert_eq!(
        goal.meta_id, meta_before,
        "precondition: clear narrows the context WITHOUT re-minting the meta"
    );
    assert!(
        state
            .metas
            .get(goal.meta_id)
            .expect("goal meta")
            .locals
            .iter()
            .any(|(_, fvar, _)| *fvar == b_id),
        "precondition: the cleared local is still in the meta's creation scope"
    );
    assert_eq!(
        state.goal_fvar_base(&goal),
        b_id.as_u64(),
        "precondition: the narrowed CONTEXT alone would hand back the cleared id"
    );
    assert!(
        state.goal_binder_base(&goal) > b_id.as_u64(),
        "the next intro must mint strictly above the cleared-but-still-bound `b`"
    );
}
