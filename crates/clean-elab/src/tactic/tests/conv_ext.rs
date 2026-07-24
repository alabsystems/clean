// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for conv_ext, conv_congr, conv_change, and eval_conv (#3082)
//!
//! Split from conv.rs per the 1000-line test file limit.

use super::*;
use clean_kernel::env::Declaration;

// =========================================================================
// conv_ext tests
// =========================================================================

#[test]
fn test_conv_ext_opens_lambda_binder() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    // Goal: λ (x : N), P(x)
    let body = make_p(Expr::bvar(0));
    let lam = Expr::lam(BinderInfo::Default, n_ty.clone(), body);
    let mut state = ProofState::new(env, lam);
    let original_meta = state.current_goal().unwrap().meta_id;

    conv_ext(&mut state, "a").expect("conv_ext should succeed on a lambda");

    let goal = state.current_goal().expect("should have a goal");
    assert_ne!(
        goal.meta_id, original_meta,
        "opening a binder must mint a distinct scratch metavariable instead of retargeting the old one"
    );
    // The body should have BVar(0) replaced with an FVar
    // Check that the local context contains the new variable "a" with type N
    let a_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "a")
        .expect("local context should contain 'a'");
    assert_eq!(
        a_decl.ty, n_ty,
        "introduced variable should have the binder's domain type"
    );
    // The target should contain the FVar, not BVar(0)
    assert!(
        !matches!(goal.target.kind(), ExprKind::BVar(0)),
        "body should not be a bare BVar(0) after ext"
    );
    let scratch_meta = state
        .metas()
        .get(goal.meta_id)
        .expect("opened scratch goal must have a registered metavariable");
    assert_eq!(scratch_meta.ty, goal.target);
    assert!(
        scratch_meta
            .locals
            .iter()
            .any(|(_, fvar, ty)| *fvar == a_decl.fvar && *ty == a_decl.ty),
        "opened binder must be captured in the scratch metavariable's exact context"
    );
    assert!(
        state
            .metas()
            .get(original_meta)
            .expect("original scratch metavariable must remain registered")
            .locals
            .is_empty(),
        "binder navigation must not widen the original metavariable scope"
    );
}

#[test]
fn test_conv_ext_opens_pi_binder() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    // Goal: ∀ (x : N), P(x)
    let body = make_p(Expr::bvar(0));
    let pi = Expr::pi(BinderInfo::Default, n_ty.clone(), body);
    let mut state = ProofState::new(env, pi);

    conv_ext(&mut state, "b").expect("conv_ext should succeed on a forall");

    let goal = state.current_goal().expect("should have a goal");
    let b_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "b")
        .expect("local context should contain 'b'");
    assert_eq!(
        b_decl.ty, n_ty,
        "introduced variable should have the binder's domain type"
    );
}

#[test]
fn test_conv_ext_fails_on_non_binder() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, x);

    let err = conv_ext(&mut state, "a").unwrap_err();
    assert!(
        matches!(err, TacticError::InvalidTarget { .. }),
        "conv_ext on a non-binder should produce InvalidTarget, got: {err}"
    );
}

// =========================================================================
// conv_congr tests
// =========================================================================

#[test]
fn test_conv_congr_descends_into_argument_single_focus() {
    // `conv_congr` now opens a multi-focus TREE (one focus per head + argument)
    // and defaults the cursor to the LAST argument, narrowing the goal target to
    // it. This preserves the proven single-focus behaviour of `congr; rw`
    // (descend into the last argument) while enabling explicit `arg i` to select
    // any sub-focus for the N-ary form. This test pins the default-cursor focus.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    // Goal: P(x) -- an application App(P, x)
    let goal = make_p(x.clone());
    let mut state = ProofState::new(env, goal);

    conv_congr(&mut state).expect("conv_congr should succeed on an application");

    // Exactly ONE goal remains (no disconnected split); the focus is the arg `x`.
    assert_eq!(
        state.goals.len(),
        1,
        "conv_congr must keep a single focus goal (no disconnected meta split)"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        x,
        "conv_congr should narrow the focus to the application's last argument"
    );
    // The multi-focus tree is recorded for the reconstruction boundary, with the
    // cursor defaulting to the single argument (component index 1).
    assert!(
        state.conv_focus_tree.is_some(),
        "conv_congr records a multi-focus tree"
    );
    assert_eq!(
        state.conv_congr_cursor.as_deref(),
        Some(&[1usize][..]),
        "conv_congr should default the cursor to the (single) last argument"
    );
}

#[test]
fn test_conv_congr_descends_into_last_argument_multi_arg() {
    // For a multi-argument application `@Eq N x y` the sound single-focus route
    // descends into the LAST argument (`y`), recording one AppArg step. There is
    // NO multi-goal split: the single-focus witness model can soundly carry one
    // focus, and a following rewrite lifts via `congrArg` through that path.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: @Eq N x y = App(App(App(Eq, N), x), y)
    let target = make_eq_n(x.clone(), y.clone());
    let mut state = ProofState::new(env, target);

    conv_congr(&mut state).expect("conv_congr should succeed on a multi-arg application");

    assert_eq!(
        state.goals.len(),
        1,
        "conv_congr must keep a single focus goal on a multi-arg application"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        y,
        "conv_congr should narrow the focus to the last argument"
    );
}

#[test]
fn test_conv_congr_fails_on_non_application() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, x);

    let err = conv_congr(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::GoalMismatch(_)),
        "conv_congr on a non-application should produce GoalMismatch, got: {err}"
    );
}

// =========================================================================
// conv_change tests
// =========================================================================

#[test]
fn test_conv_change_succeeds_with_defeq_expression() {
    let mut env = setup_env_with_full_eq();
    // Define MyX := x (reducible)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyX"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("N"), vec![]),
        value: Expr::const_(Name::from_string("x"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    let my_x = Expr::const_(Name::from_string("MyX"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let goal = make_p(my_x);
    let mut state = ProofState::new(env, goal);

    // Change from P(MyX) to P(x) -- MyX is definitionally equal to x
    conv_change(&mut state, make_p(x.clone())).expect("conv_change with defeq should succeed");
    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "conv_change should update the target"
    );
}

#[test]
fn test_conv_change_fails_with_non_defeq_expression() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = ProofState::new(env, make_p(x));

    let err = conv_change(&mut state, make_p(y)).unwrap_err();
    assert!(
        matches!(err, TacticError::GoalMismatch(_)),
        "conv_change with non-defeq should produce GoalMismatch, got: {err}"
    );
}

// =========================================================================
// eval_conv tests
// =========================================================================

#[test]
fn test_eval_conv_no_change() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());
    let mut state = ProofState::new(env, target.clone());

    // Conv body that does nothing
    eval_conv(&mut state, |_ps| Ok(())).expect("eval_conv with no changes should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        target,
        "eval_conv with no changes should preserve the target"
    );
}

#[test]
fn test_eval_conv_body_error_propagates() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, make_p(x.clone()));

    // Conv body that fails
    let err = eval_conv(&mut state, |_ps| Err(TacticError::NoGoals)).unwrap_err();

    assert!(
        matches!(err, TacticError::NoGoals),
        "eval_conv should propagate body errors, got: {err}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "eval_conv should leave target unchanged on body error"
    );
}

#[test]
fn test_eval_conv_with_navigation() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = make_eq_n(x.clone(), y.clone());
    let mut state = ProofState::new(env, target);

    // Navigate to LHS inside conv body
    eval_conv(&mut state, |ps| builtins::conv_nav(ps, ConvPosition::EqLhs))
        .expect("eval_conv with nav should succeed");

    // The focus was changed to x, but since we didn't modify it,
    // the reconstruct should produce the same target
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(x, y),
        "eval_conv with navigation but no rewrite should preserve target"
    );
}
