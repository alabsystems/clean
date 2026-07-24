// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conv tactic tests (split from advanced.rs)
//!
//! Related test files:
//! - advanced.rs: remaining advanced tactics
//! - library_search.rs: library search tests
//! - mathlib_tactics.rs: mathlib-style tactics
//! - pattern_tactics.rs: rintro, peel, split_ifs tests
//! - propositional.rs: contrapose, push_neg, tauto tests

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

// =========================================================================
// Conv Tactic Tests
// =========================================================================

#[test]
fn test_conv_state_new() {
    let expr = Expr::const_(Name::from_string("x"), vec![]);
    let conv = ConvState::new(expr.clone());

    assert_eq!(conv.original, expr);
    assert_eq!(conv.focus, expr);
    assert!(conv.path.is_empty());
}

#[test]
fn test_conv_state_go_app_fn() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let app = Expr::app(f.clone(), x);

    let mut conv = ConvState::new(app);
    conv.go(ConvPosition::AppFn).unwrap();

    assert_eq!(conv.focus, f);
    assert_eq!(conv.path, vec![ConvPosition::AppFn]);
}

#[test]
fn test_conv_state_go_app_arg() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let app = Expr::app(f, x.clone());

    let mut conv = ConvState::new(app);
    conv.go(ConvPosition::AppArg).unwrap();

    assert_eq!(conv.focus, x);
    assert_eq!(conv.path, vec![ConvPosition::AppArg]);
}

#[test]
fn test_conv_state_go_binder_body() {
    let ty = Expr::type_();
    let body = Expr::const_(Name::from_string("x"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, ty, body.clone());

    let mut conv = ConvState::new(lam);
    conv.go(ConvPosition::BinderBody).unwrap();

    assert_eq!(conv.focus, body);
}

#[test]
fn test_conv_state_rewrite_focus() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let mut conv = ConvState::new(x.clone());
    let changed = conv.rewrite_focus(&x, &y);

    assert!(changed);
    assert_eq!(conv.focus, y);
}

#[test]
fn test_conv_state_rewrite_focus_no_match() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    let mut conv = ConvState::new(x.clone());
    let changed = conv.rewrite_focus(&y, &z);

    assert!(!changed);
    assert_eq!(conv.focus, x);
}

#[test]
fn test_conv_state_finish_at_root() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let mut conv = ConvState::new(x.clone());
    conv.rewrite_focus(&x, &y);
    let result = conv.finish();

    assert_eq!(result, y);
}

#[test]
fn test_conv_rw_fails_without_hypothesis() {
    let env = setup_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, goal);

    let err = conv_rw(&mut state, vec![], "nonexistent", false).unwrap_err();
    assert!(
        matches!(
            err,
            TacticError::HypothesisNotFound(_) | TacticError::InvalidTarget { .. }
        ),
        "conv_rw with missing hypothesis should produce HypothesisNotFound or Other, got: {err}"
    );
}

#[test]
fn test_conv_lhs_rewrite_preserves_proof_chain() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local rewrite hypothesis");

    conv_lhs(&mut state, "hxy", false).expect("conv_lhs should rewrite the lhs");
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(y.clone()), make_p(y)),
        "conv_lhs should rebuild the full equality target after rewriting"
    );

    rfl(&mut state).expect("rewritten equality should close by reflexivity");
    assert!(
        state.proof_term().is_some(),
        "conv_lhs must keep MetaId(0) connected through replace_target"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_lhs should still extract a closed proof"
    );
}

#[test]
#[serial]
fn test_conv_arg_preserves_proof_chain_on_defeq_argument_change() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyX"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("N"), vec![]),
        value: Expr::const_(Name::from_string("x"), vec![]),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: make_p(Expr::const_(Name::from_string("x"), vec![])),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, make_p(Expr::const_(Name::from_string("MyX"), vec![])));
    let axiom_before = axiom_snapshot();

    conv_arg(&mut state, |ps| change(ps, x.clone()))
        .expect("conv_arg should accept a defeq change on the focused argument");
    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "conv_arg should rebuild the application with the changed argument"
    );

    exact(&mut state, Expr::const_(Name::from_string("hp"), vec![]))
        .expect("global hp : P x should solve the rewritten goal");
    assert!(
        state.proof_term().is_some(),
        "conv_arg must keep MetaId(0) connected through replace_target"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_arg should still extract a closed proof"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "defeq conv_arg rewrite must not record trusted axioms"
    );
    assert_no_trusted_axiom_usage("conv_arg", "defeq argument change", axiom_before);
}

#[test]
#[serial]
fn test_conv_arg_rejects_non_defeq_argument_change_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_p(x.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    let err = conv_arg(&mut state, |ps| {
        // Simulate a focused sub-tactic that rewrites the argument to a
        // non-defeq term without using any trusted fallback.
        ps.current_goal_mut()
            .expect("focused argument goal should exist")
            .target = y.clone();
        Ok(())
    })
    .expect_err("direct conv_arg should reject proof-carrying non-defeq rewrites");

    assert!(
        matches!(err, TacticError::GoalMismatch(ref msg)
            if msg.contains("definitionally equal argument rewrites")),
        "expected explicit direct-conv_arg defeq error, got: {err:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "failed direct conv_arg rewrite must leave the outer goal unchanged"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed direct conv_arg rewrite must not record trusted axioms"
    );
    assert_no_trusted_axiom_usage(
        "conv_arg",
        "non-defeq argument change rejection",
        axiom_before,
    );
}

// =========================================================================
// Conv Position Tests
// =========================================================================

#[test]
fn test_conv_position_equality() {
    assert_eq!(ConvPosition::Root, ConvPosition::Root);
    assert_eq!(ConvPosition::AppFn, ConvPosition::AppFn);
    assert_eq!(ConvPosition::AppArg, ConvPosition::AppArg);
    assert_ne!(ConvPosition::AppFn, ConvPosition::AppArg);
}

#[test]
fn test_conv_state_go_fails_on_wrong_type() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut conv = ConvState::new(x);

    // Cannot go to AppFn on a non-application
    let err = conv.go(ConvPosition::AppFn).unwrap_err();
    assert!(
        matches!(
            err,
            TacticError::GoalMismatch(_) | TacticError::InvalidTarget { .. }
        ),
        "go(AppFn) on non-App should produce GoalMismatch or InvalidTarget, got: {err}"
    );
}

#[test]
fn test_conv_state_nested_navigation() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);

    // f (g x)
    let inner = Expr::app(g.clone(), x.clone());
    let outer = Expr::app(f, inner);

    let mut conv = ConvState::new(outer);

    // Go to arg (g x)
    conv.go(ConvPosition::AppArg).unwrap();
    // Go to fn of that (g)
    conv.go(ConvPosition::AppFn).unwrap();

    assert_eq!(conv.focus, g);
    assert_eq!(conv.path.len(), 2);
}

// =========================================================================
// Conv navigation + reconstruct_conv_target (#2477)
// =========================================================================

/// Test: conv_nav stores navigation original and path on ProofState.
///
/// Verifies that conv_nav populates `ps.conv_nav_original` and
/// `ps.conv_nav_path` so eval_conv_goal can reconstruct the full
/// expression after body rewrites. Part of #2477.
#[test]
fn test_conv_nav_stores_navigation_state() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: @Eq N x y
    let target = make_eq_n(x.clone(), y.clone());
    let mut state = ProofState::new(env, target.clone());

    // Before navigation: no conv state stored
    assert!(state.conv_nav.is_none(), "no nav state before conv_nav");

    // Navigate to LHS
    builtins::conv_nav(&mut state, ConvPosition::EqLhs)
        .expect("conv_nav to EqLhs should succeed on an equality");

    // After navigation: original and path stored
    let (ref orig, ref path) = *state.conv_nav.as_ref().expect("conv_nav must be set");
    assert_eq!(orig, &target, "conv_nav must store the original target");
    assert_eq!(
        path,
        &vec![ConvPosition::EqLhs],
        "conv_nav must record the navigation path"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        x,
        "conv_nav must set the goal target to the focused sub-expression"
    );
}

/// Test: chained conv_nav accumulates path.
///
/// Simulates `lhs` then navigating into an App arg within the LHS.
/// The accumulated path should have both positions so reconstruction
/// can place the modified focus back into the original full expression.
#[test]
fn test_conv_nav_chained_accumulates_path() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Build P(x) = P(y) so LHS is an application P(x)
    let px = make_p(x.clone());
    let py = make_p(y.clone());
    let target = make_eq(Expr::prop(), px.clone(), py);
    let mut state = ProofState::new(env, target.clone());

    // Navigate: lhs → focuses on P(x)
    builtins::conv_nav(&mut state, ConvPosition::EqLhs).expect("nav to EqLhs");
    assert_eq!(state.current_goal().unwrap().target, px);

    // Navigate: AppArg → focuses on x (arg of P)
    builtins::conv_nav(&mut state, ConvPosition::AppArg).expect("nav to AppArg");
    assert_eq!(state.current_goal().unwrap().target, x);

    // Path should be [EqLhs, AppArg]
    let (ref orig, ref path) = *state.conv_nav.as_ref().expect("conv_nav must be set");
    assert_eq!(path, &vec![ConvPosition::EqLhs, ConvPosition::AppArg]);
    assert_eq!(
        orig, &target,
        "original stays as the full pre-navigation target"
    );
}

/// Test: ConvState::replace_at_position correctly reconstructs after
/// navigation to EqRhs and modification (symmetric to the LHS test).
///
/// Part of #2477.
#[test]
fn test_conv_reconstruct_after_rhs_rewrite() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    // Original: @Eq N x y
    let original = make_eq_n(x.clone(), y);
    let path = vec![ConvPosition::EqRhs];

    // Simulate: body rewrote RHS from y to z
    let reconstructed =
        ConvState::replace_at_position(&original, &path, &z).expect("reconstruction must succeed");

    // Should be @Eq N x z
    let expected = make_eq_n(x, z);
    assert_eq!(
        reconstructed, expected,
        "replacing EqRhs in @Eq N x y with z should produce @Eq N x z"
    );
}

/// Test: ConvState::replace_at_position correctly reconstructs after
/// deep nested path [EqLhs, AppArg].
///
/// Part of #2477.
#[test]
fn test_conv_reconstruct_after_deep_lhs_arg_rewrite() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    // Original: @Eq Prop P(x) P(y)  (i.e., make_eq(Prop, P(x), P(y)))
    let px = Expr::app(p.clone(), x);
    let py = Expr::app(p.clone(), y.clone());
    let original = make_eq(Expr::prop(), px, py);
    let path = vec![ConvPosition::EqLhs, ConvPosition::AppArg];

    // Simulate: navigated to LHS (P(x)), then to AppArg (x), replaced with z
    let reconstructed = ConvState::replace_at_position(&original, &path, &z)
        .expect("deep reconstruction must succeed");

    // Should be @Eq Prop P(z) P(y)
    let pz = Expr::app(p.clone(), z);
    let py2 = Expr::app(p, y);
    let expected = make_eq(Expr::prop(), pz, py2);
    assert_eq!(
        reconstructed, expected,
        "replacing [EqLhs, AppArg] in @Eq Prop P(x) P(y) with z should produce @Eq Prop P(z) P(y)"
    );
}

/// Test: ConvState::replace_at_position correctly reconstructs through a nested
/// let-value path.
///
/// Part of #2532.
#[test]
fn test_conv_reconstruct_after_nested_let_value_rewrite() {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let original = Expr::let_named(
        Name::anon(),
        n_ty.clone(),
        z.clone(),
        Expr::let_named(
            Name::anon(),
            n_ty.clone(),
            Expr::app(f.clone(), x.clone()),
            make_p(x.clone()),
            false,
        ),
        false,
    );
    let path = vec![
        ConvPosition::LetBody,
        ConvPosition::LetValue,
        ConvPosition::AppArg,
    ];

    let reconstructed = ConvState::replace_at_position(&original, &path, &y)
        .expect("nested let-value reconstruction must succeed");

    let expected = Expr::let_named(
        Name::anon(),
        n_ty.clone(),
        z,
        Expr::let_named(Name::anon(), n_ty, Expr::app(f, y), make_p(x), false),
        false,
    );
    assert_eq!(
        reconstructed, expected,
        "replacing [LetBody, LetValue, AppArg] should rewrite only the nested let value"
    );
}

/// Test: let-path reconstruction preserves let binder metadata.
///
/// Part of #2532.
#[test]
fn test_conv_reconstruct_after_let_value_rewrite_preserves_let_metadata() {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let original = Expr::let_named(
        Name::from_string("tmp"),
        n_ty.clone(),
        x,
        Expr::bvar(0),
        true,
    );

    let reconstructed = ConvState::replace_at_position(&original, &[ConvPosition::LetValue], &y)
        .expect("let-value reconstruction must succeed");

    let expected = Expr::let_named(Name::from_string("tmp"), n_ty, y, Expr::bvar(0), true);
    assert_eq!(
        reconstructed, expected,
        "let-value reconstruction must preserve the original let name and non_dep flag"
    );
}

/// Test: ConvState::replace_at_position correctly reconstructs after
/// navigation to EqLhs and modification.
///
/// Simulates the reconstruction that eval_conv_goal does when the conv
/// body navigates to a sub-expression and rewrites it.
#[test]
fn test_conv_reconstruct_after_lhs_rewrite() {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    // Original: @Eq N x y
    let original = make_eq_n(x, y.clone());
    let path = vec![ConvPosition::EqLhs];

    // Simulate: body rewrote LHS from x to z
    let reconstructed =
        ConvState::replace_at_position(&original, &path, &z).expect("reconstruction must succeed");

    // Should be @Eq N z y
    let expected = make_eq_n(z, y);
    assert_eq!(
        reconstructed, expected,
        "replacing EqLhs in @Eq N x y with z should produce @Eq N z y"
    );
}

/// Test: conv_rhs rewrite preserves proof chain.
///
/// Mirrors test_conv_lhs_rewrite_preserves_proof_chain but rewrites the RHS
/// of an equality instead of the LHS. Covers the symmetrical `conv_rhs` path
/// that was previously untested.
/// Part of #2477.
#[test]
fn test_conv_rhs_rewrite_preserves_proof_chain() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hyx").expect("intro should create the local rewrite hypothesis");

    // conv_rhs rewrites RHS = P(y) using hyx : y = x → P(x)
    conv_rhs(&mut state, "hyx", false).expect("conv_rhs should rewrite the rhs");
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq(Expr::prop(), make_p(x.clone()), make_p(x.clone())),
        "conv_rhs should rebuild the full equality target after rewriting RHS"
    );

    rfl(&mut state).expect("rewritten equality should close by reflexivity");
    assert!(
        state.proof_term().is_some(),
        "conv_rhs must keep MetaId(0) connected through replace_target"
    );
    assert!(
        state.closed_proof().is_some(),
        "conv_rhs should still extract a closed proof"
    );
}

/// Test: conv_rw with a deep [AppArg, AppArg] path preserves proof chain.
///
/// Exercises multi-step navigation: goal is `f (P x) = f (P y)`, rewrites the
/// innermost argument `x` in the LHS via path [EqLhs, AppArg, AppArg] using
/// hypothesis hxy : x = y. This ensures ConvState.finish() correctly
/// reconstructs nested applications after a deep-path rewrite.
/// Part of #2477.
#[test]
fn test_conv_rw_deep_path_preserves_proof_chain() {
    let mut env = setup_env_with_full_eq();
    // Add Q : N → N (a function from N to N, so f(Q(x)) is well-typed)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("N"), vec![]),
            Expr::const_(Name::from_string("N"), vec![]),
        ),
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let qx = Expr::app(q.clone(), x.clone());
    let qy = Expr::app(q.clone(), y.clone());

    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(qx, qy.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality hypothesis");

    // Deep-path rewrite: navigate into LHS → AppArg of Q(x) → rewrites x to y
    conv_rw(
        &mut state,
        vec![ConvPosition::EqLhs, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("conv_rw with deep path should succeed");

    // After rewrite: Q(y) = Q(y)
    let expected = make_eq_n(qy.clone(), qy);
    assert_eq!(
        state.current_goal().unwrap().target,
        expected,
        "deep-path conv_rw should rewrite x→y inside LHS application argument"
    );

    rfl(&mut state).expect("Q(y) = Q(y) should close by rfl");
    assert!(
        state.proof_term().is_some(),
        "deep-path conv_rw must keep MetaId(0) chain connected"
    );
    assert!(
        state.closed_proof().is_some(),
        "deep-path conv_rw should still extract a closed proof"
    );
}

/// Test: conv_rhs with navigation reconstruction preserves proof chain.
///
/// Symmetric counterpart to test_conv_lhs_navigation_reconstruction_proof_chain.
/// Goal: P(x) = P(y), navigates to RHS (P(y)), rewrites y→x using hypothesis
/// hyx : y = x, verifying that the RHS reconstruction path through
/// ConvState::replace_at_position works end-to-end.
/// Part of #2477.
#[test]
fn test_conv_rhs_navigation_reconstruction_proof_chain() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let px = make_p(x.clone());
    let py = make_p(y.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), px.clone(), py),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hyx").expect("intro should create the local equality hypothesis");

    // conv_rhs rewrites RHS = P(y) using hyx : y = x → P(x)
    conv_rhs(&mut state, "hyx", false).expect("conv_rhs should succeed");

    // After rewrite: P(x) = P(x)
    let expected_target = make_eq(Expr::prop(), px.clone(), px);
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_target,
        "conv_rhs should produce P(x) = P(x) after rewriting y→x in RHS"
    );

    rfl(&mut state).expect("P(x) = P(x) should close by rfl");
    assert!(
        state.proof_term().is_some(),
        "MetaId(0) chain must remain connected after conv_rhs + rfl"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof must extract through the conv_rhs navigation chain"
    );
}

/// Test: conv_lhs rewrite preserves proof chain with navigation reconstruction.
///
/// This is the end-to-end scenario: conv_lhs navigates to LHS, rewrites
/// via a hypothesis, and the proof chain through MetaId(0) stays connected.
/// Part of #2477.
#[test]
fn test_conv_lhs_navigation_reconstruction_proof_chain() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: P(x) = P(y) (equality in Prop)
    let px = make_p(x.clone());
    let py = make_p(y.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq(Expr::prop(), px.clone(), py.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality hypothesis");

    // conv_lhs rewrites LHS = P(x) using hxy : x = y → P(y)
    conv_lhs(&mut state, "hxy", false).expect("conv_lhs should succeed");

    // After rewrite: P(y) = P(y)
    let expected_target = make_eq(Expr::prop(), py.clone(), py);
    assert_eq!(
        state.current_goal().unwrap().target,
        expected_target,
        "conv_lhs should produce P(y) = P(y) after rewriting x→y in LHS"
    );

    // Close with rfl
    rfl(&mut state).expect("P(y) = P(y) should close by rfl");
    assert!(
        state.proof_term().is_some(),
        "MetaId(0) chain must remain connected after conv_lhs + rfl"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof must extract through the conv navigation chain"
    );
}

// =========================================================================
// #2519: Conv goal proof-carry trust-aware regressions
// =========================================================================

/// Test: conv_lhs proof-carry produces zero trusted axioms.
///
/// Exercises `conv_lhs` → `conv_rw` (the direct API in `conv.rs`), which
/// was already proof-producing. Verifies no trustedArith is needed for
/// the supported equality/application nav path.
///
/// NOTE: This exercises `conv_lhs` → `conv_rw`, not `eval_conv_goal`.
/// The compound handler path (`conv => body`) is covered by
/// `test_conv_goal_compound_*` in `conv_proof_carry.rs`.
///
/// Part of #2519.
#[test]
fn test_conv_lhs_rewrite_zero_trusted_axioms() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (x = y) → P(x) = P(y)
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro");

    // conv_lhs rewrites P(x) → P(y)
    conv_lhs(&mut state, "hxy", false).expect("conv_lhs should succeed");
    rfl(&mut state).expect("rfl after conv_lhs");

    assert!(
        state.proof_term().is_some(),
        "proof chain must stay connected"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "conv_lhs proof-carry must not use trustedArith"
    );
}

/// Test: conv_rhs proof-carry produces zero trusted axioms.
///
/// Same coverage note as `test_conv_lhs_rewrite_zero_trusted_axioms`:
/// exercises `conv_rhs` → `conv_rw`, not `eval_conv_goal`.
///
/// Part of #2519.
#[test]
fn test_conv_rhs_rewrite_zero_trusted_axioms() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    // Goal: (y = x) → P(x) = P(y)
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(y.clone(), x.clone()),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hyx").expect("intro");

    // conv_rhs rewrites P(y) → P(x) using hyx : y = x (forward: y→x)
    conv_rhs(&mut state, "hyx", false).expect("conv_rhs should succeed");
    rfl(&mut state).expect("rfl after conv_rhs");

    assert!(
        state.proof_term().is_some(),
        "proof chain must stay connected"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "conv_rhs proof-carry must not use trustedArith"
    );
}
