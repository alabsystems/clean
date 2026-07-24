// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Position-specific conv_rw path tests (binder body/type, let body/value/type).
//!
//! Split from `conv_proof_carry.rs` as part of #2547.
//! Part of #2504.

use super::*;

#[test]
#[serial]
fn test_conv_rw_binder_body_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = Expr::pi(
        BinderInfo::Default,
        n_ty.clone(),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
    );
    let goal = Expr::pi(BinderInfo::Default, make_eq_n(x.clone(), y.clone()), target);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![
            ConvPosition::BinderBody,
            ConvPosition::EqLhs,
            ConvPosition::AppArg,
        ],
        "hxy",
        false,
    )
    .expect("binder-body conv_rw should lift the rewrite proof through the Pi body");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::pi(
            BinderInfo::Default,
            n_ty,
            make_eq(Expr::prop(), make_p(y.clone()), make_p(y.clone())),
        ),
        "binder-body conv_rw should rewrite only the selected occurrence"
    );

    intro(&mut state, "n").expect("Pi target should still introduce after the rewrite");
    rfl(&mut state).expect("rewritten binder-body target should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rw binder body", axiom_before);
    assert!(
        state.closed_proof().is_some(),
        "binder-body conv_rw must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_binder_type_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_p(y.clone()),
            Expr::pi(BinderInfo::Default, make_p(x.clone()), make_p(y.clone())),
        ),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    intro(&mut state, "hy").expect("intro should add the witness for the rewritten type");
    let axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![ConvPosition::BinderType, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("binder-type conv_rw should lift the rewrite proof through the Pi type");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::pi(BinderInfo::Default, make_p(y.clone()), make_p(y.clone())),
        "binder-type conv_rw should rewrite the focused binder type"
    );

    intro(&mut state, "hy2").expect("rewritten Pi target should remain introducible");
    let hy2 = local_fvar_by_name(&state, "hy2");
    exact(&mut state, Expr::fvar(hy2))
        .expect("the rewritten binder assumption should close the goal");
    assert_no_trusted_fallback(&state, "conv_rw binder type", axiom_before);
    assert!(
        state.closed_proof().is_some(),
        "binder-type conv_rw must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_let_body_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = Expr::let_named(
        Name::anon(),
        n_ty.clone(),
        x.clone(),
        make_eq(Expr::prop(), make_p(x.clone()), make_p(y.clone())),
        false,
    );
    let goal = Expr::pi(BinderInfo::Default, make_eq_n(x.clone(), y.clone()), target);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    let axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![
            ConvPosition::LetBody,
            ConvPosition::EqLhs,
            ConvPosition::AppArg,
        ],
        "hxy",
        false,
    )
    .expect("let-body conv_rw should lift the rewrite proof through the let body");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::let_named(
            Name::anon(),
            n_ty,
            x,
            make_eq(Expr::prop(), make_p(y.clone()), make_p(y.clone())),
            false,
        ),
        "let-body conv_rw should rewrite the selected occurrence inside the let body"
    );

    norm_beta(&mut state).expect("let-body target should zeta reduce after the rewrite");
    rfl(&mut state).expect("rewritten let-body target should close by reflexivity");
    assert_no_trusted_fallback(&state, "conv_rw let body", axiom_before);
    assert!(
        state.closed_proof().is_some(),
        "let-body conv_rw must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_let_value_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_p(y.clone()),
            Expr::let_named(
                Name::anon(),
                n_ty.clone(),
                x.clone(),
                make_p(Expr::bvar(0)),
                false,
            ),
        ),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    intro(&mut state, "hy").expect("intro should add a witness for the rewritten let body");
    let axiom_before = axiom_snapshot();

    conv_rw(&mut state, vec![ConvPosition::LetValue], "hxy", false)
        .expect("let-value conv_rw should lift the rewrite proof through the let value");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::let_named(Name::anon(), n_ty, y.clone(), make_p(Expr::bvar(0)), false),
        "let-value conv_rw should rewrite only the let-bound value"
    );

    norm_beta(&mut state).expect("let-value target should zeta reduce after the rewrite");
    let hy = local_fvar_by_name(&state, "hy");
    exact(&mut state, Expr::fvar(hy))
        .expect("the post-rewrite witness should solve the zeta-reduced target");
    assert_no_trusted_fallback(&state, "conv_rw let value", axiom_before);
    assert!(
        state.closed_proof().is_some(),
        "let-value conv_rw must preserve closed_proof() extraction"
    );
}

#[test]
#[serial]
fn test_conv_rw_let_type_path_preserves_proof_chain_without_trust() {
    reset_all_counters();
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_p(y.clone()),
            Expr::let_named(
                Name::anon(),
                make_p(x.clone()),
                x.clone(),
                make_p(y.clone()),
                false,
            ),
        ),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality proof");
    intro(&mut state, "hy").expect("intro should add a witness for the rewritten goal");
    let axiom_before = axiom_snapshot();

    conv_rw(
        &mut state,
        vec![ConvPosition::LetType, ConvPosition::AppArg],
        "hxy",
        false,
    )
    .expect("let-type conv_rw should lift the rewrite proof through the let type");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::let_named(Name::anon(), make_p(y.clone()), x, make_p(y.clone()), false),
        "let-type conv_rw should rewrite only the let-bound type annotation"
    );

    norm_beta(&mut state).expect("let-type target should zeta reduce after the rewrite");
    let hy = local_fvar_by_name(&state, "hy");
    exact(&mut state, Expr::fvar(hy))
        .expect("the post-rewrite witness should solve the zeta-reduced target");
    assert_no_trusted_fallback(&state, "conv_rw let type", axiom_before);
    assert!(
        state.closed_proof().is_some(),
        "let-type conv_rw must preserve closed_proof() extraction"
    );
}
