// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};

use crate::tactic::TacticError;

fn mk_eq_subst_cast(old_ty: Expr, from: Expr, to: Expr, eq_proof: Expr, proof_expr: Expr) -> Expr {
    let eq_type = Expr::const_(Name::from_string("N"), vec![]);
    let motive = super::super::equality::abstract_over(&old_ty, &from);
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(eq_subst, eq_type.clone()),
                        Expr::lam(BinderInfo::Default, eq_type.clone(), motive),
                    ),
                    from,
                ),
                to,
            ),
            eq_proof,
        ),
        proof_expr,
    )
}

fn local_fvar(state: &ProofState, name: &str) -> FVarId {
    state
        .current_goal()
        .expect("test state should have a current goal")
        .local_ctx
        .iter()
        .find(|decl| decl.name == name)
        .map(|decl| decl.fvar)
        .expect("named local should exist")
}

fn build_validation_goal_with_replaced_local(
    state: &mut ProofState,
    hyp_name: &str,
    new_ty: Expr,
) -> Goal {
    let goal = state
        .current_goal()
        .expect("test state should have a current goal")
        .clone();
    let hyp_idx = goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == hyp_name)
        .expect("named local should exist");
    let old_decl = goal.local_ctx[hyp_idx].clone();
    let new_fvar = state.fresh_fvar();
    let replacement = Expr::fvar(new_fvar);

    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx] = LocalDecl {
        fvar: new_fvar,
        name: old_decl.name.clone(),
        ty: new_ty,
        value: None,
    };

    let new_target = goal.target.subst_fvar(old_decl.fvar, &replacement);
    for decl in new_ctx.iter_mut().skip(hyp_idx + 1) {
        decl.ty = decl.ty.subst_fvar(old_decl.fvar, &replacement);
        decl.value = decl
            .value
            .as_ref()
            .map(|value| value.subst_fvar(old_decl.fvar, &replacement));
    }

    Goal {
        meta_id: goal.meta_id,
        target: new_target,
        local_ctx: new_ctx,
        tag: goal.tag,
    }
}

fn setup_change_at_proof_carry_state() -> (ProofState, FVarId, FVarId, Expr) {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let beta_a = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
        a.clone(),
    );
    let goal = Expr::pi(
        BinderInfo::Default,
        beta_a,
        Expr::pi(BinderInfo::Default, a.clone(), a.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create h");
    intro(&mut state, "hy").expect("intro should create hy");
    let old_h_fvar = local_fvar(&state, "h");
    let hy_fvar = local_fvar(&state, "hy");
    (state, old_h_fvar, hy_fvar, a)
}

fn setup_unfold_at_proof_carry_state() -> (ProofState, FVarId, FVarId, Expr) {
    let mut env = setup_env();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
        value: a.clone(),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::prop(),
        ),
    })
    .unwrap();

    let target = Expr::app(Expr::const_(Name::from_string("P"), vec![]), a.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        Expr::app(
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("mydef"), vec![]),
        ),
        Expr::pi(BinderInfo::Default, target.clone(), target.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create h");
    intro(&mut state, "hy").expect("intro should create hy");
    let old_h_fvar = local_fvar(&state, "h");
    let hy_fvar = local_fvar(&state, "hy");
    (state, old_h_fvar, hy_fvar, target)
}

#[test]
fn test_replace_local_decl_with_cast_preserves_proof_extraction() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_p(x.clone()),
            Expr::pi(BinderInfo::Default, make_p(y.clone()), make_p(y.clone())),
        ),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h_eq").expect("intro should create h_eq");
    intro(&mut state, "h_target").expect("intro should create h_target");
    intro(&mut state, "hy").expect("intro should create hy");
    let h_eq_fvar = local_fvar(&state, "h_eq");
    let h_target_fvar = local_fvar(&state, "h_target");
    let hy_fvar = local_fvar(&state, "hy");
    let initial_meta = state.current_goal().unwrap().meta_id;

    let cast = mk_eq_subst_cast(
        make_p(x.clone()),
        x,
        y.clone(),
        Expr::fvar(h_eq_fvar),
        Expr::fvar(h_target_fvar),
    );

    state
        .replace_local_decl_with_cast(h_target_fvar, make_p(y.clone()), cast)
        .expect("local replacement with cast should succeed");

    let goal = state.current_goal().unwrap();
    let h_target = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h_target")
        .expect("rewritten hypothesis should still be present");
    assert_ne!(
        h_target.fvar, h_target_fvar,
        "replacement must use a fresh fvar"
    );
    assert_eq!(h_target.ty, make_p(y.clone()));
    assert!(
        state.metas().is_assigned(initial_meta),
        "replacement should close the old goal with a let-bound proof"
    );
    let assigned = state
        .metas()
        .get_assignment(initial_meta)
        .expect("old goal should be assigned after replacement");
    assert!(
        matches!(assigned.kind(), ExprKind::Let(..)),
        "replacement proof should be a let-binding, got: {assigned:?}"
    );

    exact(&mut state, Expr::fvar(hy_fvar)).expect("hy should close the unchanged goal");
    assert!(
        state.proof_term().is_some(),
        "replacement should preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "replacement should preserve closed_proof() extraction"
    );
}

#[test]
fn test_replace_local_decl_validation_clears_temporary_tc_cache() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(
            BinderInfo::Default,
            make_p(x.clone()),
            Expr::pi(BinderInfo::Default, make_p(y.clone()), make_p(y)),
        ),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h_eq").expect("intro should create h_eq");
    intro(&mut state, "h_target").expect("intro should create h_target");
    intro(&mut state, "hy").expect("intro should create hy");

    let validation_goal =
        build_validation_goal_with_replaced_local(&mut state, "h_target", make_p(x));
    state
        .validate_rewritten_goal_for_test(&validation_goal, "h_target")
        .expect("raw validation should accept the rewritten goal");
    assert!(
        state.has_tc_cache_for_test(),
        "raw rewritten-goal validation should populate the temporary TC cache"
    );

    state.invalidate_tc_cache();
    state
        .validate_rewritten_goal_with_cache_reset_for_test(&validation_goal, "h_target")
        .expect("production validation path should accept the rewritten goal");
    assert!(
        !state.has_tc_cache_for_test(),
        "production validation path must clear caches from the temporary validation goal"
    );
}

#[test]
fn test_replace_local_decl_def_eq_rewrites_later_local_and_target() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let old_ty = Expr::app(
        Expr::lam(BinderInfo::Default, n_ty, make_p(Expr::bvar(0))),
        x.clone(),
    );
    let new_ty = make_p(x.clone());
    let goal = Expr::pi(
        BinderInfo::Default,
        old_ty.clone(),
        Expr::pi(BinderInfo::Default, new_ty.clone(), new_ty.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h_target").expect("intro should create h_target");
    intro(&mut state, "hx").expect("intro should create hx");
    let h_target_fvar = local_fvar(&state, "h_target");
    let hx_fvar = local_fvar(&state, "hx");

    state
        .replace_local_decl_def_eq(h_target_fvar, new_ty.clone())
        .expect("defeq replacement should succeed");

    let goal = state.current_goal().unwrap();
    let h_target = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h_target")
        .expect("rewritten local should exist");
    assert_ne!(
        h_target.fvar, h_target_fvar,
        "replacement must allocate a fresh fvar"
    );
    assert_eq!(h_target.ty, new_ty);
    assert_eq!(
        goal.target,
        make_p(x),
        "defeq replacement must preserve the goal target"
    );

    exact(&mut state, Expr::fvar(hx_fvar)).expect("hx should close the unchanged goal");
    assert!(
        state.proof_term().is_some(),
        "defeq replacement should preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "defeq replacement should preserve closed_proof() extraction"
    );
}

#[test]
fn test_replace_local_decl_with_cast_rejects_later_dependent_type() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let h_target_fvar = FVarId::new(0);
    let n_fvar = FVarId::new(1);
    let target = make_p(x.clone());
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                fvar: h_target_fvar,
                name: "h_target".into(),
                ty: make_p(x),
                value: None,
            },
            LocalDecl {
                fvar: n_fvar,
                name: "n".into(),
                ty: Expr::const_(Name::from_string("N"), vec![]),
                value: None,
            },
        ],
    );
    let initial_meta = state.current_goal().unwrap().meta_id;

    let result = state.replace_local_decl_with_cast(
        h_target_fvar,
        make_p(Expr::fvar(n_fvar)),
        Expr::fvar(h_target_fvar),
    );

    match result {
        Err(TacticError::InvalidTarget { tactic, detail }) => {
            assert_eq!(tactic, "replace_local_decl");
            assert!(
                detail.contains("later local 'n'"),
                "later-dependent error should mention the blocking local, got: {detail}"
            );
        }
        other => panic!("expected later-dependent invalid-target error, got: {other:?}"),
    }

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target, target,
        "goal target must remain unchanged on error"
    );
    assert_eq!(goal.local_ctx[0].fvar, h_target_fvar);
    assert_eq!(goal.local_ctx[0].name, "h_target");
    assert!(
        !state.metas().is_assigned(initial_meta),
        "later-dependent failure must not assign the old goal"
    );
}

#[test]
fn test_replace_local_decl_with_cast_rolls_back_on_bad_cast() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let h_eq_fvar = FVarId::new(0);
    let h_target_fvar = FVarId::new(1);
    let hy_fvar = FVarId::new(2);
    let target = make_p(y.clone());
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                fvar: h_eq_fvar,
                name: "h_eq".into(),
                ty: make_eq_n(x.clone(), y.clone()),
                value: None,
            },
            LocalDecl {
                fvar: h_target_fvar,
                name: "h_target".into(),
                ty: make_p(x),
                value: None,
            },
            LocalDecl {
                fvar: hy_fvar,
                name: "hy".into(),
                ty: make_p(y),
                value: None,
            },
        ],
    );
    let initial_meta = state.current_goal().unwrap().meta_id;

    let result = state.replace_local_decl_with_cast(
        h_target_fvar,
        make_p(Expr::const_(Name::from_string("y"), vec![])),
        Expr::const_(Name::from_string("x"), vec![]),
    );

    assert!(
        matches!(
            result,
            Err(TacticError::TypeCheckFailed(_)) | Err(TacticError::TypeMismatch { .. })
        ),
        "ill-typed cast must fail with a type error, got: {result:?}"
    );

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target, target,
        "goal target must remain unchanged on failure"
    );
    assert_eq!(goal.local_ctx[1].fvar, h_target_fvar);
    assert_eq!(goal.local_ctx[1].name, "h_target");
    assert_eq!(goal.local_ctx[2].fvar, hy_fvar);
    assert!(
        !state.metas().is_assigned(initial_meta),
        "failed cast must not assign the old goal metavariable"
    );
}

#[test]
fn test_replace_local_decl_with_value_shadows_without_retyping_dependencies() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let h_fvar = FVarId::new(0);
    let hx_fvar = FVarId::new(1);
    let target = make_p(Expr::fvar(h_fvar));
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: h_fvar,
                name: "h".into(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: hx_fvar,
                name: "hx".into(),
                ty: make_p(Expr::fvar(h_fvar)),
                value: None,
            },
        ],
    );

    let new_h_fvar = state
        .replace_local_decl_with_value(h_fvar, n_ty, y.clone())
        .expect("value replacement should succeed");

    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx
            .iter()
            .any(|decl| decl.fvar == h_fvar && decl.name != "h"),
        "the dependent old local must remain available under a hidden name"
    );
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("replacement should keep a visible h");
    assert_eq!(h.fvar, new_h_fvar);
    assert_eq!(h.value, Some(y));
    let hx = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "hx")
        .expect("later local should remain present");
    assert_eq!(
        hx.ty,
        make_p(Expr::fvar(h_fvar)),
        "a replacement value is not equality evidence and must not retype later locals"
    );
    assert_eq!(
        goal.target,
        make_p(Expr::fvar(h_fvar)),
        "a replacement value is not equality evidence and must not rewrite the target"
    );

    let root_meta = state.root_meta_id;
    let assigned = state
        .metas()
        .get_assignment(root_meta)
        .expect("value shadowing must close the old goal with a proof term");
    assert!(
        matches!(assigned.kind(), ExprKind::Let(..)),
        "value shadowing must use a let-bound continuation, got: {assigned:?}"
    );

    exact(&mut state, Expr::fvar(hx_fvar)).expect("unchanged later proof should close the goal");
    assert!(
        state.proof_term().is_some(),
        "value replacement should preserve proof_term() extraction"
    );
}

#[test]
fn test_replace_local_decl_type_validated_rejects_non_defeq_retyping() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let h_fvar = FVarId::new(0);
    let target = make_p(x.clone());
    let old_ty = make_p(x);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".into(),
            ty: old_ty.clone(),
            value: None,
        }],
    );
    let old_meta = state.current_goal().unwrap().meta_id;
    let old_scope = state.metas().get(old_meta).unwrap().locals.clone();

    let result = state.replace_local_decl_type_validated(h_fvar, make_p(y));
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref detail)) if detail.contains("explicit proof")),
        "non-defeq in-place retyping must fail closed, got: {result:?}"
    );

    let goal = state
        .current_goal()
        .expect("failure must preserve the goal");
    assert_eq!(goal.meta_id, old_meta);
    assert_eq!(goal.target, target);
    assert_eq!(goal.local_ctx[0].fvar, h_fvar);
    assert_eq!(goal.local_ctx[0].ty, old_ty);
    assert_eq!(state.metas().get(old_meta).unwrap().locals, old_scope);
    assert!(!state.metas().is_assigned(old_meta));
}

#[test]
fn test_replace_local_decl_with_value_keeps_old_hidden_when_new_value_depends_on_it() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let old_h_fvar = FVarId::new(0);
    let n_fvar = FVarId::new(1);
    let mut state = ProofState::with_context(
        env,
        make_p(Expr::const_(Name::from_string("x"), vec![])),
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

    let new_h_fvar = state
        .replace_local_decl_with_value(
            old_h_fvar,
            make_p(Expr::fvar(n_fvar)),
            Expr::app(Expr::fvar(old_h_fvar), Expr::fvar(n_fvar)),
        )
        .expect("value replacement should succeed");

    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx
            .iter()
            .any(|decl| decl.fvar == old_h_fvar && decl.name != "h"),
        "old local should stay hidden when the new value depends on it"
    );
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("replacement should keep the original user-facing name visible");
    assert_eq!(h.fvar, new_h_fvar);
    assert_eq!(h.ty, make_p(Expr::fvar(n_fvar)));
    assert_eq!(
        h.value,
        Some(Expr::app(Expr::fvar(old_h_fvar), Expr::fvar(n_fvar)))
    );
    let h_pos = goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == "h")
        .expect("replacement should leave a visible h");
    let n_pos = goal
        .local_ctx
        .iter()
        .position(|decl| decl.name == "n")
        .expect("dependency local should remain present");
    assert!(
        h_pos > n_pos,
        "replacement must insert after the latest dependency"
    );
}

#[test]
fn test_replace_local_decl_with_value_produces_kernel_checked_closed_let() {
    let env = setup_env_with_full_eq();
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let target = Expr::arrow(n_ty.clone(), Expr::arrow(n_ty.clone(), n_ty.clone()));
    let mut state = ProofState::new(env, target.clone());
    intro(&mut state, "h").expect("first intro should create h");
    intro(&mut state, "y").expect("second intro should create y");
    let old_h_fvar = local_fvar(&state, "h");
    let y_fvar = local_fvar(&state, "y");

    let new_h_fvar = state
        .replace_local_decl_with_value(old_h_fvar, n_ty, Expr::fvar(y_fvar))
        .expect("value replacement should create a proof-carrying let continuation");
    exact(&mut state, Expr::fvar(new_h_fvar))
        .expect("the let-bound replacement should close the continuation");

    assert!(state.is_complete());
    let closed = state
        .closed_proof()
        .expect("the replacement chain must expose a fully closed proof");
    let checker = TypeChecker::new(state.env());
    assert!(
        checker.check_type(&closed, &target).is_ok(),
        "the closed let-shadowing proof must pass the kernel type checker: {closed:?}"
    );
}

#[test]
fn test_change_at_uses_local_proof_carry_and_preserves_proof_extraction() {
    let (mut state, old_h_fvar, hy_fvar, target) = setup_change_at_proof_carry_state();

    change_at(&mut state, "h", target.clone())
        .expect("change_at should use defeq local replacement");

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain");
    assert_ne!(h.fvar, old_h_fvar, "change_at must allocate a fresh fvar");
    assert_eq!(h.ty, target, "change_at should rewrite the hypothesis type");

    exact(&mut state, Expr::fvar(hy_fvar)).expect("hy should close the unchanged goal");
    assert!(
        state.proof_term().is_some(),
        "change_at must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "change_at must preserve closed_proof() extraction"
    );
}

#[test]
fn test_unfold_at_uses_local_proof_carry_and_preserves_proof_extraction() {
    let (mut state, old_h_fvar, hy_fvar, target) = setup_unfold_at_proof_carry_state();

    unfold_at(&mut state, "mydef", "h").expect("unfold_at should use defeq local replacement");

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain");
    assert_ne!(h.fvar, old_h_fvar, "unfold_at must allocate a fresh fvar");
    assert_eq!(
        h.ty, target,
        "unfold_at should rewrite the hypothesis type to the unfolded form"
    );

    exact(&mut state, Expr::fvar(hy_fvar)).expect("hy should close the unchanged goal");
    assert!(
        state.proof_term().is_some(),
        "unfold_at must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "unfold_at must preserve closed_proof() extraction"
    );
}
