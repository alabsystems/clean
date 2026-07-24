// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{env::Declaration, Level};

fn add_apply_fun_supporting_decls(env: &mut Environment) {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(n_ty.clone(), n_ty),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Witness"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
        ),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("mkWitness"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Witness"), vec![]),
                        Expr::bvar(1),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();
}

fn mk_eq_at_level(level: Level, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![level]), ty),
            lhs,
        ),
        rhs,
    )
}

fn add_function_injective_definition(env: &mut Environment) {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let sort_u = Expr::sort(u_level.clone());
    let sort_v = Expr::sort(v_level.clone());
    let alpha_id = FVarId::new(10_000);
    let beta_id = FVarId::new(10_001);
    let func_id = FVarId::new(10_002);
    let a1_id = FVarId::new(10_003);
    let a2_id = FVarId::new(10_004);
    let alpha = Expr::fvar(alpha_id);
    let beta = Expr::fvar(beta_id);
    let func = Expr::fvar(func_id);
    let a1 = Expr::fvar(a1_id);
    let a2 = Expr::fvar(a2_id);

    let type_with_func = Expr::pi(
        BinderInfo::Default,
        Expr::arrow(alpha.clone(), beta.clone()),
        Expr::prop(),
    );
    let type_with_beta = Expr::pi(
        BinderInfo::Implicit,
        sort_v.clone(),
        type_with_func.abstract_fvar(beta_id),
    );
    let type_ = Expr::pi(
        BinderInfo::Implicit,
        sort_u.clone(),
        type_with_beta.abstract_fvar(alpha_id),
    );

    let fa1_eq_fa2 = mk_eq_at_level(
        v_level.clone(),
        beta.clone(),
        Expr::app(func.clone(), a1.clone()),
        Expr::app(func.clone(), a2.clone()),
    );
    let a1_eq_a2 = mk_eq_at_level(u_level, alpha.clone(), a1.clone(), a2.clone());
    let body_with_h = Expr::pi(BinderInfo::Default, fa1_eq_fa2, a1_eq_a2);
    let body_with_a2 = Expr::pi(
        BinderInfo::StrictImplicit,
        alpha.clone(),
        body_with_h.abstract_fvar(a2_id),
    );
    let body_with_a1 = Expr::pi(
        BinderInfo::StrictImplicit,
        alpha.clone(),
        body_with_a2.abstract_fvar(a1_id),
    );
    let body_with_func = Expr::lam(
        BinderInfo::Default,
        Expr::arrow(alpha.clone(), beta.clone()),
        body_with_a1.abstract_fvar(func_id),
    );
    let body_with_beta = Expr::lam(
        BinderInfo::Implicit,
        sort_v,
        body_with_func.abstract_fvar(beta_id),
    );
    let value = Expr::lam(
        BinderInfo::Implicit,
        sort_u,
        body_with_beta.abstract_fvar(alpha_id),
    );

    env.add_decl(Declaration::Definition {
        name: Name::from_string("Function.Injective"),
        level_params: vec![u, v],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap();
}

fn setup_apply_fun_hypothesis_state() -> (ProofState, crate::unify::MetaId, FVarId, Expr, Expr, Expr)
{
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let state = ProofState::with_context(
        env,
        make_p(x.clone()),
        vec![LocalDecl {
            fvar: hyp_fvar,
            name: "h".to_string(),
            ty: make_eq_n(x.clone(), y.clone()),
            value: None,
        }],
    );
    let meta_id = state.current_goal().unwrap().meta_id;
    let func = Expr::const_(Name::from_string("g"), vec![]);
    (state, meta_id, hyp_fvar, func, x, y)
}

fn witness_of(alpha: Expr, value: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Witness"), vec![]), alpha),
        value,
    )
}

fn mk_witness(alpha: Expr, value: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("mkWitness"), vec![]), alpha),
        value,
    )
}

fn setup_apply_fun_dependent_target_state() -> (ProofState, crate::unify::MetaId, FVarId, Expr) {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let hyp_ty = make_eq_n(x, y);
    let target = witness_of(hyp_ty.clone(), Expr::fvar(hyp_fvar));
    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: hyp_fvar,
            name: "h".to_string(),
            ty: hyp_ty,
            value: None,
        }],
    );
    let meta_id = state.current_goal().unwrap().meta_id;
    let func = Expr::const_(Name::from_string("g"), vec![]);
    (state, meta_id, hyp_fvar, func)
}

fn setup_apply_fun_dependent_let_binding_state() -> (ProofState, crate::unify::MetaId, Expr) {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let dependent_fvar = FVarId::new(1);
    let hyp_ty = make_eq_n(x.clone(), y.clone());
    let state = ProofState::with_context(
        env,
        make_p(x),
        vec![
            LocalDecl {
                fvar: hyp_fvar,
                name: "h".to_string(),
                ty: hyp_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: dependent_fvar,
                name: "k".to_string(),
                ty: witness_of(hyp_ty.clone(), Expr::fvar(hyp_fvar)),
                value: Some(mk_witness(hyp_ty, Expr::fvar(hyp_fvar))),
            },
        ],
    );
    let meta_id = state.current_goal().unwrap().meta_id;
    let func = Expr::const_(Name::from_string("g"), vec![]);
    (state, meta_id, func)
}

fn mk_apply_fun_goal_injective(func: Expr) -> Expr {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let a1 = Expr::bvar(1);
    let a2 = Expr::bvar(0);
    let ga1_eq_ga2 = make_eq_n(
        Expr::app(func.clone(), a1.clone()),
        Expr::app(func, a2.clone()),
    );
    let a1_eq_a2 = make_eq_n(a1, a2);

    Expr::pi(
        BinderInfo::StrictImplicit,
        n_ty.clone(),
        Expr::pi(
            BinderInfo::StrictImplicit,
            n_ty,
            Expr::pi(BinderInfo::Default, ga1_eq_ga2, a1_eq_a2.lift(1)),
        ),
    )
}

fn mk_apply_fun_goal_named_injective(func: Expr) -> Expr {
    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let type_level = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Function.Injective"),
                    vec![type_level.clone(), type_level],
                ),
                n_ty.clone(),
            ),
            n_ty,
        ),
        func,
    )
}

fn setup_apply_fun_goal_state() -> (ProofState, crate::unify::MetaId, Expr, Expr, Expr) {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = ProofState::new(env, make_eq_n(x.clone(), y.clone()));
    let meta_id = state.current_goal().unwrap().meta_id;
    let func = Expr::const_(Name::from_string("g"), vec![]);
    (state, meta_id, func, x, y)
}

fn setup_apply_fun_goal_state_with_function_injective(
) -> (ProofState, crate::unify::MetaId, Expr, Expr, Expr) {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);
    add_function_injective_definition(&mut env);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let state = ProofState::new(env, make_eq_n(x.clone(), y.clone()));
    let meta_id = state.current_goal().unwrap().meta_id;
    let func = Expr::const_(Name::from_string("g"), vec![]);
    (state, meta_id, func, x, y)
}

fn setup_apply_fun_goal_closure_state(
    include_injective: bool,
) -> (ProofState, Expr, Expr, Option<Expr>) {
    let mut env = setup_env_with_full_eq();
    add_apply_fun_supporting_decls(&mut env);

    let func = Expr::const_(Name::from_string("g"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let transformed_eq = make_eq_n(
        Expr::app(func.clone(), x.clone()),
        Expr::app(func.clone(), y.clone()),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hfg"),
        level_params: vec![],
        type_: transformed_eq,
    })
    .unwrap();

    let hinj_expr = include_injective.then(|| Expr::const_(Name::from_string("hinj"), vec![]));
    if include_injective {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("hinj"),
            level_params: vec![],
            type_: mk_apply_fun_goal_injective(func.clone()),
        })
        .unwrap();
    }

    let state = ProofState::new(env, make_eq_n(x, y));
    (
        state,
        func,
        Expr::const_(Name::from_string("hfg"), vec![]),
        hinj_expr,
    )
}

#[test]
fn test_apply_fun_hypothesis_builds_congr_arg_let_binding() {
    let (mut state, initial_meta_id, _old_fvar, func, x, y) = setup_apply_fun_hypothesis_state();
    let original_target = state.current_goal().unwrap().target.clone();

    let result = apply_fun(&mut state, func.clone(), "h");
    assert!(result.is_ok(), "apply_fun should succeed: {result:?}");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "proof-carrying apply_fun must not record trusted fallback usage"
    );
    assert!(
        state.metas().is_assigned(initial_meta_id),
        "apply_fun must close the old goal with a proof term"
    );

    let proof = state.metas().get_assignment(initial_meta_id).unwrap();
    if let ExprKind::Let(_name, ty, val, _body, _) = proof.kind() {
        assert_eq!(
            ty.as_ref().clone(),
            make_eq_n(Expr::app(func.clone(), x), Expr::app(func.clone(), y)),
            "let-bound replacement hypothesis should have the transformed equality type"
        );
        let val_head = val.get_app_fn();
        match val_head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name,
                &Name::from_string("congrArg"),
                "apply_fun should justify the new hypothesis via congrArg"
            ),
            _ => panic!(
                "apply_fun proof should use congrArg, got: {:?}",
                val_head.kind()
            ),
        }
    } else {
        panic!("apply_fun should close the old goal with a let-binding");
    }

    assert_eq!(
        state.current_goal().unwrap().target,
        original_target,
        "non-dependent goal target should stay unchanged after apply_fun at hypothesis"
    );
}

#[test]
fn test_apply_fun_hypothesis_replaces_local_with_fresh_fvar() {
    let (mut state, _initial_meta_id, old_fvar, func, x, y) = setup_apply_fun_hypothesis_state();

    apply_fun(&mut state, func.clone(), "h").unwrap();

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("replacement hypothesis should remain in the local context");
    assert_ne!(h.fvar, old_fvar, "apply_fun must allocate a fresh fvar");
    assert_eq!(
        h.ty,
        make_eq_n(Expr::app(func.clone(), x), Expr::app(func, y)),
        "replacement hypothesis should expose the transformed equality type"
    );
    assert!(
        goal.local_ctx
            .iter()
            .all(|decl| decl.name != "h" || decl.fvar != old_fvar),
        "old hypothesis fvar must not remain in the rewritten goal"
    );
    assert!(
        !state.is_complete(),
        "apply_fun should leave the rewritten goal open for further proof steps"
    );
}

#[test]
fn test_apply_fun_hypothesis_rejects_ill_typed_dependent_target() {
    // Wave 98 — Gap 17 CLOSED. `validate_rewritten_goal` now runs a
    // strict kernel `check_type` on the rewritten target so dependent
    // Apps whose argument no longer matches the function's domain
    // (e.g. `Witness {x=y} h_g` with `h_g : g x = g y`) fail-closed.
    let (mut state, initial_meta_id, old_fvar, func) = setup_apply_fun_dependent_target_state();
    let original_goal = state.current_goal().unwrap().clone();

    let result = apply_fun(&mut state, func, "h");
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(_))),
        "apply_fun must fail-closed with TypeCheckFailed on ill-typed dependent target: {result:?}"
    );
    assert!(
        !state.metas().is_assigned(initial_meta_id),
        "failing closed must not assign the old goal metavariable"
    );

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target, original_goal.target,
        "target should remain unchanged"
    );
    assert_eq!(
        goal.local_ctx[0].fvar, old_fvar,
        "rejecting the rewrite must keep the original hypothesis fvar"
    );
    assert_eq!(
        goal.local_ctx[0].ty, original_goal.local_ctx[0].ty,
        "rejecting the rewrite must keep the original hypothesis type"
    );
    assert!(
        !state.has_tc_cache_for_test(),
        "rejected apply_fun rewrites must clear the per-goal type-checker cache"
    );
}

#[test]
fn test_apply_fun_hypothesis_strict_check_does_not_reject_non_dependent_rewrite() {
    // Wave 98 — Gap 17 negative test. The strict kernel check added
    // to `validate_rewritten_goal` must NOT reject sound rewrites:
    // when the goal target and downstream locals do not depend on
    // the hypothesis being rewritten, `apply_fun` must still close.
    // This proves the new path is conservative (no false rejects).
    let (mut state, _initial_meta_id, old_fvar, func, _x, _y) = setup_apply_fun_hypothesis_state();
    let result = apply_fun(&mut state, func, "h");
    assert!(
        result.is_ok(),
        "apply_fun on non-dependent target must still succeed: {result:?}"
    );
    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("replacement hypothesis should remain");
    assert_ne!(h.fvar, old_fvar, "apply_fun must allocate a fresh fvar");
}

#[test]
fn test_apply_fun_hypothesis_rejects_dependent_let_binding_value() {
    // Wave 98 — Gap 17 CLOSED. Strict-checking each local's value
    // catches the case where a downstream `Witness (x=y) h_g` value
    // still references the post-rewrite hypothesis but expects the
    // pre-rewrite type.
    let (mut state, initial_meta_id, func) = setup_apply_fun_dependent_let_binding_state();
    let original_goal = state.current_goal().unwrap().clone();

    let result = apply_fun(&mut state, func, "h");
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(_))),
        "apply_fun must reject dependent let-binding rewrite: {result:?}"
    );
    assert!(
        !state.metas().is_assigned(initial_meta_id),
        "rejecting the rewrite must not close the original goal"
    );

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target, original_goal.target,
        "target should remain unchanged"
    );
    assert_eq!(
        goal.local_ctx[1].ty, original_goal.local_ctx[1].ty,
        "downstream dependent local type should remain unchanged on error"
    );
    assert_eq!(
        goal.local_ctx[1]
            .value
            .as_ref()
            .expect("original local should remain a let-binding"),
        original_goal.local_ctx[1]
            .value
            .as_ref()
            .expect("original local should remain a let-binding"),
        "downstream dependent local value should remain unchanged on error"
    );
}

#[test]
fn test_apply_fun_goal_equality_creates_injective_side_goal() {
    let (mut state, initial_meta_id, func, x, y) = setup_apply_fun_goal_state();

    let result = apply_fun_goal(&mut state, func.clone());
    assert!(
        result.is_ok(),
        "apply_fun_goal should split an equality goal without trusted fallback: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "apply_fun_goal should not record trusted fallback usage on equality goals"
    );
    assert!(
        state.metas().is_assigned(initial_meta_id),
        "apply_fun_goal should close the original goal through the new proof chain"
    );
    assert_eq!(
        state.goals().len(),
        2,
        "apply_fun_goal should produce two goals"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(
            Expr::app(func.clone(), x.clone()),
            Expr::app(func.clone(), y.clone())
        ),
        "the transformed equality goal should stay at the front"
    );
    assert_eq!(
        state.goals().get(1).unwrap().target,
        mk_apply_fun_goal_injective(func),
        "the second goal should be the injectivity side condition"
    );
    assert!(
        state.proof_term().is_none(),
        "proof_term() should stay unavailable until both new goals are solved"
    );
}

#[test]
fn test_apply_fun_goal_prefers_function_injective_when_available() {
    let (mut state, initial_meta_id, func, x, y) =
        setup_apply_fun_goal_state_with_function_injective();

    let result = apply_fun_goal(&mut state, func.clone());
    assert!(
        result.is_ok(),
        "apply_fun_goal should use Function.Injective when the reducible definition exists: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "Function.Injective support must not reintroduce trusted fallback"
    );
    assert!(
        state.metas().is_assigned(initial_meta_id),
        "the original goal should still close through the injectivity proof chain"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        make_eq_n(
            Expr::app(func.clone(), x.clone()),
            Expr::app(func.clone(), y.clone())
        ),
        "the transformed equality goal should remain first"
    );
    assert_eq!(
        state.goals().get(1).unwrap().target,
        mk_apply_fun_goal_named_injective(func),
        "the side goal should prefer the named Function.Injective proposition"
    );
}

#[test]
fn test_apply_fun_goal_hfg_alone_does_not_finish_original_goal() {
    let (mut state, func, hfg, _) = setup_apply_fun_goal_closure_state(false);

    apply_fun_goal(&mut state, func.clone()).expect("apply_fun_goal should succeed");
    exact(&mut state, hfg).expect("hfg should solve the transformed equality");

    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "solving the transformed equality should not introduce trusted fallback usage"
    );
    assert!(
        !state.is_complete(),
        "f a = f b alone must not finish the original goal"
    );
    assert_eq!(
        state.goals().len(),
        1,
        "only the injectivity goal should remain"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        mk_apply_fun_goal_injective(func),
        "the remaining goal should be injectivity"
    );
    assert!(
        state.proof_term().is_none(),
        "proof_term() should remain unavailable while injectivity is open"
    );
}

#[test]
fn test_apply_fun_goal_finishes_with_explicit_injective_proof() {
    let (mut state, func, hfg, hinj) = setup_apply_fun_goal_closure_state(true);

    apply_fun_goal(&mut state, func).expect("apply_fun_goal should succeed");
    exact(&mut state, hfg).expect("hfg should solve the transformed equality");
    exact(&mut state, hinj.unwrap()).expect("hinj should solve the injectivity side goal");

    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "explicit injectivity should keep apply_fun_goal on the proof-carrying path"
    );
    assert!(
        state.is_complete(),
        "both goals solved should finish the proof state"
    );
    assert!(
        state.proof_term().is_some(),
        "proof_term() should remain connected after the injectivity split"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() should remain available after both goals are closed"
    );
}
