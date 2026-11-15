// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderData, BinderInfo, ExprKind, Level, MDataValue, Name, TypeChecker};
use clean_parser::SurfaceName;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn eq_nat(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}

fn refl_nat(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), value],
    )
}

fn wrapped(expr: Expr) -> Expr {
    Expr::mdata(
        vec![(Name::from_string("outerProbe"), MDataValue::Nat(17))],
        Expr::mdata(
            vec![(Name::from_string("innerProbe"), MDataValue::Nat(23))],
            expr,
        ),
    )
}

fn intro(state: &mut ProofState, name: &str) {
    crate::tactic::proof_term::intro(state, &SurfaceName::from_name(Name::from_string(name)))
        .expect("introduce actual binder");
}

fn check_closed(state: &ProofState, env: &Environment, target: &Expr) -> Expr {
    assert!(state.goals.is_empty());
    let proof = state.closed_proof().expect("closed proof");
    assert!(!proof.has_fvar_quick());
    assert!(!proof.has_loose_bvars());
    TypeChecker::new(env)
        .check_type(&proof, target)
        .expect("independent full kernel check");
    proof
}

fn genuine_let_control(with_metadata: bool) {
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        let env = Environment::with_prelude();
        let data = BinderData::from(info);
        let inner = Expr::let_named(
            Name::from_string("alias"),
            nat(),
            Expr::bvar(0),
            eq_nat(Expr::bvar(0), Expr::bvar(1)),
            false,
        );
        let target = Expr::pi(
            data,
            nat(),
            if with_metadata { wrapped(inner) } else { inner },
        );
        let mut state = ProofState::new(env.clone(), target.clone());
        intro(&mut state, "outer");
        let before = state.current_goal().expect("let goal").clone();
        assert_eq!(
            matches!(before.target.kind(), ExprKind::MData(..)),
            with_metadata
        );
        assert!(matches!(
            before.target.strip_mdata().kind(),
            ExprKind::Let(_, _, _, _, false)
        ));
        intro(&mut state, "alias");
        let goal = state.current_goal().expect("introduced alias");
        assert_eq!(goal.local_ctx.len(), 2);
        let outer = &goal.local_ctx[0];
        let alias = &goal.local_ctx[1];
        assert_eq!(outer.binder_info, data);
        assert_eq!(outer.value, None);
        assert_eq!(alias.binder_info, BinderData::default());
        assert_eq!(alias.value, Some(Expr::fvar(outer.fvar)));
        assert!(!alias.is_have());
        assert_eq!(
            state.whnf(goal, &Expr::fvar(alias.fvar)),
            Expr::fvar(outer.fvar)
        );
        assert_eq!(
            state.metas.get(before.meta_id).expect("original meta").ty,
            before.target
        );
        // The target has alias = outer; this proof needs the genuine local value.
        let proof = refl_nat(Expr::fvar(alias.fvar));
        crate::tactic::proof_term::exact(&mut state, proof).expect("use local definition");
        let proof = check_closed(&state, &env, &target);
        let ExprKind::Lam(actual, _, body) = proof.strip_mdata().kind() else {
            panic!("closed outer binder must remain a lambda")
        };
        assert_eq!(*actual, data);
        assert!(matches!(
            body.strip_mdata().kind(),
            ExprKind::Let(_, _, _, _, false)
        ));
    }
}

#[test]
fn intro_preserves_mdata_wrapped_genuine_let_value_and_scope() {
    genuine_let_control(true);
}

#[test]
fn intro_preserves_unwrapped_genuine_let_control() {
    genuine_let_control(false);
}

#[test]
fn intro_preserves_mdata_wrapped_pi_binder_annotations() {
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        let env = Environment::with_prelude();
        let data = BinderData::from(info);
        let target = Expr::pi(
            data,
            nat(),
            wrapped(Expr::pi(data, nat(), eq_nat(Expr::bvar(0), Expr::bvar(0)))),
        );
        let mut state = ProofState::new(env.clone(), target.clone());
        intro(&mut state, "outer");
        intro(&mut state, "introduced");
        let goal = state.current_goal().expect("Pi body");
        assert_eq!(goal.local_ctx.len(), 2);
        for decl in &goal.local_ctx {
            assert_eq!(decl.binder_info, data);
            assert!(decl.value.is_none());
        }
        let proof = refl_nat(Expr::fvar(goal.local_ctx[1].fvar));
        crate::tactic::proof_term::exact(&mut state, proof).expect("reflexive equality");
        let proof = check_closed(&state, &env, &target);
        let ExprKind::Lam(outer, _, body) = proof.strip_mdata().kind() else {
            panic!("closed outer binder")
        };
        assert_eq!(*outer, data);
        assert!(matches!(body.strip_mdata().kind(), ExprKind::Lam(inner, _, _) if *inner == data));
    }
}

#[test]
fn metadata_does_not_make_nonbinder_intro_succeed() {
    let env = Environment::with_prelude();
    let target = Expr::pi(
        BinderInfo::Implicit,
        nat(),
        wrapped(eq_nat(Expr::bvar(0), Expr::bvar(0))),
    );
    let mut state = ProofState::new(env.clone(), target.clone());
    intro(&mut state, "outer");
    let before = state.current_goal().expect("nonbinder goal").clone();
    let next_fvar = state.next_fvar;
    let generation = state.metas.generation();
    let error = crate::tactic::proof_term::intro(
        &mut state,
        &SurfaceName::from_name(Name::from_string("bad")),
    )
    .expect_err("outer metadata must not manufacture a binder");
    assert!(matches!(error, TacticError::GoalMismatch(_)));
    let after = state.current_goal().expect("same nonbinder goal");
    assert_eq!(state.goals.len(), 1);
    assert_eq!(after.meta_id, before.meta_id);
    assert_eq!(after.target, before.target);
    assert_eq!(after.local_ctx.len(), 1);
    assert_eq!(after.local_ctx[0].fvar, before.local_ctx[0].fvar);
    assert_eq!(
        after.local_ctx[0].binder_info,
        before.local_ctx[0].binder_info
    );
    assert_eq!(state.next_fvar, next_fvar);
    assert_eq!(state.metas.generation(), generation);
    assert!(state
        .metas
        .get(before.meta_id)
        .expect("unassigned goal")
        .assignment
        .is_none());
    let proof = refl_nat(Expr::fvar(after.local_ctx[0].fvar));
    crate::tactic::proof_term::exact(&mut state, proof).expect("refusal leaves goal usable");
    let proof = check_closed(&state, &env, &target);
    assert!(matches!(
        proof.strip_mdata().kind(),
        ExprKind::Lam(data, _, _) if *data == BinderData::from(BinderInfo::Implicit)
    ));
}
