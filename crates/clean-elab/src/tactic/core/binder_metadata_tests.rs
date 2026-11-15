// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderData, BinderInfo, ExprKind, Name, TypeChecker};
use clean_parser::SurfaceName;

#[test]
fn intro_and_revert_retain_every_binder_annotation() {
    for certified in [false, true] {
        for info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            let data = BinderData::from(info);
            let mut state = ProofState::new(
                Environment::with_prelude(),
                Expr::pi(
                    data,
                    Expr::const_(Name::from_string("Nat"), vec![]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
            );
            let name = SurfaceName::from_name(Name::from_string("n"));
            if certified {
                let _certificate =
                    crate::tactic::proof_term_cert::intro_with_cert(&mut state, &name)
                        .expect("certified intro");
            } else {
                crate::tactic::proof_term::intro(&mut state, &name).expect("intro");
            }
            assert_eq!(
                state
                    .current_goal()
                    .unwrap()
                    .local_ctx
                    .last()
                    .unwrap()
                    .binder_info,
                data
            );
            crate::tactic::congr_obtain::revert(&mut state, &name).expect("revert");
            assert!(
                matches!(state.current_goal().unwrap().target.kind(), ExprKind::Pi(actual, _, _) if *actual == data)
            );
        }
    }
}

#[test]
fn sibling_goals_with_reused_ids_keep_distinct_binder_annotations() {
    let name = SurfaceName::from_name(Name::from_string("n"));
    let local = LocalDecl {
        binder_info: BinderInfo::Implicit.into(),
        fvar: FVarId::new(0),
        name: name.clone(),
        ty: Expr::const_(Name::from_string("Nat"), vec![]),
        value: None,
    };
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        Expr::const_(Name::from_string("Nat"), vec![]),
        vec![local],
    );
    let mut sibling = state.current_goal().unwrap().clone();
    sibling.local_ctx[0].binder_info = BinderInfo::Default.into();
    sibling.meta_id = state.fresh_meta_in_context(sibling.target.clone(), &sibling.local_ctx);
    state.goals.push_back(sibling);
    crate::tactic::major_dependents::revert_fvars(&mut state, &[FVarId::new(0)])
        .expect("first revert");
    assert!(
        matches!(state.current_goal().unwrap().target.kind(), ExprKind::Pi(data, _, _) if data.info == BinderInfo::Implicit)
    );
    state.goals.pop_front();
    crate::tactic::major_dependents::revert_fvars(&mut state, &[FVarId::new(0)])
        .expect("sibling revert");
    assert!(
        matches!(state.current_goal().unwrap().target.kind(), ExprKind::Pi(data, _, _) if data.info == BinderInfo::Default)
    );
}

#[test]
fn annotated_binder_and_dependent_let_survive_revert_and_checked_reintroduction() {
    for info in [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        let env = Environment::with_prelude();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let target = Expr::pi(
            BinderData::from(info),
            nat.clone(),
            Expr::let_named(
                Name::from_string("n"),
                nat.clone(),
                Expr::bvar(0),
                nat,
                false,
            ),
        );
        let mut state = ProofState::new(env.clone(), target.clone());
        let x = SurfaceName::from_name(Name::from_string("x"));
        let n = SurfaceName::from_name(Name::from_string("n"));
        crate::tactic::proof_term::intro(&mut state, &x).expect("annotated binder");
        crate::tactic::proof_term::intro(&mut state, &n).expect("dependent let");
        crate::tactic::congr_obtain::revert(&mut state, &x).expect("dependency closure");
        let goal = state.current_goal().expect("reverted goal");
        assert!(goal.local_ctx.is_empty());
        let ExprKind::Pi(data, _, body) = goal.target.kind() else {
            panic!("the annotated hypothesis must remain a Pi")
        };
        assert_eq!(data.info, info);
        assert!(matches!(body.kind(), ExprKind::Let(..)));
        crate::tactic::proof_term::intro(&mut state, &x).expect("reintroduce binder");
        crate::tactic::proof_term::intro(&mut state, &n).expect("reintroduce let");
        let goal = state.current_goal().expect("reintroduced goal");
        assert_eq!(goal.local_ctx[0].binder_info.info, info);
        assert_eq!(
            goal.local_ctx[1].value.as_ref(),
            Some(&Expr::fvar(goal.local_ctx[0].fvar))
        );
        let value = Expr::fvar(goal.local_ctx[1].fvar);
        crate::tactic::proof_term::exact(&mut state, value).expect("use defined local");
        let proof = state.closed_proof().expect("closed proof");
        TypeChecker::new(&env)
            .check_type(&proof, &target)
            .expect("independent kernel check");
    }
}
