// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::{conv_ext, conv_rw, convert_hyp, LocalDecl};
use clean_kernel::{BinderInfo, Environment, FVarId, Name};
use clean_parser::parse_name;

fn name(source: &str) -> SurfaceName {
    parse_name(source).unwrap()
}

fn local(index: u64, name: SurfaceName, ty: Expr) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(index),
        name,
        ty,
        value: None,
    }
}

fn lift_state() -> ProofState {
    ProofState::with_context(
        Environment::new(),
        Expr::prop(),
        vec![
            local(0, name("«A.B»"), Expr::prop()),
            local(1, name("«_»"), Expr::prop()),
            local(2, SurfaceName::from_name(Name::anon().num(7)), Expr::prop()),
        ],
    )
}

#[test]
fn lift_resolves_exact_names_but_still_refuses_unimplemented_proof_transport() {
    let mut state = lift_state();
    let before = state.current_goal().unwrap().clone();
    let next_fvar = state.next_fvar;
    assert!(
        matches!(lift(&mut state, &name("«A.B»"), Some(&name("«_»"))),
        Err(TacticError::InvalidTarget { tactic, .. }) if tactic == "lift")
    );
    for query in [
        name("A.B"),
        name("«7»"),
        name("«A.B»").with_relative_constructor(),
        SurfaceName::default(),
    ] {
        assert!(matches!(
            lift(&mut state, &query, None),
            Err(TacticError::HypothesisNotFound(_))
        ));
    }
    assert!(matches!(
        lift(&mut state, &name("«A.B»"), Some(&name("missing"))),
        Err(TacticError::HypothesisNotFound(_))
    ));
    let after = state.current_goal().unwrap();
    assert_eq!(after.meta_id, before.meta_id);
    assert_eq!(after.target, before.target);
    assert_eq!(after.local_ctx.len(), before.local_ctx.len());
    assert_eq!(state.next_fvar, next_fvar);
    assert_eq!(state.trusted_axiom_count(), 0);
}

#[test]
fn lift_configuration_preserves_escaped_binder_syntax() {
    let config = LiftConfig::new()
        .with_name(&name("«A.B»"))
        .with_proof(&name("«_»"));
    assert!(config
        .new_name
        .as_ref()
        .unwrap()
        .same_syntax(&name("«A.B»")));
    assert!(config
        .proof_name
        .as_ref()
        .unwrap()
        .same_syntax(&name("«_»")));
    let mut state = lift_state();
    let invalid = LiftConfig::new().with_name(&name("x").with_relative_constructor());
    assert!(matches!(
        lift_with_config(&mut state, &name("«A.B»"), None, invalid),
        Err(TacticError::InvalidTarget { .. })
    ));
}

#[test]
fn convert_uses_latest_exact_local_not_a_display_twin() {
    let locals = vec![
        local(
            0,
            name("«A.B»"),
            Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
        ),
        local(1, name("A.B"), Expr::prop()),
        local(2, name("«A.B»"), Expr::prop()),
    ];
    let mut state = ProofState::with_context(Environment::new(), Expr::prop(), locals);
    let goal_id = state.current_goal().unwrap().meta_id;
    convert_hyp(&mut state, &name("«A.B»")).unwrap();
    assert!(state.goals.is_empty());
    assert_eq!(
        state
            .metas
            .instantiate(&Expr::fvar(crate::unify::MetaState::to_fvar(goal_id))),
        Expr::fvar(FVarId::new(2))
    );
    assert_eq!(state.trusted_axiom_count(), 0);
}

#[test]
fn named_conversion_and_rewrite_refuse_relative_and_display_twin_queries() {
    for query in [
        name("A.B"),
        name("«A.B»").with_relative_constructor(),
        SurfaceName::default(),
    ] {
        let mut state = ProofState::with_context(
            Environment::new(),
            Expr::prop(),
            vec![local(0, name("«A.B»"), Expr::prop())],
        );
        let before = state.current_goal().unwrap().meta_id;
        assert!(matches!(
            convert_hyp(&mut state, &query),
            Err(TacticError::HypothesisNotFound(_))
        ));
        assert!(matches!(
            conv_rw(&mut state, vec![], &query, false),
            Err(TacticError::HypothesisNotFound(_))
        ));
        assert_eq!(state.current_goal().unwrap().meta_id, before);
        assert_eq!(state.current_goal().unwrap().target, Expr::prop());
    }
}

#[test]
fn conv_binder_keeps_lexical_name_and_existing_case_ownership() {
    let mut state = ProofState::with_context(
        Environment::new(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        vec![local(0, name("older"), Expr::prop())],
    );
    state.current_goal_mut().unwrap().case_binders = vec![FVarId::new(0)];
    state.current_goal_mut().unwrap().tag = Some(name("«C.dot»"));
    let before = state.current_goal().unwrap().clone();
    conv_ext(&mut state, &name("«_»")).unwrap();
    let after = state.current_goal().unwrap();
    let introduced = after.local_ctx.last().unwrap();
    assert!(introduced.name.same_syntax(&name("«_»")));
    assert_ne!(after.meta_id, before.meta_id);
    assert_eq!(after.target, Expr::fvar(introduced.fvar));
    assert_eq!(after.case_binders, before.case_binders);
    assert_eq!(after.tag, before.tag);
    assert!(!after.case_binders.contains(&introduced.fvar));
}

#[test]
fn conv_binder_invalid_identity_refuses_before_state_mutation() {
    for invalid in [
        SurfaceName::default(),
        name("x").with_relative_constructor(),
    ] {
        let mut state = ProofState::new(
            Environment::new(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        );
        let before = state.current_goal().unwrap().clone();
        let next_fvar = state.next_fvar;
        assert!(conv_ext(&mut state, &invalid).is_err());
        assert_eq!(state.current_goal().unwrap().meta_id, before.meta_id);
        assert_eq!(state.current_goal().unwrap().target, before.target);
        assert_eq!(state.next_fvar, next_fvar);
    }
}
