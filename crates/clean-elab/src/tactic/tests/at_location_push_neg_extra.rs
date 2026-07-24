// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::registry::TacticRegistry;

pub(super) fn add_prop_axiom(env: &mut Environment, name: &str) -> Expr {
    let expr = Expr::const_(Name::from_string(name), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    expr
}

pub(super) fn make_direct_not(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr)
}

fn unsupported_push_neg_hypothesis_state() -> (ProofState, Expr, Expr) {
    let mut env = setup_env_with_prop_ext();

    let p = add_prop_axiom(&mut env, "P");
    let q = add_prop_axiom(&mut env, "Q");
    let target = q.clone();
    let hyp_ty = Expr::arrow(make_direct_not(make_direct_not(p)), q);

    let state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty.clone(),
            value: None,
        }],
    );

    (state, target, hyp_ty)
}

pub(super) fn assert_push_neg_failure_keeps_state(
    state: &ProofState,
    target: &Expr,
    hyp_ty: &Expr,
    failure_label: &str,
) {
    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, *target,
        "{failure_label} should leave the goal target unchanged"
    );
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("the original hypothesis should remain visible after failure");
    assert_eq!(
        h.ty, *hyp_ty,
        "{failure_label} should leave the hypothesis unchanged"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{failure_label} must not record trusted fallback"
    );
}

#[test]
fn test_push_neg_at_rewrites_inside_mdata_wrapper() {
    let mut env = setup_env_with_prop_ext();

    let p = add_prop_axiom(&mut env, "A");
    let target = p.clone();
    let wrapped_hyp_ty = Expr::mdata(vec![], make_not(&make_not(&p)));

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: wrapped_hyp_ty,
            value: None,
        }],
    );

    push_neg_at(&mut state, "h").expect("push_neg_at should rewrite inside mdata wrappers");

    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target, target,
        "push_neg_at should leave the goal target unchanged"
    );
    let h = goal
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("rewritten hypothesis should remain visible");
    assert_eq!(
        h.ty,
        Expr::mdata(vec![], p.clone()),
        "push_neg_at should preserve metadata wrappers around the rewritten hypothesis"
    );
    let h_fvar = h.fvar;
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "push_neg_at should stay on the proof-carry path inside mdata wrappers"
    );

    exact(&mut state, Expr::fvar(h_fvar))
        .expect("the rewritten metadata-wrapped hypothesis should close the original goal");
    assert!(
        state.is_complete(),
        "exact should close the goal after the wrapped push_neg rewrite"
    );
}

#[test]
fn test_push_neg_at_fails_closed_on_unsupported_implication_domain_rewrite() {
    let (mut state, target, hyp_ty) = unsupported_push_neg_hypothesis_state();

    let result = push_neg_at(&mut state, "h");
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref message)) if message.contains("legacy push_neg would rewrite it")),
        "push_neg_at should fail closed when the proof-carry path misses a legacy rewrite: {result:?}"
    );
    assert_push_neg_failure_keeps_state(&state, &target, &hyp_ty, "failed push_neg_at");
}

#[test]
fn test_push_neg_wildcard_dispatch_propagates_fail_closed_hypothesis_error() {
    let mut env = setup_env_with_prop_ext();

    let p = add_prop_axiom(&mut env, "P");
    let q = add_prop_axiom(&mut env, "Q");
    let target = make_not(&make_not(&p));
    let hyp_ty = Expr::arrow(make_direct_not(make_direct_not(p.clone())), q);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty.clone(),
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let push_neg = registry
        .get("push_neg")
        .expect("push_neg should be registered in the production registry");

    let result = (push_neg.handler)(&mut state, &[Expr::const_(Name::from_string("*"), vec![])]);
    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref message)) if message.contains("legacy push_neg would rewrite it")),
        "push_neg at * should propagate the fail-closed local rewrite error: {result:?}"
    );
    assert_push_neg_failure_keeps_state(&state, &target, &hyp_ty, "failed wildcard push_neg");
}

#[test]
fn test_push_neg_wildcard_dispatch_propagates_environment_error() {
    let mut env = Environment::new();
    env.init_true_false()
        .expect("test environment should provide False for negation encoding");

    let p = add_prop_axiom(&mut env, "P");
    let q = add_prop_axiom(&mut env, "Q");
    let target = q.clone();
    let hyp_ty = make_not(&make_not(&p));

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty.clone(),
            value: None,
        }],
    );

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let push_neg = registry
        .get("push_neg")
        .expect("push_neg should be registered in the production registry");

    let result = (push_neg.handler)(&mut state, &[Expr::const_(Name::from_string("*"), vec![])]);
    assert!(
        matches!(
            result,
            Err(TacticError::EnvironmentMissing { ref constant })
                if constant == "Classical.byContradiction"
        ),
        "push_neg at * should propagate proof-builder environment errors instead of masking them as no progress: {result:?}"
    );
    assert_push_neg_failure_keeps_state(&state, &target, &hyp_ty, "failed wildcard push_neg");
}
