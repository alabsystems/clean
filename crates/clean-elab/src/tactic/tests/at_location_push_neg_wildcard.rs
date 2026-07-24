// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::push_neg_extra::{add_prop_axiom, make_direct_not};
use super::*;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::registry::TacticRegistry;

fn run_push_neg_wildcard(state: &mut ProofState) -> TacticResult {
    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let push_neg = registry
        .get("push_neg")
        .expect("push_neg should be registered in the production registry");
    (push_neg.handler)(state, &[Expr::const_(Name::from_string("*"), vec![])])
}

fn find_local_decl<'a>(goal: &'a Goal, name: &str) -> &'a LocalDecl {
    goal.local_ctx
        .iter()
        .find(|decl| decl.name == name)
        .unwrap_or_else(|| panic!("expected local declaration '{name}'"))
}

fn wildcard_push_neg_rollback_state() -> (ProofState, Expr, Expr, Expr, FVarId, FVarId) {
    let mut env = setup_env_with_prop_ext();
    let p = add_prop_axiom(&mut env, "P");
    let q = add_prop_axiom(&mut env, "Q");
    let h_bad_ty = Expr::arrow(make_direct_not(make_direct_not(p.clone())), q.clone());
    let h_ok_ty = make_not(&make_not(&p));
    let h_bad_fvar = FVarId::new(0);
    let h_ok_fvar = FVarId::new(1);

    let state = ProofState::with_context(
        env,
        q.clone(),
        vec![
            LocalDecl {
                fvar: h_bad_fvar,
                name: "h_bad".to_string(),
                ty: h_bad_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: h_ok_fvar,
                name: "h_ok".to_string(),
                ty: h_ok_ty.clone(),
                value: None,
            },
        ],
    );

    (state, q, h_bad_ty, h_ok_ty, h_bad_fvar, h_ok_fvar)
}

#[test]
fn test_push_neg_wildcard_dispatch_succeeds_when_only_hypotheses_rewrite() {
    let mut env = setup_env_with_prop_ext();
    let p = add_prop_axiom(&mut env, "P");
    let target = add_prop_axiom(&mut env, "Q");
    let h_fvar = FVarId::new(0);

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: make_not(&make_not(&p)),
            value: None,
        }],
    );

    let result = run_push_neg_wildcard(&mut state);

    assert!(
        result.is_ok(),
        "push_neg at * should succeed when it rewrites at least one hypothesis: {result:?}"
    );

    let goal = state.current_goal().expect("goal should remain open");
    let h = find_local_decl(goal, "h");
    assert_eq!(
        goal.target, target,
        "push_neg at * should leave an already-stable target unchanged"
    );
    assert_eq!(h.ty, p, "push_neg at * should rewrite the local hypothesis");
    assert_ne!(
        h.fvar, h_fvar,
        "push_neg at * should replace the hypothesis through the proof-carry boundary"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "push_neg at * should stay on the proof-carry path when only locals rewrite"
    );
}

#[test]
fn test_push_neg_wildcard_dispatch_rolls_back_prior_hypothesis_rewrites_on_error() {
    let (mut state, target, h_bad_ty, h_ok_ty, h_bad_fvar, h_ok_fvar) =
        wildcard_push_neg_rollback_state();
    let result = run_push_neg_wildcard(&mut state);

    assert!(
        matches!(result, Err(TacticError::TypeCheckFailed(ref message)) if message.contains("legacy push_neg would rewrite it")),
        "push_neg at * should still fail closed when any hypothesis hits the proof-carry guard: {result:?}"
    );

    let goal = state.current_goal().expect("goal should remain open");
    let h_bad = find_local_decl(goal, "h_bad");
    let h_ok = find_local_decl(goal, "h_ok");

    assert_eq!(
        goal.target, target,
        "failed wildcard push_neg should leave the target unchanged"
    );
    assert_eq!(
        h_bad.ty, h_bad_ty,
        "failed wildcard push_neg should roll back the unsupported hypothesis"
    );
    assert_eq!(
        h_bad.fvar, h_bad_fvar,
        "failed wildcard push_neg should restore the original unsupported hypothesis fvar"
    );
    assert_eq!(
        h_ok.ty, h_ok_ty,
        "failed wildcard push_neg should roll back prior successful hypothesis rewrites"
    );
    assert_eq!(
        h_ok.fvar, h_ok_fvar,
        "failed wildcard push_neg should restore the original hypothesis fvar after rollback"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed wildcard push_neg must not record trusted fallback during rollback"
    );
}
