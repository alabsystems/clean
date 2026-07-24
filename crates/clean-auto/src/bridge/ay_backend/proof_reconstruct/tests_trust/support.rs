// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::types::ReconstructionResult;
use super::*;

pub(super) fn mk_trust_single_literal() -> (TermStore, VariableMapping, Proof, Expr) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], vec![], vec![]);

    let negated_goal = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop_p);
    (terms, map, proof, negated_goal)
}

pub(super) fn count_trusted_ay_in_expr(expr: &Expr) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == "trustedAy"),
        ExprKind::App(f, a) => count_trusted_ay_in_expr(f) + count_trusted_ay_in_expr(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_trusted_ay_in_expr(ty) + count_trusted_ay_in_expr(body)
        }
        ExprKind::Let(_, ty, val, body, ..) => {
            count_trusted_ay_in_expr(ty)
                + count_trusted_ay_in_expr(val)
                + count_trusted_ay_in_expr(body)
        }
        _ => 0,
    }
}

pub(super) fn mk_env_with_test_prop() -> clean_kernel::Environment {
    use clean_kernel::{Declaration, Environment};

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("TestP"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add TestP");
    env
}

pub(super) fn mk_p_hypothesis() -> (TermStore, VariableMapping, Expr, FVarId, ay_core::TermId) {
    let prop_p = Expr::const_(Name::from_string("TestP"), vec![]);
    let h_p_id = FVarId::new(10);
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", prop_p.clone(), Expr::prop());
    map.register_hypothesis("p", h_p_id, Expr::fvar(h_p_id), prop_p.clone());
    (terms, map, prop_p, h_p_id, p)
}

pub(super) fn assert_composed_proof_type_checks_to_false(
    env: &clean_kernel::Environment,
    result: &ReconstructionResult,
    proof_term: Expr,
    prop_p: &Expr,
    negated_goal: &Expr,
    h_p_id: FVarId,
    msg: &str,
) {
    use clean_kernel::{BinderInfo, LocalContext, TypeChecker};

    let mut proof_term = proof_term;
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_p_id,
        Name::from_string("h_p"),
        prop_p.clone(),
        BinderInfo::Default,
    );
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let normal_neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            negated_goal.clone(),
            BinderInfo::Default,
        );
    }
    let tc = TypeChecker::with_context(env, ctx);
    let inferred_type = tc.infer_type(&proof_term);
    assert!(
        inferred_type.is_ok(),
        "{msg}: type-check failed: {:?}",
        inferred_type.as_ref().err(),
    );
    let inferred_type = inferred_type.expect("invariant: asserted infer_type success");
    assert!(
        matches!(inferred_type.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "{msg}: expected type False, got {:?}",
        inferred_type.kind(),
    );
}
