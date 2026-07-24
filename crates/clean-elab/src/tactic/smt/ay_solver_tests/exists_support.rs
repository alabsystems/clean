// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::SmtSolver;
use super::super::*;
use crate::tactic::hypothesis::collect_fvars;
use crate::tactic::LocalDecl;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, Level, Name, TypeChecker};

fn mk_exists_prop_simple(predicate_body: Expr) -> Expr {
    let binder_ty = Expr::prop();
    let predicate = Expr::lam(BinderInfo::Default, binder_ty.clone(), predicate_body);
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            binder_ty,
        ),
        predicate,
    )
}

pub(super) fn mk_exists_prop_identity() -> Expr {
    mk_exists_prop_simple(Expr::bvar(0))
}

pub(super) fn mk_exists_prop_excluded_middle() -> Expr {
    let witness = Expr::bvar(0);
    let not_witness = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        witness.clone(),
    );
    let body = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), witness),
        not_witness,
    );
    mk_exists_prop_simple(body)
}

pub(super) fn mk_exists_prop(binder_ty: Expr, predicate_body: Expr, levels: Vec<Level>) -> Expr {
    let predicate = Expr::lam(BinderInfo::Default, binder_ty.clone(), predicate_body);
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Exists"), levels), binder_ty),
        predicate,
    )
}

pub(super) fn mk_nested_exists_nat_eq() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let inner_body = mk_nat_eq(Expr::bvar(1), Expr::bvar(0));
    let inner_exists = mk_exists_prop(nat_ty.clone(), inner_body, vec![Level::zero()]);
    mk_exists_prop(nat_ty, inner_exists, vec![Level::zero()])
}

pub(super) fn mk_and(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), lhs),
        rhs,
    )
}

pub(super) fn mk_not(expr: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr)
}

pub(super) fn contains_const(expr: &Expr, target: &str) -> bool {
    count_const_occurrences(expr, target) > 0
}

pub(super) fn count_const_occurrences(expr: &Expr, target: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == target),
        ExprKind::App(fun, arg) => {
            count_const_occurrences(fun, target) + count_const_occurrences(arg, target)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const_occurrences(ty, target) + count_const_occurrences(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const_occurrences(ty, target)
                + count_const_occurrences(val, target)
                + count_const_occurrences(body, target)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            count_const_occurrences(inner, target)
        }
        _ => 0,
    }
}

pub(super) fn exists_placeholder_pairs(solver: &SmtSolver) -> Vec<(FVarId, FVarId)> {
    solver
        .exists_witness_bindings()
        .iter()
        .map(|binding| (binding.witness_fvar, binding.witness_proof_fvar))
        .collect()
}

pub(super) fn assert_no_placeholder_leaks(proof: &Expr, placeholder_pairs: &[(FVarId, FVarId)]) {
    let proof_fvars = collect_fvars(proof);
    for (witness_fvar, witness_proof_fvar) in placeholder_pairs {
        assert!(
            !proof_fvars.contains(witness_fvar) && !proof_fvars.contains(witness_proof_fvar),
            "final proof must not leak existential placeholder FVars"
        );
    }
}

pub(super) fn assert_proof_typechecks(proof: &Expr, target: &Expr, local_ctx: &[LocalDecl]) {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_exists().expect("init_exists");
    env.init_classical().expect("init_classical");

    let state = ProofState::with_context(env, target.clone(), local_ctx.to_vec());
    let goal = state.current_goal().expect("goal should exist").clone();
    let tc = TypeChecker::with_context(state.env(), state.build_local_ctx(&goal));
    let inferred = tc
        .infer_type(proof)
        .expect("reconstructed existential proof should typecheck in the original goal context");
    let inferred = tc.whnf(&inferred);
    assert_eq!(
        inferred, *target,
        "reconstructed existential proof should prove the original goal"
    );
}

pub(super) fn mk_int_eq(lhs: Expr, rhs: Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int_ty,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn mk_nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn mk_int_to_prop_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Int"), vec![]),
        Expr::prop(),
    )
}

pub(super) fn mk_fvar_app(head: FVarId, args: &[Expr]) -> Expr {
    let mut result = Expr::fvar(head);
    for arg in args {
        result = Expr::app(result, arg.clone());
    }
    result
}
