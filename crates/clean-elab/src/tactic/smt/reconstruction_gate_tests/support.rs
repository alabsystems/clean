// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helpers for reconstruction-gate coverage.

#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::test_utils::{
    empty_residual_trust_summary, kernel_reconstruction_candidate,
};
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::KernelReconstructionCandidate;
#[cfg(feature = "ay-smt")]
use clean_kernel::name::Name;
#[cfg(feature = "ay-smt")]
use clean_kernel::{env::Declaration, TypeChecker};
#[cfg(feature = "ay-smt")]
use clean_kernel::{Environment, Expr};

#[cfg(feature = "ay-smt")]
pub(super) fn mk_absurd_false(prop: &Expr, positive_proof: &Expr, negated_proof: &Expr) -> Expr {
    use clean_kernel::level::Level;

    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
                    prop.clone(),
                ),
                Expr::const_(Name::from_string("False"), vec![]),
            ),
            positive_proof.clone(),
        ),
        negated_proof.clone(),
    )
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_trusted_ay_proof(env: &Environment, goal_ty: &Expr) -> Expr {
    use clean_kernel::level::Level;

    let level = TypeChecker::new(env)
        .infer_sort(goal_ty)
        .unwrap_or(Level::zero());
    Expr::app(
        Expr::const_(Name::from_string("trustedAy"), vec![level]),
        goal_ty.clone(),
    )
}

#[cfg(feature = "ay-smt")]
pub(super) fn assert_by_contradiction_head(proof: &Expr, context: &str) {
    match proof.get_app_fn().kind() {
        clean_kernel::ExprKind::Const(name, _) => assert_eq!(
            *name,
            Name::from_string("Classical.byContradiction"),
            "{context}: expected Classical.byContradiction head, got {name}"
        ),
        other => unreachable!("{context}: expected Const head, got {other:?}"),
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_candidate(
    refutation: Expr,
    negated_goal_fvar: Option<clean_kernel::FVarId>,
    trust_subterm_count: usize,
) -> KernelReconstructionCandidate {
    kernel_reconstruction_candidate(
        refutation,
        negated_goal_fvar,
        clean_auto::bridge::ay_contract::ReconstructionQuality::from_trust_count(
            trust_subterm_count,
        ),
        empty_residual_trust_summary(),
    )
}

#[cfg(feature = "ay-smt")]
pub(super) fn add_axiom(env: &mut Environment, name: &str, ty: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
    })
    .expect("axiom declaration should succeed");
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_base_env(init_trusted_ay: bool) -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init True/False");
    env.init_classical().expect("init Classical");
    if init_trusted_ay {
        env.init_trusted_ay().expect("init trustedAy");
    }
    env
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_prop_env(init_trusted_ay: bool) -> (Environment, Expr) {
    let mut env = mk_base_env(init_trusted_ay);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    (env, p)
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_prop_hyp_env(init_trusted_ay: bool) -> (Environment, Expr) {
    let (mut env, p) = mk_prop_env(init_trusted_ay);
    add_axiom(&mut env, "hp", p.clone());
    (env, p)
}

#[cfg(feature = "ay-smt")]
pub(super) fn mk_negated(prop: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), prop.clone())
}

#[cfg(feature = "ay-smt")]
pub(super) fn contains_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => name.to_string() == target,
        clean_kernel::ExprKind::App(fun, arg) => {
            contains_const(fun, target) || contains_const(arg, target)
        }
        clean_kernel::ExprKind::Lam(_, ty, body) | clean_kernel::ExprKind::Pi(_, ty, body) => {
            contains_const(ty, target) || contains_const(body, target)
        }
        clean_kernel::ExprKind::Let(_, ty, val, body, _) => {
            contains_const(ty, target)
                || contains_const(val, target)
                || contains_const(body, target)
        }
        clean_kernel::ExprKind::Proj(_, _, expr) | clean_kernel::ExprKind::MData(_, expr) => {
            contains_const(expr, target)
        }
        _ => false,
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn assert_inferred_type(
    env: &Environment,
    proof: &Expr,
    expected: &Expr,
    context: &str,
) {
    let inferred = TypeChecker::new(env)
        .infer_type(proof)
        .expect("proof should typecheck");
    assert_eq!(inferred, *expected, "{context}");
}
