// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification-focused infer elaboration tests split by concern.

pub(super) use super::*;

pub(super) fn elab_decl_with_nat_env(input: &str) -> Result<ElabResult, ElabError> {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_decl_for_elab(input)?;
    ctx.elab_decl(&surface)
}

pub(super) fn elab_decl_with_prelude_env(input: &str) -> Result<ElabResult, ElabError> {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_decl_for_elab(input)?;
    ctx.elab_decl(&surface)
}

pub(super) fn eq_target(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

pub(super) fn assert_tactic_preserves_target(
    env: &Environment,
    target: Expr,
    tactic_src: &str,
    success_message: &str,
    closed_message: &str,
    type_message: &str,
) {
    let surface = parse_expr(tactic_src).expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(env);
    ctx.current_expected_type = Some(target.clone());
    let proof = ctx.elab_by_tactic(&tactics).expect(success_message);

    assert!(!proof.has_fvar_quick(), "{closed_message}, got: {proof:?}");
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(ctx.is_def_eq(&proof_ty, &target), "{type_message}");
}

mod cert_verifier;
mod goal_bridge;
mod ring_dsimp;
mod simp_conv;
mod tactic_entry;
mod unfold_push_neg;
