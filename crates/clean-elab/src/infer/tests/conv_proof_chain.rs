// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `elab_by_tactic` proof-chain regressions for focused `conv` rewrites.
//!
//! Part of #2540.

use super::*;
use clean_parser::{Span, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};

fn conv_lhs_rw_h_then_rfl_tactics(reverse: bool) -> Vec<SurfaceTactic> {
    vec![
        SurfaceTactic::Conv(
            Span::dummy(),
            SurfaceTacticLocation::Goal,
            vec![
                SurfaceTactic::Named {
                    span: Span::dummy(),
                    name: "lhs".to_string(),
                    args: vec![],
                },
                SurfaceTactic::Rw(
                    Span::dummy(),
                    vec![SurfaceRwRule {
                        span: Span::dummy(),
                        reverse,
                        term: SurfaceExpr::ident("h"),
                    }],
                    SurfaceTacticLocation::Goal,
                ),
            ],
        ),
        SurfaceTactic::Named {
            span: Span::dummy(),
            name: "rfl".to_string(),
            args: vec![],
        },
    ]
}

/// Regression test for #2477/#2529/#2540: `conv { lhs; rw [h] }; rfl` through
/// `elab_by_tactic`.
///
/// History:
/// - #2477: initial conv proof-carry design
/// - #2529: bridge fix resolved HypothesisNotFound
/// - #2540: conv_focus_rewrite resolved the Nat→Nat motive bug for non-Prop focuses
#[test]
fn test_elab_by_tactic_conv_lhs_rewrite_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let tactics = conv_lhs_rw_h_then_rfl_tactics(false);
    let mut ctx = ElabCtx::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let x_fvar = ctx.push_local("x".to_string(), nat.clone());
    let y_fvar = ctx.push_local("y".to_string(), nat);
    let x_expr = Expr::fvar(x_fvar);
    let y_expr = Expr::fvar(y_fvar);

    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = Expr::app(Expr::app(Expr::app(eq_const, nat_ty), x_expr), y_expr);
    ctx.push_local("h".to_string(), target.clone());

    ctx.current_expected_type = Some(target.clone());
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("conv { lhs; rw [h] }; rfl should succeed after #2540 fix");

    let proof_ty = ctx
        .infer_type(&proof)
        .expect("forward conv proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "forward conv proof type should match the original x = y target"
    );
}

/// Regression test for #2540: reverse `conv { lhs; rw [<-h] }; rfl` through
/// `elab_by_tactic`.
///
/// This covers the full theorem-elaboration path with FVar parameters rather
/// than only direct `ProofState` evaluation. The resulting proof must
/// type-check against the original `y = x` goal in the local context.
#[test]
fn test_elab_by_tactic_conv_lhs_reverse_rewrite_preserves_proof_chain() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let tactics = conv_lhs_rw_h_then_rfl_tactics(true);
    let mut ctx = ElabCtx::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let x_fvar = ctx.push_local("x".to_string(), nat.clone());
    let y_fvar = ctx.push_local("y".to_string(), nat);
    let x_expr = Expr::fvar(x_fvar);
    let y_expr = Expr::fvar(y_fvar);

    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let hyp = Expr::app(
        Expr::app(Expr::app(eq_const.clone(), nat_ty.clone()), x_expr.clone()),
        y_expr.clone(),
    );
    let target = Expr::app(Expr::app(Expr::app(eq_const, nat_ty), y_expr), x_expr);
    ctx.push_local("h".to_string(), hyp);

    ctx.current_expected_type = Some(target.clone());
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("conv { lhs; rw [<-h] }; rfl should succeed after #2540 fix");

    let proof_ty = ctx
        .infer_type(&proof)
        .expect("reverse conv proof should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "reverse conv proof type should match the original y = x target"
    );
}
