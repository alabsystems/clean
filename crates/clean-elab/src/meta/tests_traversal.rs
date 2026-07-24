// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{Environment, Expr, ExprKind, Name};
use std::sync::Arc;

#[test]
fn test_interpret_substitute_bvar_recurses_through_cubical_and_zfc_nodes() {
    let env = Environment::new();
    let interp = RuntimeInterpreter::new(&env);

    let expr = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::bvar(1)),
        })),
        pred: Arc::new(Expr::bvar(1)),
    });

    let result = interp.substitute_bvar(&expr, 0, &Expr::prop());

    let expected = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::prop()),
        })),
        pred: Arc::new(Expr::prop()),
    });

    assert_eq!(
        result, expected,
        "substitute_bvar must recurse through Cubical/ZFC variants"
    );
}

#[test]
fn test_synth_instance_q_stuck_on_hidden_metas_in_cubical_and_zfc_nodes() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);
    let hidden_meta = ctx.fresh_meta(Expr::type_());

    let hidden_expr = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(hidden_meta.clone()),
        })),
        pred: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(
            Arc::new(hidden_meta),
        )))),
    });

    assert!(
        ctx.goal_has_unresolved_metas(&hidden_expr),
        "goal_has_unresolved_metas should find hidden metas inside Cubical/ZFC nodes"
    );

    let class_goal = Expr::app(Expr::const_(Name::from_string("Add"), vec![]), hidden_expr);
    assert!(
        matches!(
            ctx.synth_instance_q(&class_goal),
            SynthInstanceQResult::Stuck
        ),
        "synth_instance_q should report Stuck when hidden metas survive inside Cubical/ZFC nodes"
    );
}
