// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{FVarId, Level};
use std::sync::Arc;

#[test]
fn test_replace_fvar_with_const_recurses_through_cubical_and_zfc_nodes() {
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);
    let target = FVarId::new(7);
    let untouched = FVarId::new(8);
    let const_name = Name::from_string("Issue1981.replaced");
    let level_param = Name::from_string("u");
    let applied_arg = Expr::prop();

    let expr = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(Expr::fvar(target)),
        })),
        pred: Arc::new(Expr::app(Expr::fvar(untouched), Expr::fvar(target))),
    });

    let replaced = ctx.replace_fvar_with_const(
        expr,
        target,
        &const_name,
        std::slice::from_ref(&level_param),
        std::slice::from_ref(&applied_arg),
    );

    let expected_const = Expr::app(
        Expr::const_(const_name, vec![Level::param(level_param)]),
        applied_arg,
    );
    let expected = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: Arc::new(Expr::from_kind(ExprKind::CubicalPathLam {
            body: Arc::new(expected_const.clone()),
        })),
        pred: Arc::new(Expr::app(Expr::fvar(untouched), expected_const)),
    });

    assert_eq!(
        replaced, expected,
        "replace_fvar_with_const must recurse through Cubical/ZFC variants"
    );
}
