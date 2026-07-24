// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for iterative_drop of deep expression trees (#1310).
//!
//! Verifies that `iterative_drop()` can handle expressions far deeper than
//! the default 8MB stack allows for recursive Drop. The default Rust test
//! thread has an 8MB stack, which overflows at ~20K recursive Drop frames.

use clean_kernel::{iterative_drop, Expr, FVarId, Name};

/// A 20K-deep App chain can be dropped through normal `Drop` without stack overflow.
///
/// `Expr::drop` switches to iterative teardown when cached depth saturates.
#[test]
fn auto_drop_handles_20k_deep_app_chain() {
    let func = Expr::const_(Name::from_string("f"), vec![]);
    let mut deep_expr = Expr::fvar(FVarId::new(0));
    for _ in 0..20_000 {
        deep_expr = Expr::app(func.clone(), deep_expr);
    }

    assert!(
        deep_expr.has_fvar_quick(),
        "deep expression should contain FVar"
    );

    drop(deep_expr);
}

/// A 20K-deep App chain can be dropped without stack overflow using iterative_drop.
///
/// This test creates the same 20K-deep expression that causes SIGABRT with
/// recursive Drop in the pre-#1415 implementation.
/// Using `iterative_drop()` instead of `drop()` avoids the stack overflow.
#[test]
fn iterative_drop_handles_20k_deep_app_chain() {
    let func = Expr::const_(Name::from_string("f"), vec![]);
    let mut deep_expr = Expr::fvar(FVarId::new(0));
    for _ in 0..20_000 {
        deep_expr = Expr::app(func.clone(), deep_expr);
    }

    // Verify the expression was constructed correctly.
    assert!(
        deep_expr.has_fvar_quick(),
        "deep expression should contain FVar"
    );

    // Drop iteratively — this would stack-overflow with regular drop.
    iterative_drop(deep_expr);
}

/// A 50K-deep nested lambda chain can be dropped without stack overflow.
#[test]
fn iterative_drop_handles_50k_deep_lambda_chain() {
    let mut deep_expr = Expr::fvar(FVarId::new(1));
    for _ in 0..50_000 {
        deep_expr = Expr::lam(clean_kernel::BinderInfo::Default, Expr::prop(), deep_expr);
    }

    assert!(
        deep_expr.has_fvar_quick(),
        "deep lambda chain should propagate has_fvar"
    );

    iterative_drop(deep_expr);
}

/// Shared expressions (Arc refcount > 1) are handled correctly.
#[test]
fn iterative_drop_handles_shared_subexpressions() {
    let shared = Expr::const_(Name::from_string("shared"), vec![]);
    let mut deep_expr = shared.clone(); // refcount > 1
    for _ in 0..20_000 {
        deep_expr = Expr::app(shared.clone(), deep_expr);
    }

    // Drop the deep expression — shared subexpressions should just decrement refcount.
    iterative_drop(deep_expr);

    // The shared expression should still be alive (its refcount was > 1 at each level).
    assert_eq!(
        format!("{shared}"),
        "shared",
        "shared subexpression should survive iterative_drop of the deep tree"
    );
}
