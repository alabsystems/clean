// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_classify_eq() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let eq_expr = make_eq(a_ty, a.clone(), b.clone());
    let class = bridge.classify_prop(&eq_expr);

    assert!(
        matches!(
            &class,
            LogicalForm::Eq { ty, lhs, rhs }
                if matches!(ty.kind(), ExprKind::Const(n, _) if n.to_string() == "A")
                    && matches!(lhs.kind(), ExprKind::Const(n, _) if n.to_string() == "a")
                    && matches!(rhs.kind(), ExprKind::Const(n, _) if n.to_string() == "b")
        ),
        "Expected Eq(A, a, b), got {class:?}"
    );
}

#[test]
fn test_logicalform_to_expr_eq_with_known_type_succeeds() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    // A is declared as Type in setup_env, so sort inference should succeed.
    let form = LogicalForm::Eq {
        ty: Expr::const_(Name::from_string("A"), vec![]),
        lhs: Expr::const_(Name::from_string("a"), vec![]),
        rhs: Expr::const_(Name::from_string("b"), vec![]),
    };
    let result = bridge.logicalform_to_expr(&form);
    assert!(
        result.is_ok(),
        "logicalform_to_expr should succeed for declared type A"
    );
}

#[test]
fn test_logicalform_to_expr_eq_with_unknown_type_returns_infer_sort_failed() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    // "Unknown" is not declared in setup_env, so sort_level_of_type will fail.
    let form = LogicalForm::Eq {
        ty: Expr::const_(Name::from_string("Unknown"), vec![]),
        lhs: Expr::const_(Name::from_string("a"), vec![]),
        rhs: Expr::const_(Name::from_string("b"), vec![]),
    };
    let result = bridge.logicalform_to_expr(&form);
    assert!(
        result.is_err(),
        "logicalform_to_expr should fail for undeclared type"
    );
    let err = result.expect_err("unknown types should fail sort inference");
    assert!(
        matches!(err, BridgeError::InferSortFailed { .. }),
        "Expected InferSortFailed, got {err:?}"
    );
}

#[test]
fn test_logicalform_to_expr_atom_always_succeeds() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    // Atom forms should always succeed (no sort inference needed).
    let form = LogicalForm::Atom(Expr::const_(Name::from_string("p"), vec![]));
    let result = bridge.logicalform_to_expr(&form);
    assert!(
        result.is_ok(),
        "logicalform_to_expr should always succeed for Atom"
    );
}
