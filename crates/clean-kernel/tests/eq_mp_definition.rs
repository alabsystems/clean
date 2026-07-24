// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage for the `Eq.mp` forward-transport kernel definition.

use clean_kernel::{Environment, Expr, ExprKind, Name};

fn contains_const_named(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => contains_const_named(f, target) || contains_const_named(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_const_named(ty, target) || contains_const_named(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_const_named(ty, target)
                || contains_const_named(val, target)
                || contains_const_named(body, target)
        }
        _ => false,
    }
}

fn count_pi_binders(mut expr: &Expr) -> usize {
    let mut count = 0;
    while let ExprKind::Pi(_, _, body) = expr.kind() {
        count += 1;
        expr = body;
    }
    count
}

#[test]
fn test_eq_mp_definition_shape() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let eq_mp = env.get_const(&Name::from_string("Eq.mp")).unwrap();
    let eq_mp_val = eq_mp
        .value
        .as_ref()
        .expect("Eq.mp should have a definition body");

    assert!(
        matches!(eq_mp_val.kind(), ExprKind::Lam(..)),
        "Eq.mp value must be a lambda abstraction"
    );
    assert!(eq_mp.is_reducible, "Eq.mp should be reducible");
    assert_eq!(
        eq_mp.level_params.len(),
        1,
        "Eq.mp has 1 universe param (u)"
    );
    assert_eq!(
        count_pi_binders(&eq_mp.type_),
        4,
        "Eq.mp type should have 4 Pi binders (alpha, beta, h, a)"
    );
    assert!(
        contains_const_named(eq_mp_val, "cast"),
        "Eq.mp definition should route through cast for forward transport"
    );
    assert!(
        !contains_const_named(eq_mp_val, "Eq.symm"),
        "Eq.mp should not reverse the equality via Eq.symm"
    );
}
