// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_auto::{SmtBridge, SmtVerificationResult};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr};

fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
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

fn assert_unknown_lossy<E: std::fmt::Debug>(
    result: Result<SmtVerificationResult, E>,
    expected_count: &str,
    expected_kind: &str,
) {
    match result {
        Ok(SmtVerificationResult::Unknown(reason)) => {
            assert!(
                reason.contains("lossy translation"),
                "Unknown reason should mention lossy translation, got: {reason}"
            );
            assert!(
                reason.contains(expected_count),
                "Unknown reason should report the lossy count, got: {reason}"
            );
            assert!(
                reason.contains(expected_kind),
                "Unknown reason should expose the lossy expression kind `{expected_kind}`, got: {reason}"
            );
        }
        other => panic!("expected lossy lowering to return Unknown, got: {other:?}"),
    }
}

#[test]
fn test_let_equality_goal_returns_unknown_when_term_lowering_is_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let let_expr = Expr::let_named(Name::anon(), nat_ty, Expr::nat_lit(0), Expr::bvar(0), false);
    let goal = nat_eq(let_expr, Expr::nat_lit(0));

    assert_unknown_lossy(bridge.prove(&goal), "2 lossy expressions", "Let");
}

#[test]
fn test_proj_equality_goal_returns_unknown_when_term_lowering_is_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let proj_expr = Expr::proj(
        Name::from_string("PairLike"),
        0,
        Expr::const_(Name::from_string("pairWitness"), vec![]),
    );
    let goal = nat_eq(proj_expr, Expr::nat_lit(0));

    assert_unknown_lossy(bridge.prove(&goal), "2 lossy expressions", "Proj");
}

#[test]
fn test_let_prop_goal_returns_unknown_when_atom_lowering_is_lossy() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);
    let let_prop = Expr::let_named(
        Name::anon(),
        Expr::prop(),
        Expr::const_(Name::from_string("opaqueProp"), vec![]),
        Expr::bvar(0),
        false,
    );

    assert_unknown_lossy(bridge.prove(&let_prop), "1 lossy expression", "Let");
}
