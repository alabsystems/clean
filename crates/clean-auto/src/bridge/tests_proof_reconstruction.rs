// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for equality proof reconstruction strategies in proof_reconstruction.rs.
//! Tests reflexivity, direct hypothesis, BFS transitivity, and error paths.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::Level;

/// Minimal environment with Eq, Eq.refl, base type A, and constants a, b, c.
fn setup_proof_recon_env() -> Environment {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    env
}

fn make_eq_expr(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

#[test]
fn test_reflexivity_strategy_same_term() {
    let env = setup_proof_recon_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let t1 = bridge.translate_term(&a).unwrap();

    let result = bridge.build_equality_proof(t1, t1, &a, &a, &a_ty, 0);
    assert!(result.is_ok(), "reflexivity should succeed for same term");
    let (step, _proof_term) = result.unwrap();
    assert!(
        matches!(step, ProofStep::Refl(_)),
        "expected Refl proof step, got {:?}",
        step
    );
}

#[test]
fn test_direct_hypothesis_strategy() {
    let env = setup_proof_recon_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let eq_expr = make_eq_expr(&a_ty, &a, &b);
    let fvar = FVarId::new(42);
    bridge
        .add_hypothesis_with_fvar(&eq_expr, Some(fvar))
        .unwrap();

    let t1 = bridge.translate_term(&a).unwrap();
    let t2 = bridge.translate_term(&b).unwrap();

    let result = bridge.build_equality_proof(t1, t2, &a, &b, &a_ty, 0);
    assert!(
        result.is_ok(),
        "hypothesis-based proof should succeed: {:?}",
        result.err()
    );
}

#[test]
fn test_all_strategies_exhausted_returns_error() {
    let env = setup_proof_recon_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let t1 = bridge.translate_term(&a).unwrap();
    let t2 = bridge.translate_term(&b).unwrap();

    // No hypotheses registered, so all strategies should fail
    let result = bridge.build_equality_proof(t1, t2, &a, &b, &a_ty, 0);
    assert!(result.is_err(), "should fail with no available proof path");
    match result.unwrap_err() {
        BridgeError::ProofTraceFailed(msg) => {
            assert!(
                msg.contains("proof strategies exhausted"),
                "error should mention strategies: {}",
                msg
            );
        }
        other => panic!("expected ProofTraceFailed, got {:?}", other),
    }
}

#[test]
fn test_transitive_proof_via_intermediate() {
    let env = setup_proof_recon_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Add a = b hypothesis
    let eq_ab = make_eq_expr(&a_ty, &a, &b);
    let fvar_ab = FVarId::new(100);
    bridge
        .add_hypothesis_with_fvar(&eq_ab, Some(fvar_ab))
        .unwrap();

    // Add b = c hypothesis
    let eq_bc = make_eq_expr(&a_ty, &b, &c);
    let fvar_bc = FVarId::new(101);
    bridge
        .add_hypothesis_with_fvar(&eq_bc, Some(fvar_bc))
        .unwrap();

    let t1 = bridge.translate_term(&a).unwrap();
    let t3 = bridge.translate_term(&c).unwrap();

    // Should find path a->b->c via BFS transitivity (Strategy 4)
    let result = bridge.build_equality_proof(t1, t3, &a, &c, &a_ty, 0);
    assert!(
        result.is_ok(),
        "transitive proof a=b, b=c -> a=c should succeed: {:?}",
        result.err()
    );
}

/// Regression test for #2367: build_equality_proof at MAX depth returns graceful
/// error (not stack overflow). Calling with depth=100 (the limit defined in
/// proof_reconstruction.rs) ensures any congruence fallback (Strategy 5) bails out.
#[test]
fn test_depth_limit_returns_error_not_overflow() {
    let env = setup_proof_recon_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let t1 = bridge.translate_term(&a).unwrap();
    let t2 = bridge.translate_term(&b).unwrap();

    // Call at max depth (100) — Strategy 5 (congruence) must bail out immediately.
    // Without the depth guard, deeply nested terms would stack-overflow here.
    let result = bridge.build_equality_proof(t1, t2, &a, &b, &a_ty, 100);
    assert!(
        result.is_err(),
        "at max depth, build_equality_proof should fail gracefully (not stack overflow)"
    );
}
