// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end proof-chain regression for chained `simp` through `elab_by_tactic`.
//!
//! Part of #2492: validates that the simp transitivity lane carries proof terms
//! through multi-step LHS rewrites without falling back to `trustedArith`.
//! This is the elab_by_tactic-level regression (acceptance criterion 3).
//!
//! Separated from `verification.rs` per #2491 / AC #4.

use super::*;
use crate::tactic::{arith_proof_count, reset_arith_counter};
use clean_kernel::env::SimpPriority;
use clean_parser::SurfaceExpr;
use serial_test::serial;

/// Build an environment with Nat, Eq, and two registered @[simp] lemmas
/// that require chained rewriting through the simp transitivity lane.
///
/// Constants: `a`, `b`, `c` : Nat
/// Lemmas:
///   `a_eq_b : @Eq Nat a b` (registered @[simp])
///   `b_eq_c : @Eq Nat b c` (registered @[simp])
///
/// Target: `@Eq Nat a c`
///
/// The main simp loop cannot simplify the whole target expression
/// (the target IS an equality, not a simplifiable subexpression).
/// The transitivity lane rewrites the LHS: a → b (via a_eq_b) → c (via b_eq_c).
/// Then rfl closes `c = c`.
fn setup_chained_simp_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_u1 = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Declare a, b, c : Nat
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // a_eq_b : @Eq Nat a b
    let eq_ab = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), a.clone()),
        b.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a_eq_b"),
        level_params: vec![],
        type_: eq_ab,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("a_eq_b"), SimpPriority::Default);

    // b_eq_c : @Eq Nat b c
    let eq_bc = Expr::app(
        Expr::app(Expr::app(eq_u1.clone(), nat.clone()), b.clone()),
        c.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b_eq_c"),
        level_params: vec![],
        type_: eq_bc,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("b_eq_c"), SimpPriority::Default);

    // Target: @Eq Nat a c
    let target = Expr::app(Expr::app(Expr::app(eq_u1, nat), a), c);

    (env, target)
}

/// Regression test for #2492: chained `simp` must preserve the proof chain through
/// `elab_by_tactic` when the transitivity lane chains multiple simp lemma rewrites.
///
/// Target: `a = c`
/// Tactic: `by simp`
/// Transitivity lane:
///   Step 1: `a_eq_b` rewrites LHS `a → b`
///   Step 2: `b_eq_c` rewrites LHS `b → c`
///   Step 3: `rfl` closes `c = c`
///
/// Exercises the multi-step simp transitivity proof-carry path (#2492).
/// Without proof-carry, the transitivity lane would fall back to
/// `replace_target_with_trusted_fallback` and increment `trustedArith`.
#[test]
#[serial]
fn test_elab_by_tactic_chained_simp_preserves_proof_chain() {
    let (env, target) = setup_chained_simp_env();
    reset_arith_counter();
    let arith_before = arith_proof_count();

    let surface = parse_expr("by simp").expect("by-tactic expression should parse");
    let SurfaceExpr::ByTactic(_, tactics) = surface else {
        panic!("expected a ByTactic surface expression");
    };

    let mut ctx = ElabCtx::new(&env);
    ctx.current_expected_type = Some(target.clone());
    let proof = ctx
        .elab_by_tactic(&tactics)
        .expect("chained simp should elaborate successfully through elab_by_tactic");

    // Proof should be closed (no free variables)
    assert!(
        !proof.has_fvar_quick(),
        "chained simp proof should be closed, got: {proof:?}"
    );

    // Proof should type-check against the original target
    let proof_ty = ctx
        .infer_type(&proof)
        .expect("elab_by_tactic output should have an inferable type");
    assert!(
        ctx.is_def_eq(&proof_ty, &target),
        "chained simp proof type should match the original target"
    );

    // No trusted axiom usage — the entire chain should be kernel-checkable
    let arith_after = arith_proof_count();
    assert_eq!(
        arith_after - arith_before,
        0,
        "chained simp should not increment trustedArith counter \
         (before={arith_before}, after={arith_after})"
    );
}
