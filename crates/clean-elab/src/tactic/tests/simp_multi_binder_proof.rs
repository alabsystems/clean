// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-valid regression coverage for multi-binder simp theorem application.
//!
//! Part of #2516.

use super::*;
use crate::tactic::simp::{collect_simp_lemmas, simp_expr, SimpConfig};
use clean_kernel::env::SimpPriority;
use serial_test::serial;

fn add_binary_function(env: &mut Environment, name: &str) {
    let n = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n.clone(),
            Expr::pi(BinderInfo::Default, n.clone(), n),
        ),
    })
    .unwrap();
}

fn add_ternary_function(env: &mut Environment, name: &str) {
    let n = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n.clone(),
            Expr::pi(
                BinderInfo::Default,
                n.clone(),
                Expr::pi(BinderInfo::Default, n.clone(), n),
            ),
        ),
    })
    .unwrap();
}

fn pair_app(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("pair"), vec![]), lhs),
        rhs,
    )
}

fn tri_app(x: Expr, y: Expr, z: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("tri"), vec![]), x),
            y,
        ),
        z,
    )
}

fn assert_kernel_valid_proof(env: &Environment, proof: &Expr, expected_ty: &Expr, context: &str) {
    let tc = TypeChecker::new(env);
    assert!(
        tc.check_type(proof, expected_ty).is_ok(),
        "{context}: proof must type-check against the rewritten equality"
    );
}

#[test]
#[serial]
fn test_simp_expr_multi_binder_registered_lemma_proof_typechecks() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    add_binary_function(&mut env, "pair");

    let n = Expr::const_(Name::from_string("N"), vec![]);
    let pair_left_ty = Expr::pi(
        BinderInfo::Default,
        n.clone(),
        Expr::pi(
            BinderInfo::Default,
            n,
            make_eq_n(pair_app(Expr::bvar(1), Expr::bvar(0)), Expr::bvar(1)),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pair_left"),
        level_params: vec![],
        type_: pair_left_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("pair_left"), SimpPriority::Default);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let pair_xy = pair_app(x.clone(), y);
    let expected_ty = make_eq_n(pair_xy.clone(), x.clone());
    let axiom_before = axiom_snapshot();

    let state = ProofState::new(env, make_eq_n(x.clone(), x.clone()));
    let goal = state.current_goal().unwrap().clone();
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);
    let result = simp_expr(&state, &goal, &pair_xy, &lemmas, &config);

    assert_eq!(
        result.expr, x,
        "simp_expr should instantiate multi-binder theorem arguments in binder order"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("multi-binder simp lemma should produce a proof term");
    assert_kernel_valid_proof(state.env(), proof, &expected_ty, "pair_left");
    assert_no_trusted_axiom_usage("simp_expr", "multi-binder pair_left rewrite", axiom_before);
}

#[test]
#[serial]
fn test_simp_default_three_binder_registered_lemma_closes_with_kernel_valid_proof() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    add_ternary_function(&mut env, "tri");

    let n = Expr::const_(Name::from_string("N"), vec![]);
    let tri_middle_ty = Expr::pi(
        BinderInfo::Default,
        n.clone(),
        Expr::pi(
            BinderInfo::Default,
            n.clone(),
            Expr::pi(
                BinderInfo::Default,
                n,
                make_eq_n(
                    tri_app(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("tri_middle"),
        level_params: vec![],
        type_: tri_middle_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("tri_middle"), SimpPriority::Default);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    let goal_ty = make_eq_n(tri_app(x, y.clone(), z), y);
    let mut state = ProofState::new(env, goal_ty.clone());
    let axiom_before = axiom_snapshot();

    simp_default(&mut state).expect("simp should close a goal rewritten by a three-binder theorem");

    assert!(
        state.is_complete(),
        "simp should close the goal after rewriting the lhs to the rhs"
    );
    let closed = state
        .closed_proof()
        .expect("closed goal should expose a kernel-checkable proof term");
    assert_kernel_valid_proof(state.env(), &closed, &goal_ty, "tri_middle closed proof");
    assert_no_trusted_axiom_usage("simp", "three-binder tri_middle rewrite", axiom_before);
}
