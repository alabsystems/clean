// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ring_proof_sort::{build_op_chain, merge_sorted_chains};
use super::*;
use clean_kernel::env::Declaration;

fn proof_sort_env() -> (Environment, Expr) {
    let mut env = Environment::with_prelude();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["a", "b", "c", "d"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    (env, nat)
}

fn nat_add_head() -> Expr {
    Expr::const_(Name::from_string("Nat.add"), vec![])
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(nat_add_head(), a), b)
}

fn var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn assert_proof_closes(mut state: ProofState, proof: Expr) {
    let goal = state.current_goal().expect("goal should exist").clone();
    state
        .close_goal(&goal, proof)
        .expect("proof should close goal");
    assert!(state.is_complete(), "goal should be fully closed");
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "sort proofs must stay trust-free"
    );
}

#[test]
fn test_build_op_chain_single_term_returns_term() {
    let a = var("a");
    let prefix: [Expr; 0] = [];
    assert_eq!(
        build_op_chain(&nat_add_head(), &prefix, std::slice::from_ref(&a)),
        a
    );
}

#[test]
fn test_build_op_chain_three_terms_left_associates() {
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let prefix: [Expr; 0] = [];
    let chain = build_op_chain(&nat_add_head(), &prefix, &[a.clone(), b.clone(), c.clone()]);
    assert_eq!(chain, nat_add(nat_add(a, b), c));
}

#[test]
fn test_merge_sorted_chains_flattens_right_nested_rhs() {
    let (env, nat) = proof_sort_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let head = nat_add_head();
    let prefix: [Expr; 0] = [];
    let a_expr = a.clone();
    let b_expr = build_op_chain(&head, &prefix, &[b.clone(), c.clone()]);
    let lhs = nat_add(a_expr.clone(), b_expr.clone());
    let rhs = build_op_chain(&head, &prefix, &[a.clone(), b.clone(), c.clone()]);
    let state = ProofState::new(env, make_eq(nat.clone(), lhs, rhs.clone()));
    let goal = state.current_goal().expect("goal should exist").clone();
    let (merged, proof) = merge_sorted_chains(
        &state,
        &goal,
        &a_expr,
        &b_expr,
        std::slice::from_ref(&a),
        &[b, c],
        "Nat.add",
        &head,
        &prefix,
    )
    .expect("merge should succeed");
    assert_eq!(merged, rhs, "flattening should preserve sorted order");
    assert_proof_closes(state, proof.expect("flattening should produce a proof"));
}

#[test]
fn test_merge_sorted_chains_interleaved_closes_goal() {
    let (env, nat) = proof_sort_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let d = var("d");
    let head = nat_add_head();
    let prefix: [Expr; 0] = [];
    let a_expr = build_op_chain(&head, &prefix, &[a.clone(), c.clone()]);
    let b_expr = build_op_chain(&head, &prefix, &[b.clone(), d.clone()]);
    let lhs = nat_add(a_expr.clone(), b_expr.clone());
    let rhs = build_op_chain(
        &head,
        &prefix,
        &[a.clone(), b.clone(), c.clone(), d.clone()],
    );
    let state = ProofState::new(env, make_eq(nat.clone(), lhs, rhs.clone()));
    let goal = state.current_goal().expect("goal should exist").clone();
    let (merged, proof) = merge_sorted_chains(
        &state,
        &goal,
        &a_expr,
        &b_expr,
        &[a, c],
        &[b, d],
        "Nat.add",
        &head,
        &prefix,
    )
    .expect("merge should succeed");
    assert_eq!(merged, rhs, "merged chain should be sorted");
    assert_proof_closes(state, proof.expect("merge should produce a proof"));
}

#[test]
fn test_merge_sorted_chains_last_pair_swap_closes_goal() {
    let (env, nat) = proof_sort_env();
    let a = var("a");
    let b = var("b");
    let c = var("c");
    let d = var("d");
    let head = nat_add_head();
    let prefix: [Expr; 0] = [];
    let a_expr = build_op_chain(&head, &prefix, &[a.clone(), b.clone(), d.clone()]);
    let b_expr = c.clone();
    let lhs = nat_add(a_expr.clone(), b_expr.clone());
    let rhs = build_op_chain(
        &head,
        &prefix,
        &[a.clone(), b.clone(), c.clone(), d.clone()],
    );
    let state = ProofState::new(env, make_eq(nat.clone(), lhs, rhs.clone()));
    let goal = state.current_goal().expect("goal should exist").clone();
    let (merged, proof) = merge_sorted_chains(
        &state,
        &goal,
        &a_expr,
        &b_expr,
        &[a, b, d],
        std::slice::from_ref(&c),
        "Nat.add",
        &head,
        &prefix,
    )
    .expect("merge should succeed");
    assert_eq!(merged, rhs, "last-pair swap should produce canonical order");
    assert_proof_closes(state, proof.expect("last-pair swap should produce a proof"));
}

#[test]
fn test_merge_sorted_chains_sorted_pair_needs_no_proof() {
    let (env, nat) = proof_sort_env();
    let a = var("a");
    let b = var("b");
    let head = nat_add_head();
    let prefix: [Expr; 0] = [];
    let lhs = nat_add(a.clone(), b.clone());
    let state = ProofState::new(env, make_eq(nat, lhs.clone(), lhs.clone()));
    let goal = state.current_goal().expect("goal should exist").clone();
    let (merged, proof) = merge_sorted_chains(
        &state,
        &goal,
        &a,
        &b,
        std::slice::from_ref(&a),
        std::slice::from_ref(&b),
        "Nat.add",
        &head,
        &prefix,
    )
    .expect("merge should succeed");
    assert_eq!(merged, lhs, "already-sorted pair should stay unchanged");
    assert!(
        proof.is_none(),
        "already-sorted pair should not need a proof"
    );
}

#[test]
fn test_merge_sorted_chains_reverse_pair_closes_with_direct_commutation() {
    let (env, nat) = proof_sort_env();
    let a = var("a");
    let b = var("b");
    let head = nat_add_head();
    let prefix: [Expr; 0] = [];
    let lhs = nat_add(b.clone(), a.clone());
    let rhs = nat_add(a.clone(), b.clone());
    let state = ProofState::new(env, make_eq(nat, lhs.clone(), rhs.clone()));
    let goal = state.current_goal().expect("goal should exist").clone();
    let (merged, proof) = merge_sorted_chains(
        &state,
        &goal,
        &b,
        &a,
        std::slice::from_ref(&b),
        std::slice::from_ref(&a),
        "Nat.add",
        &head,
        &prefix,
    )
    .expect("merge should succeed");
    assert_eq!(merged, rhs, "reverse-sorted pair should canonicalize");
    assert_proof_closes(
        state,
        proof.expect("reverse-sorted pair should produce a commutation proof"),
    );
}
