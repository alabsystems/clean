// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The leaf cap on symbolic additive closeout ([`MAX_SUM_NF_LEAVES`]).
//!
//! A Farkas multiplier `k` reaches this module as a binary doubling chain from
//! `scale_bound`: `O(log k)` shared nodes, `k` leaves as a tree. Before the cap
//! the normal form walked the tree, so `k = 2^30` did not finish (trustc,
//! 2026-09-25: > 11 min, 184 GB, in `IntAddNf::flatten`).

use std::sync::mpsc;
use std::time::Duration;

use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::super::expr_builders_arith::CmpOp;
use super::super::theory_lemma_lra_additive::{combine_scaled_bounds, mk_int_add, scale_bound};
use super::{additive_leaf_count_within, try_close_int_additive_nf, MAX_SUM_NF_LEAVES};

fn mk_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_int(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

#[test]
fn the_leaf_count_is_the_tree_size_computed_over_the_shared_dag() {
    let acc = scale_bound(
        &ay::Sort::Int,
        CmpOp::Le,
        &mk_var("x"),
        &mk_int(5),
        &mk_var("h"),
        1000,
    )
    .expect("k = 1000 builds");
    assert_eq!(additive_leaf_count_within(&acc.lhs, 1 << 20), Some(1000));
    assert_eq!(additive_leaf_count_within(&acc.lhs, 1000), Some(1000));
    assert_eq!(additive_leaf_count_within(&acc.lhs, 999), None);
    // A non-additive expression is one leaf.
    assert_eq!(additive_leaf_count_within(&mk_var("x"), 1), Some(1));
}

#[test]
fn a_two_to_the_thirty_multiplier_declines_instead_of_expanding() {
    // Run under a watchdog: a regression of the cap would otherwise hang the
    // test binary (and grow without bound) rather than fail it.
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let x = mk_var("x");
            // `2^30 · (x ≤ 2^32)` + `2^30 · (2^33 ≤ x)`: the capacity row's
            // multiplier on both sides of a shared atom, so without the cap the
            // multiset match would eventually succeed — after 2^31 leaves a side.
            let scaled = scale_bound(
                &ay::Sort::Int,
                CmpOp::Le,
                &x,
                &mk_int(1 << 32),
                &mk_var("g"),
                1 << 30,
            )
            .expect("k = 2^30 builds in O(30) nodes");
            let wide = scale_bound(
                &ay::Sort::Int,
                CmpOp::Le,
                &mk_int(1 << 33),
                &x,
                &mk_var("c"),
                1 << 30,
            )
            .expect("k = 2^30 builds in O(30) nodes");
            let acc = combine_scaled_bounds(&ay::Sort::Int, &mut [scaled, wide])
                .expect("two Le accumulators combine");
            let _ = tx
                .send(try_close_int_additive_nf(acc.op, &acc.lhs, &acc.rhs, &acc.proof).is_none());
        })
        .expect("spawn");
    let declined = rx
        .recv_timeout(Duration::from_secs(60))
        .expect("the capped closeout must return promptly, not expand 2^30 leaves");
    assert!(declined, "a closeout past MAX_SUM_NF_LEAVES must decline");
}

#[test]
fn a_small_weighted_closeout_under_the_cap_still_reconstructs() {
    // `3 · (x ≤ 5)` + `(16 ≤ x + x + x)` ⊢ `16 + 3x ≤ 3x + 15`: shared atoms
    // cancel, `16 ≤ 15` is the residual contradiction. Six leaves on each side.
    let x = mk_var("x");
    let three_x = mk_int_add(&x, &mk_int_add(&x, &x));
    let scaled = scale_bound(&ay::Sort::Int, CmpOp::Le, &x, &mk_int(5), &mk_var("g"), 3)
        .expect("k = 3 builds");
    let lower = scale_bound(
        &ay::Sort::Int,
        CmpOp::Le,
        &mk_int(16),
        &three_x,
        &mk_var("c"),
        1,
    )
    .expect("k = 1 builds");
    let acc = combine_scaled_bounds(&ay::Sort::Int, &mut [scaled, lower]).expect("combine");
    let leaves = additive_leaf_count_within(&acc.lhs, MAX_SUM_NF_LEAVES).unwrap()
        + additive_leaf_count_within(&acc.rhs, MAX_SUM_NF_LEAVES).unwrap();
    assert!(leaves <= MAX_SUM_NF_LEAVES);
    assert!(
        try_close_int_additive_nf(acc.op, &acc.lhs, &acc.rhs, &acc.proof).is_some(),
        "a weighted closeout well under the cap must still reconstruct"
    );
}
