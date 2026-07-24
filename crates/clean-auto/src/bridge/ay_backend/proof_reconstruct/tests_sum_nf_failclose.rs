// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed negative-case regression tests for `try_close_int_additive_nf`.
//!
//! Part of #2595: verify the sum-NF closeout path returns `None` when the
//! residual after atom cancellation is NOT a concrete contradiction.
//! These complement the inline success-path test in `theory_lemma_lra_sum_nf.rs`.

use super::expr_builders_arith::CmpOp;
use super::theory_lemma_lra_additive::mk_int_add;
use super::theory_lemma_lra_sum_nf::try_close_int_additive_nf;
use clean_kernel::name::Name;
use clean_kernel::Expr;

fn mk_var(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Build `@Int.ofNat n` for a non-negative integer literal.
fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

#[test]
fn test_try_close_non_contradictory_residual_returns_none() {
    // 3 + x + y ≤ 4 + x + y → residual 3 ≤ 4 is satisfiable, not a contradiction
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_int_add(&mk_int_ofnat(3), &mk_int_add(&x, &y));
    let rhs = mk_int_add(&mk_int_ofnat(4), &mk_int_add(&x, &y));
    let proof = mk_var("h");

    assert!(
        try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "3 ≤ 4 is satisfiable — must return None, not a spurious proof of False"
    );
}

#[test]
fn test_try_close_unshared_atoms_returns_none() {
    // x + 3 ≤ y + 2 → atoms don't match (x vs y), can't cancel
    let x = mk_var("x");
    let y = mk_var("y");
    let lhs = mk_int_add(&x, &mk_int_ofnat(3));
    let rhs = mk_int_add(&y, &mk_int_ofnat(2));
    let proof = mk_var("h");

    assert!(
        try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "unshared atoms prevent cancellation — must return None"
    );
}

#[test]
fn test_try_close_partially_shared_atoms_returns_none() {
    // x + z + 3 ≤ x + w + 2 → only x is shared, z vs w remain symbolic
    let x = mk_var("x");
    let z = mk_var("z");
    let w = mk_var("w");
    let lhs = mk_int_add(&mk_int_add(&x, &z), &mk_int_ofnat(3));
    let rhs = mk_int_add(&mk_int_add(&x, &w), &mk_int_ofnat(2));
    let proof = mk_var("h");

    assert!(
        try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "partially shared atoms leave symbolic residual — must return None"
    );
}

#[test]
fn test_try_close_le_equal_constants_returns_none() {
    // x + 3 ≤ x + 3 → residual 3 ≤ 3 is satisfiable (equality holds)
    let x = mk_var("x");
    let lhs = mk_int_add(&x, &mk_int_ofnat(3));
    let rhs = mk_int_add(&x, &mk_int_ofnat(3));
    let proof = mk_var("h");

    assert!(
        try_close_int_additive_nf(CmpOp::Le, &lhs, &rhs, &proof).is_none(),
        "3 ≤ 3 is satisfiable — must return None for Le"
    );
}

#[test]
fn test_try_close_lt_equal_constants_returns_some() {
    // x + 3 < x + 3 → residual 3 < 3 IS a contradiction
    let x = mk_var("x");
    let lhs = mk_int_add(&x, &mk_int_ofnat(3));
    let rhs = mk_int_add(&x, &mk_int_ofnat(3));
    let proof = mk_var("h");

    assert!(
        try_close_int_additive_nf(CmpOp::Lt, &lhs, &rhs, &proof).is_some(),
        "3 < 3 is contradictory — must return Some for Lt"
    );
}
