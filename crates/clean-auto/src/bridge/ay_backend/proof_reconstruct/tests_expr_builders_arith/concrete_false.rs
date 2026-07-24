// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    expr_contains_const, mk_int_concrete_false, mk_int_negsucc_expr, mk_int_ofnat_expr,
    mk_lt_irrefl_false, mk_var_expr, CmpOp, Sort,
};
use proptest::prelude::*;

#[test]
fn test_mk_int_concrete_false_le_contains_nonneg_caseson() {
    let five = mk_int_ofnat_expr(5);
    let three = mk_int_ofnat_expr(3);
    let chain_proof = mk_var_expr("h_5_le_3");
    let result = mk_int_concrete_false(CmpOp::Le, &five, &three, &chain_proof);

    assert!(expr_contains_const(&result, "Int.NonNeg.casesOn"));
    assert!(expr_contains_const(&result, "Int.casesOn"));
    assert!(expr_contains_const(&result, "Int.sub"));
    assert!(expr_contains_const(&result, "True.intro"));
}

#[test]
fn test_mk_int_concrete_false_lt_contains_start_plus_one() {
    let five = mk_int_ofnat_expr(5);
    let chain_proof = mk_var_expr("h_5_lt_5");
    let result = mk_int_concrete_false(CmpOp::Lt, &five, &five, &chain_proof);

    assert!(expr_contains_const(&result, "Int.NonNeg.casesOn"));
    assert!(expr_contains_const(&result, "Int.add"));
    assert!(expr_contains_const(&result, "Nat.succ"));
}

#[test]
fn test_mk_int_concrete_false_le_nonneg_index_is_sub_end_start() {
    let start = mk_int_ofnat_expr(10);
    let end_ = mk_int_ofnat_expr(3);
    let h = mk_var_expr("h");
    let result = mk_int_concrete_false(CmpOp::Le, &start, &end_, &h);

    assert!(
        !expr_contains_const(&result, "Int.lt_irrefl"),
        "Le concrete false must NOT use lt_irrefl"
    );
}

#[test]
fn test_mk_int_concrete_false_negative_endpoints() {
    let neg1 = mk_int_negsucc_expr(0);
    let neg3 = mk_int_negsucc_expr(2);
    let h = mk_var_expr("h_neg1_le_neg3");
    let result = mk_int_concrete_false(CmpOp::Le, &neg1, &neg3, &h);

    assert!(expr_contains_const(&result, "Int.NonNeg.casesOn"));
    assert!(expr_contains_const(&result, "Int.negSucc"));
}

#[test]
fn test_mk_lt_irrefl_false_int_produces_irrefl() {
    let a = mk_var_expr("a");
    let chain_proof = mk_var_expr("h_a_lt_a");
    let result = mk_lt_irrefl_false(&Sort::Int, &a, &chain_proof)
        .expect("Int sort should produce lt_irrefl");
    assert!(expr_contains_const(&result, "Int.lt_irrefl"));
}

#[test]
fn test_mk_lt_irrefl_false_real_produces_irrefl() {
    let a = mk_var_expr("a");
    let chain_proof = mk_var_expr("h_a_lt_a");
    let result = mk_lt_irrefl_false(&Sort::Real, &a, &chain_proof)
        .expect("Real sort should produce lt_irrefl");
    assert!(expr_contains_const(&result, "Real.lt_irrefl"));
}

#[test]
fn test_mk_lt_irrefl_false_unsupported_sort_returns_none() {
    let a = mk_var_expr("a");
    let chain_proof = mk_var_expr("h");
    assert!(mk_lt_irrefl_false(&Sort::Bool, &a, &chain_proof).is_none());
    assert!(mk_lt_irrefl_false(&Sort::String, &a, &chain_proof).is_none());
}

proptest! {
    #[test]
    fn proptest_mk_int_concrete_false_le_structure(
        start in 1u64..1_000,
        gap in 1u64..100,
    ) {
        let end_val = start.saturating_sub(gap);
        if start <= end_val {
            return Ok(());
        }
        let start_expr = mk_int_ofnat_expr(start);
        let end_expr = mk_int_ofnat_expr(end_val);
        let h = mk_var_expr("h");
        let result = mk_int_concrete_false(CmpOp::Le, &start_expr, &end_expr, &h);
        prop_assert!(expr_contains_const(&result, "Int.NonNeg.casesOn"));
        prop_assert!(!expr_contains_const(&result, "Int.lt_irrefl"));
    }

    #[test]
    fn proptest_mk_int_concrete_false_lt_structure(n in 0u64..1_000) {
        let expr = mk_int_ofnat_expr(n);
        let h = mk_var_expr("h");
        let result = mk_int_concrete_false(CmpOp::Lt, &expr, &expr, &h);
        prop_assert!(expr_contains_const(&result, "Int.NonNeg.casesOn"));
        prop_assert!(expr_contains_const(&result, "Int.add"));
    }
}
