// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edge case tests for Int native reducers.
//! Tests overflow, division/modulo semantics, negation, and comparison edge cases.

use super::*;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

const I64_MAX_U64: u64 = i64::MAX as u64;
const NEG_MAX_SUCC: u64 = I64_MAX_U64 - 1;

fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(names::INT_OF_NAT.clone(), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(names::INT_NEG_SUCC.clone(), vec![]),
        Expr::nat_lit(n),
    )
}

fn is_bool_true(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels)
        if levels.is_empty() && *name == Name::from_string("Bool.true"))
}

fn is_bool_false(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels)
        if levels.is_empty() && *name == Name::from_string("Bool.false"))
}

fn max_int() -> Expr {
    int_of_nat(I64_MAX_U64)
}

fn neg_max_int() -> Expr {
    int_neg_succ(NEG_MAX_SUCC)
}

fn unrepresentable_min_int() -> Expr {
    int_neg_succ(I64_MAX_U64)
}

fn assert_int_result(result: Option<Expr>, expected: i64) {
    let result = result.expect("expected reducer to produce an Int expression");
    assert_eq!(get_int_val(&result), Some(i128::from(expected)));
}

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    assert_eq!(get_nat_val(&result), Some(expected));
}

fn assert_bool_result(result: Option<Expr>, expected: bool) {
    let result = result.expect("expected reducer to produce a Bool constructor");
    if expected {
        assert!(
            is_bool_true(&result),
            "expected Bool.true, got {:?}",
            result
        );
    } else {
        assert!(
            is_bool_false(&result),
            "expected Bool.false, got {:?}",
            result
        );
    }
}

fn assert_decidable_result(result: Option<Expr>, expected_true: bool) {
    let result = result.expect("expected reducer to produce a Decidable constructor");
    let head = result.get_app_fn();
    let expected_name = if expected_true {
        &*names::DECIDABLE_IS_TRUE
    } else {
        &*names::DECIDABLE_IS_FALSE
    };
    match head.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => assert_eq!(name, expected_name),
        _ => panic!("expected {:?}, got {:?}", expected_name, head),
    }
}

fn binary_reducers() -> [NativeReducerFn; 9] {
    [
        reduce_int_add,
        reduce_int_sub,
        reduce_int_mul,
        reduce_int_div,
        reduce_int_mod,
        reduce_int_beq,
        reduce_int_blt,
        reduce_int_ble,
        reduce_int_dec_eq,
    ]
}

fn unary_reducers() -> [NativeReducerFn; 3] {
    [reduce_int_neg, reduce_int_nat_abs, reduce_int_to_nat]
}

#[test]
fn test_get_int_val_of_nat() {
    assert_eq!(get_int_val(&int_of_nat(42)), Some(42));
}

#[test]
fn test_get_int_val_neg_succ() {
    assert_eq!(get_int_val(&int_neg_succ(0)), Some(-1));
    assert_eq!(get_int_val(&int_neg_succ(4)), Some(-5));
}

#[test]
fn test_get_int_val_bare_nat_literal() {
    assert_eq!(get_int_val(&Expr::nat_lit(17)), Some(17));
}

#[test]
fn test_get_int_val_non_app_non_lit_is_none() {
    let e = Expr::const_(Name::from_string("x"), vec![]);
    assert_eq!(get_int_val(&e), None);
}

#[test]
fn test_get_int_val_of_nat_with_levels_is_none() {
    let e = Expr::app(
        Expr::const_(names::INT_OF_NAT.clone(), vec![Level::zero()]),
        Expr::nat_lit(3),
    );
    assert_eq!(get_int_val(&e), None);
}

#[test]
fn test_get_int_val_neg_succ_with_levels_is_none() {
    let e = Expr::app(
        Expr::const_(names::INT_NEG_SUCC.clone(), vec![Level::zero()]),
        Expr::nat_lit(3),
    );
    assert_eq!(get_int_val(&e), None);
}

#[test]
fn test_get_int_val_of_nat_above_i64_max_is_representable() {
    // Trust (i128 widening): `ofNat` literals above i64::MAX — e.g. u32::MAX and
    // values up to u64::MAX — are now read, since the reducer carries i128.
    let v = I64_MAX_U64.saturating_add(1);
    assert_eq!(get_int_val(&int_of_nat(v)), Some(i128::from(v)));
    assert_eq!(
        get_int_val(&int_of_nat(u64::MAX)),
        Some(i128::from(u64::MAX))
    );
}

#[test]
fn test_get_int_val_neg_succ_i64_max_represents_i64_min() {
    // negSucc(i64::MAX) = -(i64::MAX + 1) = i64::MIN, which is representable
    assert_eq!(
        get_int_val(&unrepresentable_min_int()),
        Some(i128::from(i64::MIN))
    );
}

#[test]
fn test_get_int_val_neg_succ_u64_max_represents_neg_2_pow_64() {
    // Trust (i128 widening): negSucc(u64::MAX) = -(u64::MAX + 1) = -(2^64), now read.
    assert_eq!(
        get_int_val(&int_neg_succ(u64::MAX)),
        Some(-(i128::from(u64::MAX) + 1))
    );
}

#[test]
fn test_mk_int_roundtrip_core_values() {
    for v in [0i128, 1, -1, 42, -42] {
        assert_eq!(get_int_val(&mk_int(v).expect("representable")), Some(v));
    }
}

#[test]
fn test_mk_int_roundtrip_extremes() {
    // Round-trips across the FULL i128 range now reachable (the arbitrary-precision
    // `nat_lit_u128` encoding lifted the former `u64` magnitude cap), including the
    // 2^64 / 2^127 boundaries that overflow-check thresholds (`u64::MAX`, `i128::MIN`,
    // `i128::MAX`) live at.
    for v in [
        i128::from(i64::MAX),
        -i128::from(i64::MAX),
        i128::from(u64::MAX),
        i128::from(u64::MAX) + 1, // 2^64 — previously declined
        i128::MAX,
        i128::MIN,
    ] {
        assert_eq!(get_int_val(&mk_int(v).expect("representable")), Some(v));
    }
}

/// Extract the non-negative `BigNat` magnitude of an `Int.ofNat <lit>` result.
fn int_ofnat_mag(e: &Expr) -> Option<crate::expr::BigNat> {
    if let ExprKind::App(f, arg) = e.kind() {
        if let (ExprKind::Const(name, lv), ExprKind::Lit(Literal::Nat(n))) = (f.kind(), arg.kind())
        {
            if lv.is_empty() && *name == *names::INT_OF_NAT {
                return Some(n.clone());
            }
        }
    }
    None
}

#[test]
fn test_int_add_arbitrary_precision_beyond_u64() {
    use crate::expr::BigNat;
    // ARBITRARY PRECISION (was: i128 declined past u64). u64::MAX + 1 = 2^64
    // now reduces to the exact `Int.ofNat 2^64` rather than declining.
    let a = int_of_nat(u64::MAX);
    let b = int_of_nat(1);
    let r = reduce_int_add(&[&a, &b]).expect("BigInt add must reduce");
    let two_pow_64 = BigNat::Small(1).checked_shl_big(64);
    assert_eq!(int_ofnat_mag(&r), Some(two_pow_64), "u64::MAX + 1 = 2^64");
}

#[test]
fn test_int_add_negative_produces_i64_min() {
    // -i64::MAX + (-1) = i64::MIN, which is representable
    let a = neg_max_int();
    let b = int_neg_succ(0);
    assert_int_result(reduce_int_add(&[&a, &b]), i64::MIN);
}

#[test]
fn test_int_add_zero_identity() {
    let zero = int_of_nat(0);
    let pos = int_of_nat(9);
    let neg = int_neg_succ(4);
    assert_int_result(reduce_int_add(&[&zero, &pos]), 9);
    assert_int_result(reduce_int_add(&[&neg, &zero]), -5);
    assert_int_result(reduce_int_add(&[&zero, &zero]), 0);
}

#[test]
fn test_int_add_mixed_sign_cancellation() {
    let a = max_int();
    let b = neg_max_int();
    let c = int_of_nat(10);
    let d = int_neg_succ(4);
    assert_int_result(reduce_int_add(&[&a, &b]), 0);
    assert_int_result(reduce_int_add(&[&c, &d]), 5);
}

#[test]
fn test_int_sub_zero_minus_i64_max() {
    let zero = int_of_nat(0);
    let max = max_int();
    assert_int_result(reduce_int_sub(&[&zero, &max]), -i64::MAX);
}

#[test]
fn test_int_sub_arbitrary_precision_beyond_u64() {
    use crate::expr::BigNat;
    // u64::MAX − (−1) = 2^64 now reduces (was: i128 declined past u64).
    let a = int_of_nat(u64::MAX);
    let b = int_neg_succ(0);
    let r = reduce_int_sub(&[&a, &b]).expect("BigInt sub must reduce");
    let two_pow_64 = BigNat::Small(1).checked_shl_big(64);
    assert_eq!(
        int_ofnat_mag(&r),
        Some(two_pow_64),
        "u64::MAX − (−1) = 2^64"
    );
}

#[test]
fn test_int_sub_negative_minus_positive_produces_i64_min() {
    // -i64::MAX - 1 = i64::MIN, which is representable
    let a = neg_max_int();
    let b = int_of_nat(1);
    assert_int_result(reduce_int_sub(&[&a, &b]), i64::MIN);
}

#[test]
fn test_int_sub_self_and_zero_are_zero() {
    let a = int_neg_succ(6);
    let zero = int_of_nat(0);
    assert_int_result(reduce_int_sub(&[&a, &a]), 0);
    assert_int_result(reduce_int_sub(&[&zero, &zero]), 0);
}

#[test]
fn test_int_sub_accepts_bare_nat_literal_operand() {
    let a = Expr::nat_lit(9);
    let b = int_of_nat(4);
    assert_int_result(reduce_int_sub(&[&a, &b]), 5);
}

#[test]
fn test_int_mul_arbitrary_precision_beyond_u64() {
    use crate::expr::BigNat;
    // 2^33 · 2^33 = 2^66 now reduces (was: i128 declined past u64).
    let a = int_of_nat(1 << 33);
    let b = int_of_nat(1 << 33);
    let r = reduce_int_mul(&[&a, &b]).expect("BigInt mul must reduce");
    let two_pow_66 = BigNat::Small(1).checked_shl_big(66);
    assert_eq!(int_ofnat_mag(&r), Some(two_pow_66), "2^33 · 2^33 = 2^66");
}

#[test]
fn test_int_mul_negative_arbitrary_precision_beyond_u64() {
    use crate::expr::BigNat;
    // −(2^33) · 2^33 = −(2^66) now reduces to `Int.negSucc (2^66 − 1)`.
    let a = int_neg_succ((1 << 33) - 1); // = −(2^33)
    let b = int_of_nat(1 << 33);
    let r = reduce_int_mul(&[&a, &b]).expect("BigInt mul must reduce");
    // negSucc m = −(m+1); here −(2^66) so m = 2^66 − 1.
    let expected_m = BigNat::Small(1).checked_shl_big(66).pred().unwrap();
    let got = if let ExprKind::App(f, arg) = r.kind() {
        match (f.kind(), arg.kind()) {
            (ExprKind::Const(name, lv), ExprKind::Lit(Literal::Nat(n)))
                if lv.is_empty() && *name == *names::INT_NEG_SUCC =>
            {
                Some(n.clone())
            }
            _ => None,
        }
    } else {
        None
    };
    assert_eq!(got, Some(expected_m), "−(2^33)·2^33 = negSucc (2^66 − 1)");
}

#[test]
fn test_int_mul_i64_min_boundary_produces_i64_min() {
    // -(2^62) * 2 = -2^63 = i64::MIN, which is representable
    let a = int_neg_succ(4_611_686_018_427_387_903);
    let b = int_of_nat(2);
    assert_int_result(reduce_int_mul(&[&a, &b]), i64::MIN);
}

#[test]
fn test_int_mul_zero_annihilator() {
    let zero = int_of_nat(0);
    let pos = int_of_nat(13);
    let neg = int_neg_succ(2);
    assert_int_result(reduce_int_mul(&[&zero, &pos]), 0);
    assert_int_result(reduce_int_mul(&[&neg, &zero]), 0);
}

#[test]
fn test_int_mul_one_identity() {
    let one = int_of_nat(1);
    let pos = int_of_nat(13);
    let neg = int_neg_succ(2);
    assert_int_result(reduce_int_mul(&[&one, &neg]), -3);
    assert_int_result(reduce_int_mul(&[&pos, &one]), 13);
}

#[test]
fn test_int_mul_negative_sign_cases() {
    let neg_one = int_neg_succ(0);
    let max = max_int();
    let neg_three = int_neg_succ(2);
    let neg_four = int_neg_succ(3);
    assert_int_result(reduce_int_mul(&[&neg_one, &max]), -i64::MAX);
    assert_int_result(reduce_int_mul(&[&neg_three, &neg_four]), 12);
}

#[test]
fn test_int_div_truncates_toward_zero_negative_positive() {
    let a = int_neg_succ(6);
    let b = int_of_nat(2);
    assert_int_result(reduce_int_div(&[&a, &b]), -3);
}

#[test]
fn test_int_div_truncates_toward_zero_positive_negative() {
    let a = int_of_nat(7);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_div(&[&a, &b]), -3);
}

#[test]
fn test_int_div_truncates_toward_zero_negative_negative() {
    let a = int_neg_succ(6);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_div(&[&a, &b]), 3);
}

#[test]
fn test_int_div_by_zero_returns_zero() {
    let a = int_of_nat(5);
    let b = int_of_nat(0);
    assert_int_result(reduce_int_div(&[&a, &b]), 0);
}

#[test]
fn test_int_div_zero_dividend_returns_zero() {
    let zero = int_of_nat(0);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_div(&[&zero, &b]), 0);
}

#[test]
fn test_int_div_identity_cases() {
    let pos = int_of_nat(9);
    let neg = int_neg_succ(6);
    let one = int_of_nat(1);
    let neg_one = int_neg_succ(0);
    assert_int_result(reduce_int_div(&[&pos, &one]), 9);
    assert_int_result(reduce_int_div(&[&neg, &one]), -7);
    assert_int_result(reduce_int_div(&[&pos, &neg_one]), -9);
}

#[test]
fn test_int_mod_t_remainder_negative_positive() {
    let a = int_neg_succ(6);
    let b = int_of_nat(2);
    assert_int_result(reduce_int_mod(&[&a, &b]), -1);
}

#[test]
fn test_int_mod_t_remainder_positive_negative() {
    let a = int_of_nat(7);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_mod(&[&a, &b]), 1);
}

#[test]
fn test_int_mod_t_remainder_negative_negative() {
    let a = int_neg_succ(6);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_mod(&[&a, &b]), -1);
}

#[test]
fn test_int_mod_by_zero_returns_dividend() {
    let pos = int_of_nat(7);
    let neg = int_neg_succ(6);
    let zero = int_of_nat(0);
    assert_int_result(reduce_int_mod(&[&pos, &zero]), 7);
    assert_int_result(reduce_int_mod(&[&neg, &zero]), -7);
}

#[test]
fn test_int_mod_zero_dividend_returns_zero() {
    let zero = int_of_nat(0);
    let b = int_neg_succ(1);
    assert_int_result(reduce_int_mod(&[&zero, &b]), 0);
}

#[test]
fn test_int_mod_unit_divisors_return_zero() {
    let a = int_of_nat(7);
    let one = int_of_nat(1);
    let neg_one = int_neg_succ(0);
    assert_int_result(reduce_int_mod(&[&a, &one]), 0);
    assert_int_result(reduce_int_mod(&[&a, &neg_one]), 0);
}

#[test]
fn test_int_neg_edge_cases() {
    let zero = int_of_nat(0);
    let neg_one = int_neg_succ(0);
    let max = max_int();
    let neg_max = neg_max_int();
    assert_int_result(reduce_int_neg(&[&zero]), 0);
    assert_int_result(reduce_int_neg(&[&neg_one]), 1);
    assert_int_result(reduce_int_neg(&[&max]), -i64::MAX);
    assert_int_result(reduce_int_neg(&[&neg_max]), i64::MAX);
}

#[test]
fn test_int_neg_unrepresentable_boundary_returns_none() {
    // Arbitrary-magnitude read + i128 result: negating i64::MIN (= 2^63) and even
    // -(2^64) now succeeds. The ONLY decline boundary left is i128::MIN itself, whose
    // negation (2^127) is not representable in the i128 result.
    assert_eq!(
        get_int_val(&reduce_int_neg(&[&unrepresentable_min_int()]).expect("representable")),
        Some(-(i128::from(i64::MIN))),
    );
    // -(2^64) now negates to 2^64 (was declined under the u64 cap).
    let neg_two_pow_64 = int_neg_succ(u64::MAX);
    assert_eq!(
        get_int_val(&reduce_int_neg(&[&neg_two_pow_64]).expect("representable")),
        Some(i128::from(u64::MAX) + 1),
    );
    // i128::MIN: -(i128::MIN) = 2^127 overflows i128, so the reducer declines (sound).
    let min = mk_int(i128::MIN).expect("i128::MIN is representable as negSucc(2^127-1)");
    assert!(reduce_int_neg(&[&min]).is_none());
}

#[test]
fn test_int_nat_abs_edge_cases() {
    let zero = int_of_nat(0);
    let neg_one = int_neg_succ(0);
    let max = max_int();
    let neg_max = neg_max_int();
    assert_nat_result(reduce_int_nat_abs(&[&zero]), 0);
    assert_nat_result(reduce_int_nat_abs(&[&neg_one]), 1);
    assert_nat_result(reduce_int_nat_abs(&[&max]), I64_MAX_U64);
    assert_nat_result(reduce_int_nat_abs(&[&neg_max]), I64_MAX_U64);
}

#[test]
fn test_int_to_nat_edge_cases() {
    let neg = int_neg_succ(0);
    let zero = int_of_nat(0);
    let pos = int_of_nat(7);
    let max = max_int();
    assert_nat_result(reduce_int_to_nat(&[&neg]), 0);
    assert_nat_result(reduce_int_to_nat(&[&zero]), 0);
    assert_nat_result(reduce_int_to_nat(&[&pos]), 7);
    assert_nat_result(reduce_int_to_nat(&[&max]), I64_MAX_U64);
}

#[test]
fn test_int_beq_edge_cases() {
    let zero = int_of_nat(0);
    let neg_one = int_neg_succ(0);
    let neg_five_a = int_neg_succ(4);
    let neg_five_b = int_neg_succ(4);
    let bare = Expr::nat_lit(11);
    let of_nat = int_of_nat(11);
    assert_bool_result(reduce_int_beq(&[&zero, &neg_one]), false);
    assert_bool_result(reduce_int_beq(&[&neg_five_a, &neg_five_b]), true);
    assert_bool_result(reduce_int_beq(&[&bare, &of_nat]), true);
}

#[test]
fn test_int_blt_edge_cases() {
    let neg_one = int_neg_succ(0);
    let zero = int_of_nat(0);
    let max = max_int();
    let neg_max = neg_max_int();
    assert_bool_result(reduce_int_blt(&[&neg_one, &zero]), true);
    assert_bool_result(reduce_int_blt(&[&zero, &zero]), false);
    assert_bool_result(reduce_int_blt(&[&max, &neg_one]), false);
    assert_bool_result(reduce_int_blt(&[&neg_max, &max]), true);
}

#[test]
fn test_int_ble_edge_cases() {
    let neg_one_a = int_neg_succ(0);
    let neg_one_b = int_neg_succ(0);
    let zero = int_of_nat(0);
    let max = max_int();
    let neg_max = neg_max_int();
    assert_bool_result(reduce_int_ble(&[&neg_one_a, &neg_one_b]), true);
    assert_bool_result(reduce_int_ble(&[&zero, &zero]), true);
    assert_bool_result(reduce_int_ble(&[&max, &neg_one_a]), false);
    assert_bool_result(reduce_int_ble(&[&neg_max, &max]), true);
}

#[test]
fn test_int_dec_eq_edge_cases() {
    let pos_a = int_of_nat(3);
    let pos_b = int_of_nat(3);
    let neg_a = int_neg_succ(4);
    let neg_b = int_neg_succ(4);
    let other = int_of_nat(4);
    assert_decidable_result(reduce_int_dec_eq(&[&pos_a, &pos_b]), true);
    assert_decidable_result(reduce_int_dec_eq(&[&neg_a, &neg_b]), true);
    assert_decidable_result(reduce_int_dec_eq(&[&pos_a, &other]), false);
}

#[test]
fn test_int_binary_reducers_reject_too_few_args() {
    let a = int_of_nat(3);
    for reducer in binary_reducers() {
        assert!(reducer(&[]).is_none());
        assert!(reducer(&[&a]).is_none());
    }
}

#[test]
fn test_int_unary_reducers_reject_too_few_args() {
    for reducer in unary_reducers() {
        assert!(reducer(&[]).is_none());
    }
}

#[test]
fn test_int_reducers_reject_non_int_inputs() {
    let bad = Expr::const_(Name::from_string("x"), vec![]);
    let good = int_of_nat(1);
    for reducer in binary_reducers() {
        assert!(reducer(&[&bad, &good]).is_none());
        assert!(reducer(&[&good, &bad]).is_none());
    }
    for reducer in unary_reducers() {
        assert!(reducer(&[&bad]).is_none());
    }
}
