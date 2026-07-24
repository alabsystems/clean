// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    extract_concrete_int_from_expr, is_concrete_violation_by_expr, mk_int_negsucc_expr,
    mk_int_ofnat_expr, CmpOp, Expr, Name,
};
use proptest::prelude::*;

#[test]
fn test_extract_concrete_int_ofnat() {
    let expr = mk_int_ofnat_expr(5);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(5))
    );
}

#[test]
fn test_extract_concrete_int_ofnat_zero() {
    let expr = mk_int_ofnat_expr(0);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(0))
    );
}

#[test]
fn test_extract_concrete_int_negsucc() {
    let expr = mk_int_negsucc_expr(0);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(-1))
    );
    let expr = mk_int_negsucc_expr(2);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(-3))
    );
}

#[test]
fn test_extract_concrete_int_symbolic_returns_none() {
    let expr = Expr::const_(Name::from_string("testX"), vec![]);
    assert_eq!(extract_concrete_int_from_expr(&expr), None);
}

#[test]
fn test_is_concrete_violation_le_violated() {
    let five = mk_int_ofnat_expr(5);
    let three = mk_int_ofnat_expr(3);
    assert!(is_concrete_violation_by_expr(&five, &three, CmpOp::Le));
}

#[test]
fn test_is_concrete_violation_le_not_violated() {
    let three = mk_int_ofnat_expr(3);
    let five = mk_int_ofnat_expr(5);
    assert!(!is_concrete_violation_by_expr(&three, &five, CmpOp::Le));
}

#[test]
fn test_is_concrete_violation_le_equal() {
    let five = mk_int_ofnat_expr(5);
    assert!(!is_concrete_violation_by_expr(&five, &five, CmpOp::Le));
}

#[test]
fn test_is_concrete_violation_lt_equal() {
    let five = mk_int_ofnat_expr(5);
    assert!(is_concrete_violation_by_expr(&five, &five, CmpOp::Lt));
}

#[test]
fn test_is_concrete_violation_symbolic_returns_false() {
    let symbolic = Expr::const_(Name::from_string("testX"), vec![]);
    let five = mk_int_ofnat_expr(5);
    assert!(!is_concrete_violation_by_expr(&symbolic, &five, CmpOp::Le));
    assert!(!is_concrete_violation_by_expr(&five, &symbolic, CmpOp::Le));
}

#[test]
fn test_is_concrete_violation_negative_endpoints() {
    let neg1 = mk_int_negsucc_expr(0);
    let neg3 = mk_int_negsucc_expr(2);
    assert!(is_concrete_violation_by_expr(&neg1, &neg3, CmpOp::Le));
    assert!(!is_concrete_violation_by_expr(&neg3, &neg1, CmpOp::Le));
}

#[test]
fn test_negsucc_roundtrip_boundary_negone() {
    let expr = mk_int_negsucc_expr(0);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(-1)),
        "negSucc(0) must decode to -1"
    );
}

#[test]
fn test_negsucc_roundtrip_boundary_negtwo() {
    let expr = mk_int_negsucc_expr(1);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(-2)),
        "negSucc(1) must decode to -2"
    );
}

#[test]
fn test_negsucc_roundtrip_large_negative() {
    let expr = mk_int_negsucc_expr(999);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(num_bigint::BigInt::from(-1000)),
        "negSucc(999) must decode to -1000"
    );
}

#[test]
fn test_ofnat_roundtrip_boundary_zero_one() {
    for n in [0u64, 1] {
        let expr = mk_int_ofnat_expr(n);
        assert_eq!(
            extract_concrete_int_from_expr(&expr),
            Some(num_bigint::BigInt::from(n)),
            "ofNat({n}) must roundtrip to {n}"
        );
    }
}

#[test]
fn test_ofnat_roundtrip_large() {
    let expr = mk_int_ofnat_expr(u64::MAX);
    let expected = num_bigint::BigInt::from(u64::MAX);
    assert_eq!(
        extract_concrete_int_from_expr(&expr),
        Some(expected),
        "ofNat(u64::MAX) must roundtrip correctly"
    );
}

#[test]
fn test_negsucc_roundtrip_systematic() {
    for n in 0u64..100 {
        let expr = mk_int_negsucc_expr(n);
        let expected = num_bigint::BigInt::from(-(n as i64) - 1);
        assert_eq!(
            extract_concrete_int_from_expr(&expr),
            Some(expected),
            "negSucc({n}) must decode to -{}",
            n + 1
        );
    }
}

#[test]
fn test_concrete_violation_le_vs_lt_boundary_systematic() {
    for n in [0u64, 1, 2, 100, 1000] {
        let expr = mk_int_ofnat_expr(n);
        assert!(
            !is_concrete_violation_by_expr(&expr, &expr, CmpOp::Le),
            "Le at equality ({n} <= {n}) must NOT be violated"
        );
        assert!(
            is_concrete_violation_by_expr(&expr, &expr, CmpOp::Lt),
            "Lt at equality ({n} < {n}) must BE violated"
        );
    }
}

#[test]
fn test_concrete_violation_adjacent_values() {
    for n in [0u64, 1, 10, 99] {
        let a = mk_int_ofnat_expr(n + 1);
        let b = mk_int_ofnat_expr(n);
        assert!(
            is_concrete_violation_by_expr(&a, &b, CmpOp::Le),
            "{} <= {} must be violated",
            n + 1,
            n
        );
        assert!(
            is_concrete_violation_by_expr(&a, &b, CmpOp::Lt),
            "{} < {} must be violated",
            n + 1,
            n
        );
        assert!(
            !is_concrete_violation_by_expr(&b, &a, CmpOp::Le),
            "{n} <= {} must NOT be violated",
            n + 1
        );
        assert!(
            !is_concrete_violation_by_expr(&b, &a, CmpOp::Lt),
            "{n} < {} must NOT be violated",
            n + 1
        );
    }
}

proptest! {
    #[test]
    fn proptest_ofnat_roundtrip(n in any::<u64>()) {
        let expr = mk_int_ofnat_expr(n);
        let extracted = extract_concrete_int_from_expr(&expr);
        prop_assert_eq!(
            extracted,
            Some(num_bigint::BigInt::from(n)),
            "ofNat({}) must roundtrip to {}",
            n,
            n
        );
    }

    #[test]
    fn proptest_negsucc_roundtrip(n in any::<u64>()) {
        let expr = mk_int_negsucc_expr(n);
        let expected = -(num_bigint::BigInt::from(n) + num_bigint::BigInt::from(1u64));
        let extracted = extract_concrete_int_from_expr(&expr);
        prop_assert_eq!(
            extracted,
            Some(expected.clone()),
            "negSucc({}) must decode to {}",
            n,
            expected
        );
    }
}

proptest! {
    #[test]
    fn proptest_le_violation_nonneg(a in 0u64..10_000, b in 0u64..10_000) {
        let a_expr = mk_int_ofnat_expr(a);
        let b_expr = mk_int_ofnat_expr(b);
        let violated = is_concrete_violation_by_expr(&a_expr, &b_expr, CmpOp::Le);
        prop_assert_eq!(
            violated,
            a > b,
            "Le violation for {} <= {}: expected {}, got {}",
            a,
            b,
            a > b,
            violated
        );
    }

    #[test]
    fn proptest_lt_violation_nonneg(a in 0u64..10_000, b in 0u64..10_000) {
        let a_expr = mk_int_ofnat_expr(a);
        let b_expr = mk_int_ofnat_expr(b);
        let violated = is_concrete_violation_by_expr(&a_expr, &b_expr, CmpOp::Lt);
        prop_assert_eq!(
            violated,
            a >= b,
            "Lt violation for {} < {}: expected {}, got {}",
            a,
            b,
            a >= b,
            violated
        );
    }

    #[test]
    fn proptest_le_violation_negative(a in 0u64..5_000, b in 0u64..5_000) {
        let a_expr = mk_int_negsucc_expr(a);
        let b_expr = mk_int_negsucc_expr(b);
        let violated = is_concrete_violation_by_expr(&a_expr, &b_expr, CmpOp::Le);
        prop_assert_eq!(
            violated,
            a < b,
            "Le violation for negSucc({}) <= negSucc({}): expected {}, got {}",
            a,
            b,
            a < b,
            violated
        );
    }

    #[test]
    fn proptest_lt_violation_negative(a in 0u64..5_000, b in 0u64..5_000) {
        let a_expr = mk_int_negsucc_expr(a);
        let b_expr = mk_int_negsucc_expr(b);
        let violated = is_concrete_violation_by_expr(&a_expr, &b_expr, CmpOp::Lt);
        prop_assert_eq!(
            violated,
            a <= b,
            "Lt violation for negSucc({}) < negSucc({}): expected {}, got {}",
            a,
            b,
            a <= b,
            violated
        );
    }

    #[test]
    fn proptest_le_violation_cross_sign(a in 0u64..5_000, b in 0u64..5_000) {
        let pos_expr = mk_int_ofnat_expr(a);
        let neg_expr = mk_int_negsucc_expr(b);
        prop_assert!(
            is_concrete_violation_by_expr(&pos_expr, &neg_expr, CmpOp::Le),
            "ofNat({}) <= negSucc({}) must always be violated",
            a,
            b
        );
        prop_assert!(
            !is_concrete_violation_by_expr(&neg_expr, &pos_expr, CmpOp::Le),
            "negSucc({}) <= ofNat({}) must never be violated",
            b,
            a
        );
    }

    #[test]
    fn proptest_symbolic_never_violated(a in 0u64..1_000) {
        let concrete = mk_int_ofnat_expr(a);
        let symbolic = Expr::const_(Name::from_string("sym_x"), vec![]);
        prop_assert!(!is_concrete_violation_by_expr(&symbolic, &concrete, CmpOp::Le));
        prop_assert!(!is_concrete_violation_by_expr(&concrete, &symbolic, CmpOp::Le));
        prop_assert!(!is_concrete_violation_by_expr(&symbolic, &concrete, CmpOp::Lt));
        prop_assert!(!is_concrete_violation_by_expr(&concrete, &symbolic, CmpOp::Lt));
    }
}
