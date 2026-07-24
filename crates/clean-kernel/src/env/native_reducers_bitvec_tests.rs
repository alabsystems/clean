// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BitVec and UInt/Int BitVec conversion native reducers.

use super::*;
use crate::env::Environment;
use crate::expr::{ExprKind, Literal};
use crate::name::Name;

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(expected), "expected {expected}");
    } else {
        panic!("expected Nat literal {expected}, got {:?}", result);
    }
}

// --- BitVec.ofNat tests ---

#[test]
fn test_bitvec_of_nat_8bit_in_range() {
    // BitVec.ofNat 8 42 = 42 (42 < 256)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &Expr::nat_lit(42)]),
        42,
    );
}

#[test]
fn test_bitvec_of_nat_8bit_wraps() {
    // BitVec.ofNat 8 256 = 0 (256 % 256 = 0)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &Expr::nat_lit(256)]),
        0,
    );
    // BitVec.ofNat 8 259 = 3 (259 % 256 = 3)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &Expr::nat_lit(259)]),
        3,
    );
}

#[test]
fn test_bitvec_of_nat_16bit_wraps() {
    // BitVec.ofNat 16 65536 = 0
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(16), &Expr::nat_lit(65536)]),
        0,
    );
}

#[test]
fn test_bitvec_of_nat_32bit_wraps() {
    // BitVec.ofNat 32 4294967296 = 0
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(32), &Expr::nat_lit(4294967296)]),
        0,
    );
}

#[test]
fn test_bitvec_of_nat_64bit_no_wrap() {
    // BitVec.ofNat 64 12345 = 12345 (width >= 64, no truncation for u64 values)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(64), &Expr::nat_lit(12345)]),
        12345,
    );
}

#[test]
fn test_bitvec_of_nat_zero_width() {
    // BitVec.ofNat 0 42 = 0 (2^0 = 1, 42 % 1 = 0)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(0), &Expr::nat_lit(42)]),
        0,
    );
}

#[test]
fn test_bitvec_of_nat_1bit() {
    // BitVec.ofNat 1 3 = 1 (3 % 2 = 1)
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(1), &Expr::nat_lit(3)]),
        1,
    );
}

#[test]
fn test_bitvec_of_nat_no_args() {
    assert!(reduce_bitvec_of_nat(&[]).is_none());
    assert!(reduce_bitvec_of_nat(&[&Expr::nat_lit(8)]).is_none());
}

#[test]
fn test_bitvec_of_nat_non_literal() {
    let var = Expr::const_(Name::from_string("x"), vec![]);
    assert!(reduce_bitvec_of_nat(&[&var, &Expr::nat_lit(42)]).is_none());
    assert!(reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &var]).is_none());
}

// --- BitVec.toNat tests ---

#[test]
fn test_bitvec_to_nat_identity() {
    assert_nat_result(reduce_bitvec_to_nat(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_bitvec_to_nat_with_width_arg() {
    // In practice, toNat has an implicit width arg before the value
    assert_nat_result(
        reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &Expr::nat_lit(200)]),
        200,
    );
}

#[test]
fn test_bitvec_to_nat_no_args() {
    assert!(reduce_bitvec_to_nat(&[]).is_none());
}

#[test]
fn test_bitvec_to_nat_non_literal() {
    let var = Expr::const_(Name::from_string("x"), vec![]);
    assert!(reduce_bitvec_to_nat(&[&var]).is_none());
}

// --- BitVec.toFin / BitVec.ofFin tests ---

#[test]
fn test_bitvec_to_fin_identity() {
    assert_nat_result(reduce_bitvec_to_fin(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_bitvec_of_fin_identity() {
    assert_nat_result(reduce_bitvec_of_fin(&[&Expr::nat_lit(42)]), 42);
}

// --- UInt toBitVec tests ---

#[test]
fn test_uint8_to_bitvec_identity() {
    assert_nat_result(reduce_uint8_to_bitvec(&[&Expr::nat_lit(200)]), 200);
}

#[test]
fn test_uint16_to_bitvec_identity() {
    assert_nat_result(reduce_uint16_to_bitvec(&[&Expr::nat_lit(50000)]), 50000);
}

#[test]
fn test_uint32_to_bitvec_identity() {
    assert_nat_result(
        reduce_uint32_to_bitvec(&[&Expr::nat_lit(3000000000)]),
        3000000000,
    );
}

#[test]
fn test_uint64_to_bitvec_identity() {
    assert_nat_result(
        reduce_uint64_to_bitvec(&[&Expr::nat_lit(u64::MAX)]),
        u64::MAX,
    );
}

#[test]
fn test_usize_to_bitvec_identity() {
    assert_nat_result(reduce_usize_to_bitvec(&[&Expr::nat_lit(999)]), 999);
}

#[test]
fn test_to_bitvec_no_args() {
    assert!(reduce_uint8_to_bitvec(&[]).is_none());
    assert!(reduce_uint16_to_bitvec(&[]).is_none());
    assert!(reduce_uint32_to_bitvec(&[]).is_none());
    assert!(reduce_uint64_to_bitvec(&[]).is_none());
    assert!(reduce_usize_to_bitvec(&[]).is_none());
}

#[test]
fn test_to_bitvec_non_literal() {
    let var = Expr::const_(Name::from_string("x"), vec![]);
    assert!(reduce_uint8_to_bitvec(&[&var]).is_none());
}

// --- UInt ofBitVec tests ---

#[test]
fn test_uint8_of_bitvec_identity() {
    assert_nat_result(reduce_uint8_of_bitvec(&[&Expr::nat_lit(200)]), 200);
}

#[test]
fn test_uint16_of_bitvec_identity() {
    assert_nat_result(reduce_uint16_of_bitvec(&[&Expr::nat_lit(50000)]), 50000);
}

#[test]
fn test_uint32_of_bitvec_identity() {
    assert_nat_result(
        reduce_uint32_of_bitvec(&[&Expr::nat_lit(3000000000)]),
        3000000000,
    );
}

#[test]
fn test_uint64_of_bitvec_identity() {
    assert_nat_result(
        reduce_uint64_of_bitvec(&[&Expr::nat_lit(u64::MAX)]),
        u64::MAX,
    );
}

#[test]
fn test_usize_of_bitvec_identity() {
    assert_nat_result(reduce_usize_of_bitvec(&[&Expr::nat_lit(999)]), 999);
}

// --- Signed integer toUInt/ofUInt tests ---

#[test]
fn test_int8_to_uint8_identity() {
    assert_nat_result(reduce_int8_to_uint8(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_int16_to_uint16_identity() {
    assert_nat_result(reduce_int16_to_uint16(&[&Expr::nat_lit(1000)]), 1000);
}

#[test]
fn test_int32_to_uint32_identity() {
    assert_nat_result(reduce_int32_to_uint32(&[&Expr::nat_lit(100000)]), 100000);
}

#[test]
fn test_int64_to_uint64_identity() {
    assert_nat_result(reduce_int64_to_uint64(&[&Expr::nat_lit(999999)]), 999999);
}

#[test]
fn test_isize_to_usize_identity() {
    assert_nat_result(reduce_isize_to_usize(&[&Expr::nat_lit(123)]), 123);
}

#[test]
fn test_int8_of_uint8_identity() {
    assert_nat_result(reduce_int8_of_uint8(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_int16_of_uint16_identity() {
    assert_nat_result(reduce_int16_of_uint16(&[&Expr::nat_lit(1000)]), 1000);
}

#[test]
fn test_int32_of_uint32_identity() {
    assert_nat_result(reduce_int32_of_uint32(&[&Expr::nat_lit(100000)]), 100000);
}

#[test]
fn test_int64_of_uint64_identity() {
    assert_nat_result(reduce_int64_of_uint64(&[&Expr::nat_lit(999999)]), 999999);
}

#[test]
fn test_isize_of_usize_identity() {
    assert_nat_result(reduce_isize_of_usize(&[&Expr::nat_lit(123)]), 123);
}

// --- Signed integer toBitVec tests ---

#[test]
fn test_int8_to_bitvec_identity() {
    assert_nat_result(reduce_int8_to_bitvec(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_int16_to_bitvec_identity() {
    assert_nat_result(reduce_int16_to_bitvec(&[&Expr::nat_lit(1000)]), 1000);
}

#[test]
fn test_int32_to_bitvec_identity() {
    assert_nat_result(reduce_int32_to_bitvec(&[&Expr::nat_lit(100000)]), 100000);
}

#[test]
fn test_int64_to_bitvec_identity() {
    assert_nat_result(reduce_int64_to_bitvec(&[&Expr::nat_lit(999999)]), 999999);
}

#[test]
fn test_isize_to_bitvec_identity() {
    assert_nat_result(reduce_isize_to_bitvec(&[&Expr::nat_lit(123)]), 123);
}

// --- Registration test ---

#[test]
fn test_all_bitvec_reducers_registered() {
    let mut env = Environment::new();
    env.init_bitvec_native_reducers();

    let expected_names = vec![
        // BitVec core
        &*names::BITVEC_OF_NAT,
        &*names::BITVEC_TO_NAT,
        &*names::BITVEC_TO_FIN,
        &*names::BITVEC_OF_FIN,
        // UInt toBitVec
        &*names::UINT8_TO_BITVEC,
        &*names::UINT16_TO_BITVEC,
        &*names::UINT32_TO_BITVEC,
        &*names::UINT64_TO_BITVEC,
        &*names::USIZE_TO_BITVEC,
        // UInt ofBitVec
        &*names::UINT8_OF_BITVEC,
        &*names::UINT16_OF_BITVEC,
        &*names::UINT32_OF_BITVEC,
        &*names::UINT64_OF_BITVEC,
        &*names::USIZE_OF_BITVEC,
        // Signed toUInt/ofUInt
        &*names::INT8_TO_UINT8,
        &*names::INT16_TO_UINT16,
        &*names::INT32_TO_UINT32,
        &*names::INT64_TO_UINT64,
        &*names::ISIZE_TO_USIZE,
        &*names::INT8_OF_UINT8,
        &*names::INT16_OF_UINT16,
        &*names::INT32_OF_UINT32,
        &*names::INT64_OF_UINT64,
        &*names::ISIZE_OF_USIZE,
        // Signed toBitVec
        &*names::INT8_TO_BITVEC,
        &*names::INT16_TO_BITVEC,
        &*names::INT32_TO_BITVEC,
        &*names::INT64_TO_BITVEC,
        &*names::ISIZE_TO_BITVEC,
    ];
    for name in expected_names {
        assert!(
            env.get_native_reducer(name).is_some(),
            "expected reducer {} to be registered",
            name
        );
    }
}

// --- End-to-end reduce_native tests ---

#[test]
fn test_reduce_native_fires_for_bitvec_of_nat() {
    let mut env = Environment::new();
    env.init_bitvec_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(names::BITVEC_OF_NAT.clone(), vec![]),
            Expr::nat_lit(8),
        ),
        Expr::nat_lit(300),
    );
    let result = tc.reduce_native_for_test(&expr);
    assert_nat_result(result, 44); // 300 % 256 = 44
}

#[test]
fn test_reduce_native_fires_for_uint8_to_bitvec() {
    let mut env = Environment::new();
    env.init_bitvec_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(names::UINT8_TO_BITVEC.clone(), vec![]),
        Expr::nat_lit(42),
    );
    let result = tc.reduce_native_for_test(&expr);
    assert_nat_result(result, 42);
}

#[test]
fn test_reduce_native_fires_for_uint32_of_bitvec() {
    let mut env = Environment::new();
    env.init_bitvec_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(names::UINT32_OF_BITVEC.clone(), vec![]),
        Expr::nat_lit(1000000),
    );
    let result = tc.reduce_native_for_test(&expr);
    assert_nat_result(result, 1000000);
}
