// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for signed fixed-width integer native reducers.

use super::*;
use crate::env::native_reducers_uint::get_nat_val;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;

fn is_bool_true(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels)
        if levels.is_empty() && *name == Name::from_string("Bool.true"))
}

fn is_bool_false(e: &Expr) -> bool {
    matches!(e.kind(), ExprKind::Const(name, levels)
        if levels.is_empty() && *name == Name::from_string("Bool.false"))
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn is_dec_is_true(e: &Expr) -> bool {
    // Peel *all* application layers: a sound `isTrue`/`isFalse` is fully applied
    // (`@Decidable.isFalse prop proof`), so a single-layer peel would miss it.
    matches!(e.get_app_fn().kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("Decidable.isTrue"))
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn is_dec_is_false(e: &Expr) -> bool {
    matches!(e.get_app_fn().kind(),
        ExprKind::Const(name, _) if *name == Name::from_string("Decidable.isFalse"))
}

/// Wrap a `Nat` literal as the concrete signed value `<T>.mk <nat>` — the
/// well-typed kernel form an `@Eq <T>` operand actually has.
fn imk(ty: &str, e: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(&format!("{ty}.mk")), vec![]),
        e.clone(),
    )
}

// --- Int8 tests ---

#[test]
fn test_int8_add_simple() {
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_int8_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(8));
}

#[test]
fn test_int8_add_wrapping() {
    // 200 + 100 = 300, mod 256 = 44
    let a = Expr::nat_lit(200);
    let b = Expr::nat_lit(100);
    let result = reduce_int8_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(44));
}

#[test]
fn test_int8_sub_wrapping() {
    // 3 - 5 = -2, mod 256 = 254
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_int8_sub(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(254));
}

#[test]
fn test_int8_mul_simple() {
    let a = Expr::nat_lit(6);
    let b = Expr::nat_lit(7);
    let result = reduce_int8_mul(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(42));
}

#[test]
fn test_int8_div_signed() {
    // -10 (= 246 unsigned) / 3 = -3 (= 253 unsigned)
    // Two's complement: 246 = -10, result -3 = 253
    let a = Expr::nat_lit(246); // -10 in Int8
    let b = Expr::nat_lit(3);
    let result = reduce_int8_div(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(253)); // -3 in Int8
}

#[test]
fn test_int8_div_by_zero() {
    let a = Expr::nat_lit(5);
    let b = Expr::nat_lit(0);
    let result = reduce_int8_div(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(0));
}

#[test]
fn test_int8_mod_signed() {
    // -5 (= 251 unsigned) % 2 = -1 (= 255 unsigned)
    let a = Expr::nat_lit(251); // -5 in Int8
    let b = Expr::nat_lit(2);
    let result = reduce_int8_mod(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(255)); // -1 in Int8
}

#[test]
fn test_int8_beq_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(42);
    let result = reduce_int8_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result));
}

#[test]
fn test_int8_beq_not_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(43);
    let result = reduce_int8_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_false(&result));
}

#[test]
fn test_int8_blt_signed() {
    // -1 (=255) < 0 in signed Int8 comparison
    let a = Expr::nat_lit(255); // -1 in Int8
    let b = Expr::nat_lit(0);
    let result = reduce_int8_blt(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result), "-1 < 0 should be true");

    // Reverse: 0 < -1 should be false
    let result = reduce_int8_blt(&[&b, &a]).expect("should reduce");
    assert!(is_bool_false(&result), "0 < -1 should be false");
}

#[test]
fn test_int8_ble_signed() {
    // -128 (=128) <= 127 in signed Int8
    let a = Expr::nat_lit(128); // -128 in Int8
    let b = Expr::nat_lit(127);
    let result = reduce_int8_ble(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result), "-128 <= 127 should be true");
}

#[test]
fn test_int8_dec_eq_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(42);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_int8_dec_eq(&[&imk("Int8", &a), &imk("Int8", &b)]).is_none(),
        "signed decEq declines — Int8 not registered"
    );
}

#[test]
fn test_int8_dec_eq_not_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(43);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_int8_dec_eq(&[&imk("Int8", &a), &imk("Int8", &b)]).is_none(),
        "signed decEq declines — Int8 not registered"
    );
}

// --- Int16 tests ---

#[test]
fn test_int16_add_wrapping() {
    let a = Expr::nat_lit(65535);
    let b = Expr::nat_lit(2);
    let result = reduce_int16_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(1));
}

#[test]
fn test_int16_sub_wrapping() {
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_int16_sub(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(65534));
}

#[test]
fn test_int16_mul_simple() {
    let a = Expr::nat_lit(123);
    let b = Expr::nat_lit(4);
    let result = reduce_int16_mul(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(492));
}

#[test]
fn test_int16_div_signed() {
    let neg10 = Expr::nat_lit(65526);
    let three = Expr::nat_lit(3);
    let result = reduce_int16_div(&[&neg10, &three]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(65533));
}

#[test]
fn test_int16_mod_signed() {
    let neg5 = Expr::nat_lit(65531);
    let two = Expr::nat_lit(2);
    let result = reduce_int16_mod(&[&neg5, &two]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(65535));
}

#[test]
fn test_int16_beq_equal() {
    let a = Expr::nat_lit(1024);
    let b = Expr::nat_lit(1024);
    let result = reduce_int16_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result));
}

#[test]
fn test_int16_blt_signed() {
    let neg1 = Expr::nat_lit(65535);
    let zero = Expr::nat_lit(0);
    let result = reduce_int16_blt(&[&neg1, &zero]).expect("should reduce");
    assert!(is_bool_true(&result), "-1 < 0 should be true in Int16");
}

#[test]
fn test_int16_ble_signed() {
    let min = Expr::nat_lit(32768);
    let max = Expr::nat_lit(32767);
    let result = reduce_int16_ble(&[&min, &max]).expect("should reduce");
    assert!(is_bool_true(&result), "-32768 <= 32767 should be true");
}

#[test]
fn test_int16_dec_eq_equal() {
    let a = Expr::nat_lit(2048);
    let b = Expr::nat_lit(2048);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_int16_dec_eq(&[&imk("Int16", &a), &imk("Int16", &b)]).is_none(),
        "signed decEq declines — Int16 not registered"
    );
}

#[test]
fn test_int16_dec_lt_true() {
    let neg1 = Expr::nat_lit(65535);
    let zero = Expr::nat_lit(0);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int16_dec_lt(&[&neg1, &zero]).is_none(),
        "reduce_int16_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_int16_dec_le_equal() {
    let a = Expr::nat_lit(2048);
    let b = Expr::nat_lit(2048);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int16_dec_le(&[&a, &b]).is_none(),
        "reduce_int16_dec_le declines (unproven signed order)"
    );
}

// --- Int32 tests ---

#[test]
fn test_int32_add_simple() {
    let a = Expr::nat_lit(100);
    let b = Expr::nat_lit(200);
    let result = reduce_int32_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(300));
}

#[test]
fn test_int32_sub_wrapping() {
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_int32_sub(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(4294967294));
}

#[test]
fn test_int32_mul_simple() {
    let a = Expr::nat_lit(12345);
    let b = Expr::nat_lit(17);
    let result = reduce_int32_mul(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(209865));
}

#[test]
fn test_int32_div_signed() {
    let neg10 = Expr::nat_lit(4294967286);
    let three = Expr::nat_lit(3);
    let result = reduce_int32_div(&[&neg10, &three]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(4294967293));
}

#[test]
fn test_int32_mod_signed() {
    let neg5 = Expr::nat_lit(4294967291);
    let two = Expr::nat_lit(2);
    let result = reduce_int32_mod(&[&neg5, &two]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(4294967295));
}

#[test]
fn test_int32_beq_equal() {
    let a = Expr::nat_lit(123456);
    let b = Expr::nat_lit(123456);
    let result = reduce_int32_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result));
}

#[test]
fn test_int32_blt_signed() {
    // -1 (= 2^32 - 1 = 4294967295) < 0 in signed Int32
    let a = Expr::nat_lit(4294967295); // -1 in Int32
    let b = Expr::nat_lit(0);
    let result = reduce_int32_blt(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result), "-1 < 0 should be true in Int32");
}

#[test]
fn test_int32_ble_signed() {
    let min = Expr::nat_lit(2147483648);
    let max = Expr::nat_lit(2147483647);
    let result = reduce_int32_ble(&[&min, &max]).expect("should reduce");
    assert!(is_bool_true(&result), "i32::MIN <= i32::MAX should be true");
}

#[test]
fn test_int32_dec_eq_equal() {
    let a = Expr::nat_lit(123456);
    let b = Expr::nat_lit(123456);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_int32_dec_eq(&[&imk("Int32", &a), &imk("Int32", &b)]).is_none(),
        "signed decEq declines — Int32 not registered"
    );
}

#[test]
fn test_int32_dec_lt_true() {
    let neg1 = Expr::nat_lit(4294967295);
    let zero = Expr::nat_lit(0);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int32_dec_lt(&[&neg1, &zero]).is_none(),
        "reduce_int32_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_int32_dec_le_equal() {
    let a = Expr::nat_lit(123456);
    let b = Expr::nat_lit(123456);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int32_dec_le(&[&a, &b]).is_none(),
        "reduce_int32_dec_le declines (unproven signed order)"
    );
}

// --- Int64 / ISize tests ---

#[test]
fn test_int64_add_wrapping() {
    let a = Expr::nat_lit(u64::MAX);
    let b = Expr::nat_lit(1);
    let result = reduce_int64_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(0));
}

#[test]
fn test_int64_sub_wrapping() {
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_int64_sub(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(u64::MAX - 1));
}

#[test]
fn test_int64_mul_simple() {
    let a = Expr::nat_lit(123_456_789);
    let b = Expr::nat_lit(17);
    let result = reduce_int64_mul(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(2_098_765_413));
}

#[test]
fn test_int64_mod_signed() {
    let neg5 = Expr::nat_lit((-5i64) as u64);
    let two = Expr::nat_lit(2);
    let result = reduce_int64_mod(&[&neg5, &two]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some((-1i64) as u64));
}

#[test]
fn test_int64_beq_equal() {
    let a = Expr::nat_lit(123_456_789);
    let b = Expr::nat_lit(123_456_789);
    let result = reduce_int64_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result));
}

#[test]
fn test_int64_blt_signed() {
    // u64::MAX is -1 in signed i64
    let a = Expr::nat_lit(u64::MAX);
    let b = Expr::nat_lit(0);
    let result = reduce_int64_blt(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result), "-1 < 0 should be true in Int64");
}

#[test]
fn test_int64_ble_signed() {
    let min = Expr::nat_lit(i64::MIN as u64);
    let max = Expr::nat_lit(i64::MAX as u64);
    let result = reduce_int64_ble(&[&min, &max]).expect("should reduce");
    assert!(is_bool_true(&result), "i64::MIN <= i64::MAX should be true");
}

#[test]
fn test_int64_div_signed() {
    // -10 (as u64) / 3 = -3 (as u64)
    let neg10 = (-10i64) as u64;
    let neg3 = (-3i64) as u64;
    let a = Expr::nat_lit(neg10);
    let b = Expr::nat_lit(3);
    let result = reduce_int64_div(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(neg3));
}

#[test]
fn test_int64_dec_eq_equal() {
    let a = Expr::nat_lit(123_456_789);
    let b = Expr::nat_lit(123_456_789);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_int64_dec_eq(&[&imk("Int64", &a), &imk("Int64", &b)]).is_none(),
        "signed decEq declines — Int64 not registered"
    );
}

#[test]
fn test_int64_dec_lt_true() {
    let neg1 = Expr::nat_lit(u64::MAX);
    let zero = Expr::nat_lit(0);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int64_dec_lt(&[&neg1, &zero]).is_none(),
        "reduce_int64_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_int64_dec_le_equal() {
    let a = Expr::nat_lit(123_456_789);
    let b = Expr::nat_lit(123_456_789);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int64_dec_le(&[&a, &b]).is_none(),
        "reduce_int64_dec_le declines (unproven signed order)"
    );
}

#[test]
fn test_isize_dec_eq_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(42);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_isize_dec_eq(&[&imk("ISize", &a), &imk("ISize", &b)]).is_none(),
        "signed decEq declines — ISize not registered"
    );
}

#[test]
fn test_isize_dec_eq_not_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(43);
    // Signed types are not registered in any Clean env, so their decEq declines
    // (see the reducer note); sound by omission, never an unverified term.
    assert!(
        reduce_isize_dec_eq(&[&imk("ISize", &a), &imk("ISize", &b)]).is_none(),
        "signed decEq declines — ISize not registered"
    );
}

#[test]
fn test_isize_add_wrapping() {
    let a = Expr::nat_lit(usize::MAX as u64);
    let b = Expr::nat_lit(1);
    let result = reduce_isize_add(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(0));
}

#[test]
fn test_isize_sub_wrapping() {
    let a = Expr::nat_lit(3);
    let b = Expr::nat_lit(5);
    let result = reduce_isize_sub(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some((usize::MAX - 1) as u64));
}

#[test]
fn test_isize_mul_simple() {
    let a = Expr::nat_lit(123_456);
    let b = Expr::nat_lit(17);
    let result = reduce_isize_mul(&[&a, &b]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some(2_098_752));
}

#[test]
fn test_isize_div_signed() {
    let neg10 = Expr::nat_lit((-10isize) as usize as u64);
    let three = Expr::nat_lit(3);
    let result = reduce_isize_div(&[&neg10, &three]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some((-3isize) as usize as u64));
}

#[test]
fn test_isize_mod_signed() {
    let neg5 = Expr::nat_lit((-5isize) as usize as u64);
    let two = Expr::nat_lit(2);
    let result = reduce_isize_mod(&[&neg5, &two]).expect("should reduce");
    assert_eq!(get_nat_val(&result), Some((-1isize) as usize as u64));
}

#[test]
fn test_isize_beq_equal() {
    let a = Expr::nat_lit(123_456);
    let b = Expr::nat_lit(123_456);
    let result = reduce_isize_beq(&[&a, &b]).expect("should reduce");
    assert!(is_bool_true(&result));
}

#[test]
fn test_isize_blt_signed() {
    let neg1 = Expr::nat_lit((-1isize) as usize as u64);
    let zero = Expr::nat_lit(0);
    let result = reduce_isize_blt(&[&neg1, &zero]).expect("should reduce");
    assert!(is_bool_true(&result), "-1 < 0 should be true in ISize");
}

#[test]
fn test_isize_ble_signed() {
    let min = Expr::nat_lit(isize::MIN as usize as u64);
    let max = Expr::nat_lit(isize::MAX as usize as u64);
    let result = reduce_isize_ble(&[&min, &max]).expect("should reduce");
    assert!(
        is_bool_true(&result),
        "isize::MIN <= isize::MAX should be true"
    );
}

#[test]
fn test_isize_dec_lt_true() {
    let neg1 = Expr::nat_lit((-1isize) as usize as u64);
    let zero = Expr::nat_lit(0);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_isize_dec_lt(&[&neg1, &zero]).is_none(),
        "reduce_isize_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_isize_dec_le_equal() {
    let a = Expr::nat_lit(123_456);
    let b = Expr::nat_lit(123_456);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_isize_dec_le(&[&a, &b]).is_none(),
        "reduce_isize_dec_le declines (unproven signed order)"
    );
}

// --- Edge cases ---

#[test]
fn test_sint_too_few_args() {
    let a = Expr::nat_lit(3);
    assert!(reduce_int8_add(&[&a]).is_none());
    assert!(reduce_int8_add(&[]).is_none());
    assert!(reduce_int8_dec_eq(&[&a]).is_none());
}

// --- Registration test ---

#[test]
fn test_sint_reducers_registered() {
    let mut env = Environment::new();
    env.init_sint_native_reducers();

    // Function-form names
    assert!(
        env.get_native_reducer(&names::INT8_DEC_EQ).is_some(),
        "Int8.decEq should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INT16_ADD).is_some(),
        "Int16.add should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INT32_BLT).is_some(),
        "Int32.blt should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INT64_DIV).is_some(),
        "Int64.div should be registered"
    );
    assert!(
        env.get_native_reducer(&names::ISIZE_DEC_EQ).is_some(),
        "ISize.decEq should be registered"
    );

    // Instance name aliases
    assert!(
        env.get_native_reducer(&names::INST_DEC_EQ_INT8).is_some(),
        "instDecidableEqInt8 should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DEC_EQ_INT16).is_some(),
        "instDecidableEqInt16 should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DEC_EQ_INT32).is_some(),
        "instDecidableEqInt32 should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DEC_EQ_INT64).is_some(),
        "instDecidableEqInt64 should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INST_DEC_EQ_ISIZE).is_some(),
        "instDecidableEqISize should be registered"
    );
}

#[test]
fn test_signed_int_decidable_eq_aliases_reduce() {
    let mut env = Environment::new();
    env.init_sint_native_reducers();

    let int8_alias = *env
        .get_native_reducer(&names::INST_DEC_EQ_INT8)
        .expect("instDecidableEqInt8 should be registered");
    let int16_alias = *env
        .get_native_reducer(&names::INST_DEC_EQ_INT16)
        .expect("instDecidableEqInt16 should be registered");
    let int32_alias = *env
        .get_native_reducer(&names::INST_DEC_EQ_INT32)
        .expect("instDecidableEqInt32 should be registered");
    let int64_alias = *env
        .get_native_reducer(&names::INST_DEC_EQ_INT64)
        .expect("instDecidableEqInt64 should be registered");
    let isize_alias = *env
        .get_native_reducer(&names::INST_DEC_EQ_ISIZE)
        .expect("instDecidableEqISize should be registered");

    // Operands are concrete signed values `<T>.mk <nat>` (the well-typed form).
    let n = Expr::nat_lit(37);
    for (alias, ty) in [
        (int8_alias, "Int8"),
        (int16_alias, "Int16"),
        (int32_alias, "Int32"),
        (int64_alias, "Int64"),
        (isize_alias, "ISize"),
    ] {
        let a = imk(ty, &n);
        let b = imk(ty, &n);
        assert!(
            alias(&[&a, &b]).is_none(),
            "instDecidableEq{ty} declines — signed type not registered"
        );
    }
}

// --- decLt / decLe tests ---

#[test]
fn test_int8_dec_lt_true() {
    let a = Expr::nat_lit(255);
    let b = Expr::nat_lit(0);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int8_dec_lt(&[&a, &b]).is_none(),
        "reduce_int8_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_int8_dec_lt_false() {
    let a = Expr::nat_lit(0);
    let b = Expr::nat_lit(255); // -1
                                // Signed two's-complement ordering now *declines* (sound: not backed by an
                                // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int8_dec_lt(&[&a, &b]).is_none(),
        "reduce_int8_dec_lt declines (unproven signed order)"
    );
}

#[test]
fn test_int8_dec_le_equal() {
    let a = Expr::nat_lit(42);
    let b = Expr::nat_lit(42);
    // Signed two's-complement ordering now *declines* (sound: not backed by an
    // in-kernel order proof) instead of emitting `Decidable sorryAx`.
    assert!(
        reduce_int8_dec_le(&[&a, &b]).is_none(),
        "reduce_int8_dec_le declines (unproven signed order)"
    );
}

#[test]
fn test_int32_dec_lt_registered() {
    let mut env = Environment::new();
    env.init_sint_native_reducers();
    assert!(
        env.get_native_reducer(&names::INT32_DEC_LT).is_some(),
        "Int32.decLt should be registered"
    );
    assert!(
        env.get_native_reducer(&names::INT32_DEC_LE).is_some(),
        "Int32.decLe should be registered"
    );
}

// --- to_signed helper tests ---

#[test]
fn test_to_signed_positive() {
    assert_eq!(to_signed(127, 8), 127);
    assert_eq!(to_signed(0, 8), 0);
    assert_eq!(to_signed(1, 8), 1);
}

#[test]
fn test_to_signed_negative() {
    assert_eq!(to_signed(255, 8), -1); // -1 in Int8
    assert_eq!(to_signed(128, 8), -128); // MIN in Int8
    assert_eq!(to_signed(246, 8), -10); // -10 in Int8
}

#[test]
fn test_to_signed_16bit() {
    assert_eq!(to_signed(65535, 16), -1); // -1 in Int16
    assert_eq!(to_signed(32768, 16), -32768); // MIN in Int16
}

#[test]
fn test_to_signed_64bit() {
    assert_eq!(to_signed(u64::MAX, 64), -1);
    assert_eq!(to_signed(1u64 << 63, 64), i64::MIN);
}

/// Signed `decEq` (`Int8`..`ISize`) **declines** for every input. The signed
/// types are not registered in any Clean environment (no `add_inductive`, no
/// `<T>.val : <T> → Nat` projection), so a wrapper disproof would emit
/// `<T>.val`-referencing output we cannot type-check here and that
/// `reduce_native` would trust without re-checking. Declining keeps the reducer
/// sound by omission. (Contrast `test_uint_dec_eq_is_sound`, where the UInt
/// types ARE in the prelude and the wrapper output is fully kernel-type-checked.)
#[test]
fn test_sint_dec_eq_declines() {
    let cases: [(NativeReducerFn, &str); 5] = [
        (reduce_int8_dec_eq, "Int8"),
        (reduce_int16_dec_eq, "Int16"),
        (reduce_int32_dec_eq, "Int32"),
        (reduce_int64_dec_eq, "Int64"),
        (reduce_isize_dec_eq, "ISize"),
    ];
    for (red, ty) in cases {
        for (x, y) in [(7u64, 7u64), (7, 8)] {
            let a = imk(ty, &Expr::nat_lit(x));
            let b = imk(ty, &Expr::nat_lit(y));
            assert!(
                red(&[&a, &b]).is_none(),
                "{ty}.decEq must decline (type not registered)"
            );
        }
    }
}
