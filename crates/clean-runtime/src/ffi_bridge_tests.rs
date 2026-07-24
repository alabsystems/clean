// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the FFI native function bridge.

use super::*;

// ---------------------------------------------------------------------------
// Registration and lookup
// ---------------------------------------------------------------------------

#[test]
fn test_ffi_bridge_new_has_builtins() {
    let bridge = FfiBridge::new();
    let names = bridge.registered_names();
    assert!(
        names.contains(&"String.append".to_owned()),
        "should have String.append"
    );
    assert!(
        names.contains(&"Array.mk".to_owned()),
        "should have Array.mk"
    );
    assert!(
        names.contains(&"Float.add".to_owned()),
        "should have Float.add"
    );
    assert!(
        names.contains(&"IO.println".to_owned()),
        "should have IO.println"
    );
}

#[test]
fn test_ffi_bridge_register_custom() {
    let mut bridge = FfiBridge::new();
    let func: NativeFn = Arc::new(|args: &[Value]| {
        if args.is_empty() {
            Ok(Value::Nat(999))
        } else {
            Ok(Value::Unit)
        }
    });
    bridge.register_native("Custom.fn", func);
    let result = bridge
        .call_native("Custom.fn", &[])
        .expect("custom fn should succeed");
    assert_eq!(result, Value::Nat(999));
}

#[test]
fn test_ffi_bridge_unknown_function_error() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Nonexistent.fn", &[])
        .expect_err("should fail on unknown");
    match err {
        FfiError::UnknownFunction { name } => assert_eq!(name, "Nonexistent.fn"),
        other => panic!("expected UnknownFunction, got {other:?}"),
    }
}

#[test]
fn test_ffi_bridge_registered_names_sorted() {
    let bridge = FfiBridge::new();
    let names = bridge.registered_names();
    let mut sorted = names.clone();
    sorted.sort_unstable();
    assert_eq!(names, sorted, "registered_names should be sorted");
}

// ---------------------------------------------------------------------------
// String operations
// ---------------------------------------------------------------------------

#[test]
fn test_string_append_basic() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "String.append",
            &[
                Value::String("hello".into()),
                Value::String(" world".into()),
            ],
        )
        .expect("append should succeed");
    assert_eq!(result, Value::String("hello world".into()));
}

#[test]
fn test_string_length_returns_byte_count() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("String.length", &[Value::String("hello".into())])
        .expect("length should succeed");
    assert_eq!(result, Value::Nat(5));
}

#[test]
fn test_string_push_appends_char() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "String.push",
            &[Value::String("hell".into()), Value::Nat(97)], // 'a'
        )
        .expect("push should succeed");
    assert_eq!(result, Value::String("hella".into()));
}

#[test]
fn test_string_mk_from_char_codes() {
    let bridge = FfiBridge::new();
    let codes = Value::Array(vec![Value::Nat(104), Value::Nat(105)]); // 'h', 'i'
    let result = bridge
        .call_native("String.mk", &[codes])
        .expect("mk should succeed");
    assert_eq!(result, Value::String("hi".into()));
}

// ---------------------------------------------------------------------------
// Array operations
// ---------------------------------------------------------------------------

#[test]
fn test_array_mk_creates_empty() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Array.mk", &[])
        .expect("mk should succeed");
    assert_eq!(result, Value::Array(vec![]));
}

#[test]
fn test_array_push_adds_element() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Array.push", &[Value::Array(vec![]), Value::Nat(42)])
        .expect("push should succeed");
    assert_eq!(result, Value::Array(vec![Value::Nat(42)]));
}

#[test]
fn test_array_get_valid_index() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let result = bridge
        .call_native("Array.get", &[arr, Value::Nat(0)])
        .expect("get should succeed");
    assert_eq!(result, Value::Nat(1));
}

#[test]
fn test_array_get_out_of_bounds() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::Nat(1)]);
    let err = bridge
        .call_native("Array.get", &[arr, Value::Nat(5)])
        .expect_err("out of bounds should fail");
    match err {
        FfiError::ExecutionFailed { function, message } => {
            assert_eq!(function, "Array.get");
            assert!(message.contains("out of bounds"), "message: {message}");
        }
        other => panic!("expected ExecutionFailed, got {other:?}"),
    }
}

#[test]
fn test_array_size_returns_count() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::Nat(10), Value::Nat(20)]);
    let result = bridge
        .call_native("Array.size", &[arr])
        .expect("size should succeed");
    assert_eq!(result, Value::Nat(2));
}

#[test]
fn test_array_set_replaces_element() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let result = bridge
        .call_native("Array.set", &[arr, Value::Nat(0), Value::Nat(99)])
        .expect("set should succeed");
    assert_eq!(result, Value::Array(vec![Value::Nat(99), Value::Nat(2)]));
}

// ---------------------------------------------------------------------------
// Float operations
// ---------------------------------------------------------------------------

#[test]
fn test_float_add_basic() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Float.add", &[Value::Float(1.5), Value::Float(2.5)])
        .expect("add should succeed");
    assert_eq!(result, Value::Float(4.0));
}

#[test]
fn test_float_mul_basic() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Float.mul", &[Value::Float(3.0), Value::Float(2.0)])
        .expect("mul should succeed");
    assert_eq!(result, Value::Float(6.0));
}

#[test]
fn test_float_div_basic() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Float.div", &[Value::Float(10.0), Value::Float(2.0)])
        .expect("div should succeed");
    assert_eq!(result, Value::Float(5.0));
}

#[test]
fn test_float_div_by_zero_error() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Float.div", &[Value::Float(1.0), Value::Float(0.0)])
        .expect_err("div by zero should fail");
    match err {
        FfiError::ExecutionFailed { function, message } => {
            assert_eq!(function, "Float.div");
            assert!(message.contains("division by zero"), "message: {message}");
        }
        other => panic!("expected ExecutionFailed, got {other:?}"),
    }
}

#[test]
fn test_float_to_string() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("Float.toString", &[Value::Float(3.125)])
        .expect("toString should succeed");
    assert_eq!(result, Value::String("3.125".into()));
}

// ---------------------------------------------------------------------------
// Error handling
// ---------------------------------------------------------------------------

#[test]
fn test_type_mismatch_on_string_append() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("String.append", &[Value::Nat(1), Value::String("x".into())])
        .expect_err("type mismatch should fail");
    match err {
        FfiError::TypeMismatch {
            function,
            index,
            expected,
            found,
        } => {
            assert_eq!(function, "String.append");
            assert_eq!(index, 0);
            assert_eq!(expected, "String");
            assert_eq!(found, "Nat");
        }
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
fn test_arity_mismatch_on_string_append() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("String.append", &[])
        .expect_err("arity mismatch should fail");
    match err {
        FfiError::ArityMismatch {
            function,
            expected,
            got,
        } => {
            assert_eq!(function, "String.append");
            assert_eq!(expected, 2);
            assert_eq!(got, 0);
        }
        other => panic!("expected ArityMismatch, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// IO operations
// ---------------------------------------------------------------------------

#[test]
fn test_io_get_env_returns_string() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native("IO.getEnv", &[Value::String("PATH".into())])
        .expect("getEnv should succeed");
    match result {
        Value::String(s) => assert!(!s.is_empty(), "PATH should be non-empty"),
        other => panic!("expected String, got {other:?}"),
    }
}

#[test]
fn test_io_get_env_unset_returns_empty() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "IO.getEnv",
            &[Value::String("CLEAN_VERY_UNLIKELY_ENV_VAR_12345".into())],
        )
        .expect("getEnv should succeed for unset var");
    assert_eq!(result, Value::String(String::new()));
}

// ---------------------------------------------------------------------------
// Value equality and debug
// ---------------------------------------------------------------------------

#[test]
fn test_value_debug_formatting() {
    let val = Value::Nat(42);
    let dbg = format!("{val:?}");
    assert!(dbg.contains("Nat"), "debug should contain Nat: {dbg}");
    assert!(dbg.contains("42"), "debug should contain 42: {dbg}");
}

#[test]
fn test_value_partial_eq_different_types() {
    assert_ne!(Value::Nat(1), Value::Int(1));
    assert_ne!(Value::String("a".into()), Value::Nat(97));
    assert_eq!(Value::Unit, Value::Unit);
    assert_eq!(Value::Bool(true), Value::Bool(true));
    assert_ne!(Value::Bool(true), Value::Bool(false));
}

#[test]
fn test_value_clone_round_trip() {
    let original = Value::Array(vec![
        Value::Nat(1),
        Value::String("hello".into()),
        Value::Float(3.125),
    ]);
    let cloned = original.clone();
    assert_eq!(original, cloned);
}

// ---------------------------------------------------------------------------
// Char values
// ---------------------------------------------------------------------------

#[test]
fn test_value_char_clone_round_trip() {
    let original = Value::Char('z' as u32);
    let cloned = original.clone();
    assert_eq!(original, cloned);
    assert_eq!(original, Value::Char(122));
}

#[test]
fn test_value_char_debug_formatting() {
    let dbg = format!("{:?}", Value::Char('A' as u32));
    assert!(dbg.contains("Char"), "debug should contain Char: {dbg}");
    assert!(
        dbg.contains("65"),
        "debug should contain code point 65: {dbg}"
    );
}

#[test]
fn test_value_char_eq_distinguishes_from_nat() {
    assert_eq!(Value::Char(97), Value::Char(97));
    assert_ne!(Value::Char(97), Value::Char(98));
    // A Char must not compare equal to a Nat holding the same code point.
    assert_ne!(Value::Char(97), Value::Nat(97));
}

#[test]
fn test_value_char_round_trips_through_array() {
    let original = Value::Array(vec![Value::Char('h' as u32), Value::Char('i' as u32)]);
    let cloned = original.clone();
    assert_eq!(original, cloned);
}

#[test]
fn test_string_push_accepts_char_value() {
    let bridge = FfiBridge::new();
    let result = bridge
        .call_native(
            "String.push",
            &[Value::String("hell".into()), Value::Char('o' as u32)],
        )
        .expect("push should succeed with Char");
    assert_eq!(result, Value::String("hello".into()));
}

// ---------------------------------------------------------------------------
// Decidable-equality natives
// ---------------------------------------------------------------------------

#[test]
fn test_bool_eq_true_and_false() {
    let bridge = FfiBridge::new();
    let equal = bridge
        .call_native("Bool.eq", &[Value::Bool(true), Value::Bool(true)])
        .expect("Bool.eq should succeed");
    assert_eq!(equal, Value::Bool(true));
    let unequal = bridge
        .call_native("Bool.eq", &[Value::Bool(true), Value::Bool(false)])
        .expect("Bool.eq should succeed");
    assert_eq!(unequal, Value::Bool(false));
}

#[test]
fn test_bool_eq_type_mismatch() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Bool.eq", &[Value::Nat(1), Value::Bool(true)])
        .expect_err("Bool.eq should reject non-Bool");
    match err {
        FfiError::TypeMismatch {
            expected, found, ..
        } => {
            assert_eq!(expected, "Bool");
            assert_eq!(found, "Nat");
        }
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
fn test_string_eq_equal_and_unequal() {
    let bridge = FfiBridge::new();
    let equal = bridge
        .call_native(
            "String.eq",
            &[Value::String("abc".into()), Value::String("abc".into())],
        )
        .expect("String.eq should succeed");
    assert_eq!(equal, Value::Bool(true));
    let unequal = bridge
        .call_native(
            "String.eq",
            &[Value::String("abc".into()), Value::String("abd".into())],
        )
        .expect("String.eq should succeed");
    assert_eq!(unequal, Value::Bool(false));
}

#[test]
fn test_char_eq_equal_and_unequal() {
    let bridge = FfiBridge::new();
    let equal = bridge
        .call_native("Char.eq", &[Value::Char(97), Value::Char(97)])
        .expect("Char.eq should succeed");
    assert_eq!(equal, Value::Bool(true));
    let unequal = bridge
        .call_native("Char.eq", &[Value::Char(97), Value::Char(98)])
        .expect("Char.eq should succeed");
    assert_eq!(unequal, Value::Bool(false));
}

#[test]
fn test_char_eq_type_mismatch_does_not_panic() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Char.eq", &[Value::Nat(97), Value::Char(97)])
        .expect_err("Char.eq should reject Nat in place of Char");
    match err {
        FfiError::TypeMismatch {
            expected, found, ..
        } => {
            assert_eq!(expected, "Char");
            assert_eq!(found, "Nat");
        }
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Array contains / eq
// ---------------------------------------------------------------------------

#[test]
fn test_array_contains_present_and_absent() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::Nat(1), Value::Nat(2), Value::Nat(3)]);
    let present = bridge
        .call_native("Array.contains", &[arr.clone(), Value::Nat(2)])
        .expect("Array.contains should succeed");
    assert_eq!(present, Value::Bool(true));
    let absent = bridge
        .call_native("Array.contains", &[arr, Value::Nat(9)])
        .expect("Array.contains should succeed");
    assert_eq!(absent, Value::Bool(false));
}

#[test]
fn test_array_contains_mixed_element_types() {
    let bridge = FfiBridge::new();
    let arr = Value::Array(vec![Value::String("a".into()), Value::Char(98)]);
    let has_char = bridge
        .call_native("Array.contains", &[arr.clone(), Value::Char(98)])
        .expect("Array.contains should succeed");
    assert_eq!(has_char, Value::Bool(true));
    // A Nat with the same code point must not match a Char element.
    let no_nat = bridge
        .call_native("Array.contains", &[arr, Value::Nat(98)])
        .expect("Array.contains should succeed");
    assert_eq!(no_nat, Value::Bool(false));
}

#[test]
fn test_array_eq_element_wise() {
    let bridge = FfiBridge::new();
    let a = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let b = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let equal = bridge
        .call_native("Array.eq", &[a, b])
        .expect("Array.eq should succeed");
    assert_eq!(equal, Value::Bool(true));

    let c = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let d = Value::Array(vec![Value::Nat(1), Value::Nat(3)]);
    let unequal = bridge
        .call_native("Array.eq", &[c, d])
        .expect("Array.eq should succeed");
    assert_eq!(unequal, Value::Bool(false));
}

#[test]
fn test_array_eq_different_lengths() {
    let bridge = FfiBridge::new();
    let a = Value::Array(vec![Value::Nat(1)]);
    let b = Value::Array(vec![Value::Nat(1), Value::Nat(2)]);
    let result = bridge
        .call_native("Array.eq", &[a, b])
        .expect("Array.eq should succeed");
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_array_eq_rejects_non_array() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Array.eq", &[Value::Array(vec![]), Value::Nat(1)])
        .expect_err("Array.eq should reject non-array argument");
    match err {
        FfiError::TypeMismatch {
            index,
            expected,
            found,
            ..
        } => {
            assert_eq!(index, 1);
            assert_eq!(expected, "Array");
            assert_eq!(found, "Nat");
        }
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
fn test_new_eq_natives_registered() {
    let bridge = FfiBridge::new();
    let names = bridge.registered_names();
    for expected in [
        "Bool.eq",
        "String.eq",
        "Char.eq",
        "Array.contains",
        "Array.eq",
    ] {
        assert!(
            names.contains(&expected.to_owned()),
            "should have registered {expected}"
        );
    }
}

// ---------------------------------------------------------------------------
// Nat / Int arithmetic natives
//
// Each value-equality assertion references the authoritative const-fold spec
// in `clean-compiler/src/const_fold_ext2.rs` (`fold_arith` / `fold_cmp`), which
// the kernel reducers in `native_reducers_arith.rs` also match. Overflow cases
// must DECLINE (return `FfiError::ArithmeticOverflow`) rather than wrap, because
// the kernel reduces `Nat`/`Int` as unbounded bignums.
// ---------------------------------------------------------------------------

#[test]
fn test_arith_natives_registered() {
    let bridge = FfiBridge::new();
    let names = bridge.registered_names();
    for expected in [
        "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.pow", "Nat.beq", "Nat.blt",
        "Nat.ble", "Nat.bge", "Nat.bgt", "Nat.land", "Nat.lor", "Nat.xor", "Int.add", "Int.sub",
        "Int.mul", "Int.div", "Int.mod", "Int.beq", "Int.blt", "Int.ble", "Int.bge", "Int.bgt",
    ] {
        assert!(
            names.contains(&expected.to_owned()),
            "should have registered {expected}"
        );
    }
}

#[test]
fn test_nat_add_small() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.add", 2, 3) == Some(5).
    let result = bridge
        .call_native("Nat.add", &[Value::Nat(2), Value::Nat(3)])
        .expect("Nat.add should succeed");
    assert_eq!(result, Value::Nat(5));
}

#[test]
fn test_nat_add_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.add", u64::MAX, 1) == None (checked_add overflow) =>
    // DECLINE, NOT wrap-to-0. The kernel would produce the bignum 2^64.
    let err = bridge
        .call_native("Nat.add", &[Value::Nat(u64::MAX), Value::Nat(1)])
        .expect_err("Nat.add overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Nat.add"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_nat_sub_saturates_at_zero() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.sub", 5, 10) == Some(0) (truncated/floored subtraction).
    let result = bridge
        .call_native("Nat.sub", &[Value::Nat(5), Value::Nat(10)])
        .expect("Nat.sub should succeed");
    assert_eq!(result, Value::Nat(0));
}

#[test]
fn test_nat_sub_normal() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.sub", 10, 3) == Some(7).
    let result = bridge
        .call_native("Nat.sub", &[Value::Nat(10), Value::Nat(3)])
        .expect("Nat.sub should succeed");
    assert_eq!(result, Value::Nat(7));
}

#[test]
fn test_nat_mul_small() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.mul", 6, 7) == Some(42).
    let result = bridge
        .call_native("Nat.mul", &[Value::Nat(6), Value::Nat(7)])
        .expect("Nat.mul should succeed");
    assert_eq!(result, Value::Nat(42));
}

#[test]
fn test_nat_mul_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.mul", u64::MAX, 2) == None (checked_mul overflow) =>
    // DECLINE rather than emit a wrapped value.
    let err = bridge
        .call_native("Nat.mul", &[Value::Nat(u64::MAX), Value::Nat(2)])
        .expect_err("Nat.mul overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Nat.mul"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_nat_div_by_zero_is_zero() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.div", 7, 0) == Some(0) (Lean total semantics).
    let result = bridge
        .call_native("Nat.div", &[Value::Nat(7), Value::Nat(0)])
        .expect("Nat.div by zero should succeed (total)");
    assert_eq!(result, Value::Nat(0));
}

#[test]
fn test_nat_div_normal() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.div", 17, 5) == Some(3) (floored division).
    let result = bridge
        .call_native("Nat.div", &[Value::Nat(17), Value::Nat(5)])
        .expect("Nat.div should succeed");
    assert_eq!(result, Value::Nat(3));
}

#[test]
fn test_nat_mod_by_zero_is_dividend() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.mod", 7, 0) == Some(7) (modulus by zero yields dividend).
    let result = bridge
        .call_native("Nat.mod", &[Value::Nat(7), Value::Nat(0)])
        .expect("Nat.mod by zero should succeed (total)");
    assert_eq!(result, Value::Nat(7));
}

#[test]
fn test_nat_mod_normal() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.mod", 17, 5) == Some(2).
    let result = bridge
        .call_native("Nat.mod", &[Value::Nat(17), Value::Nat(5)])
        .expect("Nat.mod should succeed");
    assert_eq!(result, Value::Nat(2));
}

#[test]
fn test_nat_pow_small() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.pow", 2, 10) == Some(1024).
    let result = bridge
        .call_native("Nat.pow", &[Value::Nat(2), Value::Nat(10)])
        .expect("Nat.pow should succeed");
    assert_eq!(result, Value::Nat(1024));
}

#[test]
fn test_nat_pow_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.pow", 2, 64) == None (checked_pow overflows u64) =>
    // DECLINE. The kernel would produce the bignum 2^64.
    let err = bridge
        .call_native("Nat.pow", &[Value::Nat(2), Value::Nat(64)])
        .expect_err("Nat.pow overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Nat.pow"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_nat_beq_true_and_false() {
    let bridge = FfiBridge::new();
    // fold_cmp("Nat.beq", 3, 3) == Some(true); (3, 4) == Some(false).
    let eq = bridge
        .call_native("Nat.beq", &[Value::Nat(3), Value::Nat(3)])
        .expect("Nat.beq should succeed");
    assert_eq!(eq, Value::Bool(true));
    let ne = bridge
        .call_native("Nat.beq", &[Value::Nat(3), Value::Nat(4)])
        .expect("Nat.beq should succeed");
    assert_eq!(ne, Value::Bool(false));
}

#[test]
fn test_nat_blt_true_and_false() {
    let bridge = FfiBridge::new();
    // fold_cmp("Nat.blt", 3, 4) == Some(true); (4, 4) == Some(false).
    let lt = bridge
        .call_native("Nat.blt", &[Value::Nat(3), Value::Nat(4)])
        .expect("Nat.blt should succeed");
    assert_eq!(lt, Value::Bool(true));
    let not_lt = bridge
        .call_native("Nat.blt", &[Value::Nat(4), Value::Nat(4)])
        .expect("Nat.blt should succeed");
    assert_eq!(not_lt, Value::Bool(false));
}

#[test]
fn test_nat_ble_true_and_false() {
    let bridge = FfiBridge::new();
    // fold_cmp("Nat.ble", 4, 4) == Some(true); (5, 4) == Some(false).
    let le = bridge
        .call_native("Nat.ble", &[Value::Nat(4), Value::Nat(4)])
        .expect("Nat.ble should succeed");
    assert_eq!(le, Value::Bool(true));
    let not_le = bridge
        .call_native("Nat.ble", &[Value::Nat(5), Value::Nat(4)])
        .expect("Nat.ble should succeed");
    assert_eq!(not_le, Value::Bool(false));
}

#[test]
fn test_nat_bge_bgt() {
    let bridge = FfiBridge::new();
    // fold_cmp("Nat.bge", 5, 4) == Some(true); "Nat.bgt" (4, 4) == Some(false).
    let ge = bridge
        .call_native("Nat.bge", &[Value::Nat(5), Value::Nat(4)])
        .expect("Nat.bge should succeed");
    assert_eq!(ge, Value::Bool(true));
    let not_gt = bridge
        .call_native("Nat.bgt", &[Value::Nat(4), Value::Nat(4)])
        .expect("Nat.bgt should succeed");
    assert_eq!(not_gt, Value::Bool(false));
}

#[test]
fn test_nat_lor_land_xor_exact() {
    let bridge = FfiBridge::new();
    // fold_arith("Nat.lor", 0b1100, 0b1010) == Some(0b1110 == 14).
    let lor = bridge
        .call_native("Nat.lor", &[Value::Nat(0b1100), Value::Nat(0b1010)])
        .expect("Nat.lor should succeed");
    assert_eq!(lor, Value::Nat(0b1110));
    // fold_arith("Nat.land", 0b1100, 0b1010) == Some(0b1000 == 8).
    let land = bridge
        .call_native("Nat.land", &[Value::Nat(0b1100), Value::Nat(0b1010)])
        .expect("Nat.land should succeed");
    assert_eq!(land, Value::Nat(0b1000));
    // fold_arith("Nat.xor", 0b1100, 0b1010) == Some(0b0110 == 6).
    let xor = bridge
        .call_native("Nat.xor", &[Value::Nat(0b1100), Value::Nat(0b1010)])
        .expect("Nat.xor should succeed");
    assert_eq!(xor, Value::Nat(0b0110));
}

#[test]
fn test_nat_add_type_mismatch() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Nat.add", &[Value::Int(1), Value::Nat(2)])
        .expect_err("Nat.add should reject Int operand");
    match err {
        FfiError::TypeMismatch {
            function,
            index,
            expected,
            found,
        } => {
            assert_eq!(function, "Nat.add");
            assert_eq!(index, 0);
            assert_eq!(expected, "Nat");
            assert_eq!(found, "Int");
        }
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

#[test]
fn test_nat_add_arity_mismatch() {
    let bridge = FfiBridge::new();
    let err = bridge
        .call_native("Nat.add", &[Value::Nat(1)])
        .expect_err("Nat.add should reject single argument");
    match err {
        FfiError::ArityMismatch {
            function,
            expected,
            got,
        } => {
            assert_eq!(function, "Nat.add");
            assert_eq!(expected, 2);
            assert_eq!(got, 1);
        }
        other => panic!("expected ArityMismatch, got {other:?}"),
    }
}

#[test]
fn test_int_add_sub_mul_small() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.add", -3i64 as u64, 5) == Some(2).
    let add = bridge
        .call_native("Int.add", &[Value::Int(-3), Value::Int(5)])
        .expect("Int.add should succeed");
    assert_eq!(add, Value::Int(2));
    // fold_arith("Int.sub", 3, 5) == Some(-2).
    let sub = bridge
        .call_native("Int.sub", &[Value::Int(3), Value::Int(5)])
        .expect("Int.sub should succeed");
    assert_eq!(sub, Value::Int(-2));
    // fold_arith("Int.mul", -4, 6) == Some(-24).
    let mul = bridge
        .call_native("Int.mul", &[Value::Int(-4), Value::Int(6)])
        .expect("Int.mul should succeed");
    assert_eq!(mul, Value::Int(-24));
}

#[test]
fn test_int_add_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.add", i64::MAX, 1) == None (checked_add overflow) => DECLINE.
    let err = bridge
        .call_native("Int.add", &[Value::Int(i64::MAX), Value::Int(1)])
        .expect_err("Int.add overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Int.add"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_int_sub_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.sub", i64::MIN, 1) == None (checked_sub overflow) => DECLINE.
    let err = bridge
        .call_native("Int.sub", &[Value::Int(i64::MIN), Value::Int(1)])
        .expect_err("Int.sub overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Int.sub"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_int_mul_overflow_declines() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.mul", i64::MAX, 2) == None (checked_mul overflow) => DECLINE.
    let err = bridge
        .call_native("Int.mul", &[Value::Int(i64::MAX), Value::Int(2)])
        .expect_err("Int.mul overflow should decline");
    match err {
        FfiError::ArithmeticOverflow { function } => assert_eq!(function, "Int.mul"),
        other => panic!("expected ArithmeticOverflow, got {other:?}"),
    }
}

#[test]
fn test_int_div_by_zero_is_zero() {
    let bridge = FfiBridge::new();
    // Int division by zero yields 0 (Lean convention).
    let result = bridge
        .call_native("Int.div", &[Value::Int(7), Value::Int(0)])
        .expect("Int.div by zero should succeed (total)");
    assert_eq!(result, Value::Int(0));
}

#[test]
fn test_int_div_normal() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.div", -7, 2) == Some(-3) (i64 truncating division).
    let result = bridge
        .call_native("Int.div", &[Value::Int(-7), Value::Int(2)])
        .expect("Int.div should succeed");
    assert_eq!(result, Value::Int(-3));
}

#[test]
fn test_int_mod_by_zero_is_zero() {
    let bridge = FfiBridge::new();
    // Int modulus by zero yields 0 (Lean convention).
    let result = bridge
        .call_native("Int.mod", &[Value::Int(7), Value::Int(0)])
        .expect("Int.mod by zero should succeed (total)");
    assert_eq!(result, Value::Int(0));
}

#[test]
fn test_int_mod_normal() {
    let bridge = FfiBridge::new();
    // fold_arith("Int.mod", -7, 2) == Some(-1) (i64 truncating remainder).
    let result = bridge
        .call_native("Int.mod", &[Value::Int(-7), Value::Int(2)])
        .expect("Int.mod should succeed");
    assert_eq!(result, Value::Int(-1));
}

#[test]
fn test_int_comparisons_true_and_false() {
    let bridge = FfiBridge::new();
    // fold_cmp("Int.beq", -1, -1) == Some(true); (-1, 0) == Some(false).
    let beq_t = bridge
        .call_native("Int.beq", &[Value::Int(-1), Value::Int(-1)])
        .expect("Int.beq should succeed");
    assert_eq!(beq_t, Value::Bool(true));
    let beq_f = bridge
        .call_native("Int.beq", &[Value::Int(-1), Value::Int(0)])
        .expect("Int.beq should succeed");
    assert_eq!(beq_f, Value::Bool(false));
    // fold_cmp("Int.blt", -2, -1) == Some(true); (-1, -2) == Some(false).
    let blt_t = bridge
        .call_native("Int.blt", &[Value::Int(-2), Value::Int(-1)])
        .expect("Int.blt should succeed");
    assert_eq!(blt_t, Value::Bool(true));
    let blt_f = bridge
        .call_native("Int.blt", &[Value::Int(-1), Value::Int(-2)])
        .expect("Int.blt should succeed");
    assert_eq!(blt_f, Value::Bool(false));
    // fold_cmp("Int.ble", -1, -1) == Some(true); (0, -1) == Some(false).
    let ble_t = bridge
        .call_native("Int.ble", &[Value::Int(-1), Value::Int(-1)])
        .expect("Int.ble should succeed");
    assert_eq!(ble_t, Value::Bool(true));
    let ble_f = bridge
        .call_native("Int.ble", &[Value::Int(0), Value::Int(-1)])
        .expect("Int.ble should succeed");
    assert_eq!(ble_f, Value::Bool(false));
}
