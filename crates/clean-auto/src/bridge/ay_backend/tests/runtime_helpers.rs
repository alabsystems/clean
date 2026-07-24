// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Panic-payload and BigNat helper coverage tests.

use super::*;

#[test]
fn test_panic_payload_to_string_extracts_str_payload() {
    let payload: Box<dyn std::any::Any + Send> = Box::new("solver panic");

    assert_eq!(panic_payload_to_string(&payload), "solver panic");
}

#[test]
fn test_panic_payload_to_string_extracts_string_payload() {
    let payload: Box<dyn std::any::Any + Send> = Box::new(String::from("owned panic"));

    assert_eq!(panic_payload_to_string(&payload), "owned panic");
}

#[test]
fn test_panic_payload_to_string_falls_back_for_unknown_payload() {
    let payload: Box<dyn std::any::Any + Send> = Box::new(17u32);

    assert_eq!(panic_payload_to_string(&payload), "unknown panic payload");
}

#[test]
fn test_bignat_to_bigint_converts_small_value() {
    let value = BigNat::Small(42);

    assert_eq!(bignat_to_bigint(&value), BigInt::from(42u64));
}

#[test]
fn test_bignat_to_bigint_preserves_limb_order() {
    let value = BigNat::Big(vec![0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210]);
    let expected = BigInt::parse_bytes(b"fedcba98765432100123456789abcdef", 16)
        .expect("hex literal should parse");

    assert_eq!(bignat_to_bigint(&value), expected);
}

#[test]
fn test_bignat_to_bigint_keeps_zero_middle_limb() {
    let value = BigNat::Big(vec![1, 0, 2]);
    let expected = BigInt::from(1u8) + (BigInt::from(2u8) << 128);

    assert_eq!(bignat_to_bigint(&value), expected);
}
