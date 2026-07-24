// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bitwise operation tests for UInt native reducers.
//! Tests land, lor, xor, shiftLeft, shiftRight, complement, and toNat
//! for all five unsigned integer widths.

use super::*;

type Reducer = fn(args: &[&Expr]) -> Option<Expr>;

const UINT8_BITS: u64 = UINT8_MODULUS.trailing_zeros() as u64;
const UINT16_BITS: u64 = UINT16_MODULUS.trailing_zeros() as u64;
const UINT32_BITS: u64 = UINT32_MODULUS.trailing_zeros() as u64;
const UINT64_BITS: u64 = 64;

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    let actual = get_nat_val(&result).unwrap_or_else(|| {
        panic!("expected Nat literal {expected}, got {:?}", result);
    });
    assert_eq!(actual, expected);
}

fn width_mask(bits: u64) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

fn alternating_aa(bits: u64) -> u64 {
    let mut value = 0u64;
    let mut bit = 1u64;
    while bit < bits {
        value |= 1u64 << bit;
        bit += 2;
    }
    value
}

fn alternating_55(bits: u64) -> u64 {
    width_mask(bits) ^ alternating_aa(bits)
}

fn expected_shl(a: u64, shift: u64, bits: u64) -> u64 {
    // Lean v4.30 semantics: the shift amount is taken MOD the bit width
    // (`a <<< b = a <<< (b % bits)`), NOT saturating-to-zero. Verified live
    // on v4.30.0-rc2 by both `#eval` and kernel `rfl`:
    // `(1 : UInt64) <<< 64 = 1`, `(1 : UInt8) <<< 10 = 4`. Also pinned by
    // the carrier differential harness (`carrier_differential_tests.rs`).
    let sh = shift % bits;
    if bits == 64 {
        a.wrapping_shl(sh as u32)
    } else {
        (a << sh) & width_mask(bits)
    }
}

fn expected_shr(a: u64, shift: u64, bits: u64) -> u64 {
    // Lean v4.30 semantics: shift amount mod bit width (see expected_shl):
    // `(128 : UInt8) >>> 10 = 32`, `(1 : UInt64) >>> 64 = 1`.
    a >> (shift % bits)
}

fn expected_complement(a: u64, bits: u64) -> u64 {
    (!a) & width_mask(bits)
}

fn check_land_cases(reducer: Reducer, bits: u64) {
    let aa = alternating_aa(bits);
    let fifty_five = alternating_55(bits);
    let max = width_mask(bits);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(fifty_five)]),
        0,
    );
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(0)]), 0);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(max)]), aa);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(aa)]), aa);
}

fn check_lor_cases(reducer: Reducer, bits: u64) {
    let aa = alternating_aa(bits);
    let fifty_five = alternating_55(bits);
    let max = width_mask(bits);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(fifty_five)]),
        max,
    );
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(0)]), aa);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(max)]), max);
}

fn check_xor_cases(reducer: Reducer, bits: u64) {
    let aa = alternating_aa(bits);
    let fifty_five = alternating_55(bits);
    let max = width_mask(bits);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(fifty_five)]),
        max,
    );
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(aa)]), 0);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa), &Expr::nat_lit(0)]), aa);
}

fn check_shl_cases(reducer: Reducer, bits: u64) {
    let top_bit = 1u64 << (bits - 1);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(3), &Expr::nat_lit(2)]),
        expected_shl(3, 2, bits),
    );
    assert_nat_result(reducer(&[&Expr::nat_lit(42), &Expr::nat_lit(0)]), 42);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(1), &Expr::nat_lit(bits - 1)]),
        expected_shl(1, bits - 1, bits),
    );
    assert_nat_result(
        reducer(&[&Expr::nat_lit(3), &Expr::nat_lit(bits + 1)]),
        expected_shl(3, bits + 1, bits),
    );
    assert_nat_result(
        reducer(&[&Expr::nat_lit(top_bit), &Expr::nat_lit(1)]),
        expected_shl(top_bit, 1, bits),
    );
}

fn check_shr_cases(reducer: Reducer, bits: u64) {
    let top_bit = 1u64 << (bits - 1);
    let high_nibble = 0xAu64 << (bits - 4);
    let max = width_mask(bits);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(top_bit), &Expr::nat_lit(2)]),
        expected_shr(top_bit, 2, bits),
    );
    assert_nat_result(reducer(&[&Expr::nat_lit(42), &Expr::nat_lit(0)]), 42);
    assert_nat_result(
        reducer(&[&Expr::nat_lit(high_nibble), &Expr::nat_lit(bits + 1)]),
        expected_shr(high_nibble, bits + 1, bits),
    );
    assert_nat_result(
        reducer(&[&Expr::nat_lit(max), &Expr::nat_lit(bits - 1)]),
        expected_shr(max, bits - 1, bits),
    );
}

fn check_complement_cases(reducer: Reducer, bits: u64) {
    let aa = alternating_aa(bits);
    let fifty_five = alternating_55(bits);
    let max = width_mask(bits);
    assert_nat_result(reducer(&[&Expr::nat_lit(0)]), max);
    assert_nat_result(reducer(&[&Expr::nat_lit(max)]), 0);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa)]), fifty_five);
    assert_nat_result(reducer(&[&Expr::nat_lit(1)]), expected_complement(1, bits));
}

fn check_to_nat_cases(reducer: Reducer, bits: u64) {
    let aa = alternating_aa(bits);
    let max = width_mask(bits);
    assert_nat_result(reducer(&[&Expr::nat_lit(0)]), 0);
    assert_nat_result(reducer(&[&Expr::nat_lit(42)]), 42);
    assert_nat_result(reducer(&[&Expr::nat_lit(aa)]), aa);
    assert_nat_result(reducer(&[&Expr::nat_lit(max)]), max);
}

fn check_binary_rejects_non_literal_args(reducer: Reducer, op_name: &str) {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let one = Expr::nat_lit(1);
    assert!(
        reducer(&[&x, &one]).is_none(),
        "{op_name} should reject a non-literal lhs"
    );
    assert!(
        reducer(&[&one, &x]).is_none(),
        "{op_name} should reject a non-literal rhs"
    );
}

fn check_binary_rejects_insufficient_args(reducer: Reducer, op_name: &str) {
    let one = Expr::nat_lit(1);
    assert!(reducer(&[]).is_none(), "{op_name} should reject zero args");
    assert!(
        reducer(&[&one]).is_none(),
        "{op_name} should reject a missing rhs"
    );
}

fn check_unary_rejects_bad_args(reducer: Reducer, op_name: &str) {
    let x = Expr::const_(Name::from_string("x"), vec![]);
    assert!(reducer(&[]).is_none(), "{op_name} should reject zero args");
    assert!(
        reducer(&[&x]).is_none(),
        "{op_name} should reject a non-literal arg"
    );
}

macro_rules! define_uint_bitwise_tests {
    (
        bits = $bits:expr,
        reducers: {
            land = $land:ident,
            lor = $lor:ident,
            xor = $xor:ident,
            shl = $shl:ident,
            shr = $shr:ident,
            compl = $compl:ident,
            to_nat = $to_nat:ident,
        },
        tests: {
            land_cases = $land_cases:ident,
            lor_cases = $lor_cases:ident,
            xor_cases = $xor_cases:ident,
            shl_cases = $shl_cases:ident,
            shr_cases = $shr_cases:ident,
            complement_cases = $complement_cases:ident,
            to_nat_cases = $to_nat_cases:ident,
            land_rejects_non_literal_args = $land_rejects_non_literal_args:ident,
            shl_rejects_insufficient_args = $shl_rejects_insufficient_args:ident,
            complement_rejects_bad_args = $complement_rejects_bad_args:ident,
            to_nat_rejects_bad_args = $to_nat_rejects_bad_args:ident,
        }
    ) => {
        #[test]
        fn $land_cases() {
            check_land_cases($land, $bits);
        }

        #[test]
        fn $lor_cases() {
            check_lor_cases($lor, $bits);
        }

        #[test]
        fn $xor_cases() {
            check_xor_cases($xor, $bits);
        }

        #[test]
        fn $shl_cases() {
            check_shl_cases($shl, $bits);
        }

        #[test]
        fn $shr_cases() {
            check_shr_cases($shr, $bits);
        }

        #[test]
        fn $complement_cases() {
            check_complement_cases($compl, $bits);
        }

        #[test]
        fn $to_nat_cases() {
            check_to_nat_cases($to_nat, $bits);
        }

        #[test]
        fn $land_rejects_non_literal_args() {
            check_binary_rejects_non_literal_args($land, stringify!($land));
        }

        #[test]
        fn $shl_rejects_insufficient_args() {
            check_binary_rejects_insufficient_args($shl, stringify!($shl));
        }

        #[test]
        fn $complement_rejects_bad_args() {
            check_unary_rejects_bad_args($compl, stringify!($compl));
        }

        #[test]
        fn $to_nat_rejects_bad_args() {
            check_unary_rejects_bad_args($to_nat, stringify!($to_nat));
        }
    };
}

define_uint_bitwise_tests!(
    bits = UINT8_BITS,
    reducers: {
        land = reduce_uint8_land,
        lor = reduce_uint8_lor,
        xor = reduce_uint8_xor,
        shl = reduce_uint8_shl,
        shr = reduce_uint8_shr,
        compl = reduce_uint8_compl,
        to_nat = reduce_uint8_to_nat,
    },
    tests: {
        land_cases = test_uint8_land_cases,
        lor_cases = test_uint8_lor_cases,
        xor_cases = test_uint8_xor_cases,
        shl_cases = test_uint8_shl_cases,
        shr_cases = test_uint8_shr_cases,
        complement_cases = test_uint8_complement_cases,
        to_nat_cases = test_uint8_to_nat_cases,
        land_rejects_non_literal_args = test_uint8_land_rejects_non_literal_args,
        shl_rejects_insufficient_args = test_uint8_shl_rejects_insufficient_args,
        complement_rejects_bad_args = test_uint8_complement_rejects_bad_args,
        to_nat_rejects_bad_args = test_uint8_to_nat_rejects_bad_args,
    }
);

define_uint_bitwise_tests!(
    bits = UINT16_BITS,
    reducers: {
        land = reduce_uint16_land,
        lor = reduce_uint16_lor,
        xor = reduce_uint16_xor,
        shl = reduce_uint16_shl,
        shr = reduce_uint16_shr,
        compl = reduce_uint16_compl,
        to_nat = reduce_uint16_to_nat,
    },
    tests: {
        land_cases = test_uint16_land_cases,
        lor_cases = test_uint16_lor_cases,
        xor_cases = test_uint16_xor_cases,
        shl_cases = test_uint16_shl_cases,
        shr_cases = test_uint16_shr_cases,
        complement_cases = test_uint16_complement_cases,
        to_nat_cases = test_uint16_to_nat_cases,
        land_rejects_non_literal_args = test_uint16_land_rejects_non_literal_args,
        shl_rejects_insufficient_args = test_uint16_shl_rejects_insufficient_args,
        complement_rejects_bad_args = test_uint16_complement_rejects_bad_args,
        to_nat_rejects_bad_args = test_uint16_to_nat_rejects_bad_args,
    }
);

define_uint_bitwise_tests!(
    bits = UINT32_BITS,
    reducers: {
        land = reduce_uint32_land,
        lor = reduce_uint32_lor,
        xor = reduce_uint32_xor,
        shl = reduce_uint32_shl,
        shr = reduce_uint32_shr,
        compl = reduce_uint32_compl,
        to_nat = reduce_uint32_to_nat,
    },
    tests: {
        land_cases = test_uint32_land_cases,
        lor_cases = test_uint32_lor_cases,
        xor_cases = test_uint32_xor_cases,
        shl_cases = test_uint32_shl_cases,
        shr_cases = test_uint32_shr_cases,
        complement_cases = test_uint32_complement_cases,
        to_nat_cases = test_uint32_to_nat_cases,
        land_rejects_non_literal_args = test_uint32_land_rejects_non_literal_args,
        shl_rejects_insufficient_args = test_uint32_shl_rejects_insufficient_args,
        complement_rejects_bad_args = test_uint32_complement_rejects_bad_args,
        to_nat_rejects_bad_args = test_uint32_to_nat_rejects_bad_args,
    }
);

define_uint_bitwise_tests!(
    bits = UINT64_BITS,
    reducers: {
        land = reduce_uint64_land,
        lor = reduce_uint64_lor,
        xor = reduce_uint64_xor,
        shl = reduce_uint64_shl,
        shr = reduce_uint64_shr,
        compl = reduce_uint64_compl,
        to_nat = reduce_uint64_to_nat,
    },
    tests: {
        land_cases = test_uint64_land_cases,
        lor_cases = test_uint64_lor_cases,
        xor_cases = test_uint64_xor_cases,
        shl_cases = test_uint64_shl_cases,
        shr_cases = test_uint64_shr_cases,
        complement_cases = test_uint64_complement_cases,
        to_nat_cases = test_uint64_to_nat_cases,
        land_rejects_non_literal_args = test_uint64_land_rejects_non_literal_args,
        shl_rejects_insufficient_args = test_uint64_shl_rejects_insufficient_args,
        complement_rejects_bad_args = test_uint64_complement_rejects_bad_args,
        to_nat_rejects_bad_args = test_uint64_to_nat_rejects_bad_args,
    }
);

// No USize bitwise tests: USize compute was removed with the carrier
// BitVec-parity pass (Platform-dependent width => kernel stays stuck).

#[test]
fn test_usize_bitwise_native_reducers_are_intentionally_unregistered() {
    let mut env = Environment::new();
    env.init_uint_native_reducers();
    for name in [
        &*names::USIZE_LAND,
        &*names::USIZE_LOR,
        &*names::USIZE_XOR,
        &*names::USIZE_SHIFT_LEFT,
        &*names::USIZE_SHIFT_RIGHT,
        &*names::USIZE_COMPLEMENT,
        &*names::USIZE_TO_NAT,
    ] {
        assert!(
            env.get_native_reducer(name).is_none(),
            "{name} must stay unregistered while System.Platform.numBits is abstract"
        );
    }
}

// ---------------------------------------------------------------------------
// Shift edge cases: shift amount >= bitwidth wraps MOD the width
// (Lean v4.30 semantics, `a <<< b = a <<< (b % bits)`)
// ---------------------------------------------------------------------------

/// Verify shift-left at and beyond the exact bit width: v4.30 takes the
/// shift amount MOD the width, so shifting by any multiple of the width is
/// the identity (verified live: `(1 : UInt64) <<< 64 = 1` by `rfl`).
fn check_shl_exact_bitwidth(reducer: Reducer, bits: u64) {
    // shift by exactly bitwidth == shift by 0 (identity)
    assert_nat_result(
        reducer(&[&Expr::nat_lit(1), &Expr::nat_lit(bits)]),
        expected_shl(1, bits, bits),
    );
    assert_nat_result(
        reducer(&[&Expr::nat_lit(42), &Expr::nat_lit(bits)]),
        expected_shl(42, bits, bits),
    );
    // shift by 2 * bitwidth == shift by 0 (identity)
    assert_nat_result(
        reducer(&[&Expr::nat_lit(1), &Expr::nat_lit(2 * bits)]),
        expected_shl(1, 2 * bits, bits),
    );
    // shift by bitwidth + 1 == shift by 1
    assert_nat_result(
        reducer(&[&Expr::nat_lit(1), &Expr::nat_lit(bits + 1)]),
        expected_shl(1, bits + 1, bits),
    );
    // shift by a large multiple of bitwidth == shift by 0 (identity)
    assert_nat_result(
        reducer(&[&Expr::nat_lit(7), &Expr::nat_lit(100 * bits)]),
        expected_shl(7, 100 * bits, bits),
    );
}

fn check_shr_exact_bitwidth(reducer: Reducer, bits: u64) {
    let max = width_mask(bits);
    // shift right by exactly bitwidth == shift by 0 (identity)
    assert_nat_result(
        reducer(&[&Expr::nat_lit(max), &Expr::nat_lit(bits)]),
        expected_shr(max, bits, bits),
    );
    assert_nat_result(
        reducer(&[&Expr::nat_lit(42), &Expr::nat_lit(bits)]),
        expected_shr(42, bits, bits),
    );
    // shift by 2 * bitwidth == shift by 0 (identity)
    assert_nat_result(
        reducer(&[&Expr::nat_lit(max), &Expr::nat_lit(2 * bits)]),
        expected_shr(max, 2 * bits, bits),
    );
    // shift by bitwidth + 1 == shift by 1
    assert_nat_result(
        reducer(&[&Expr::nat_lit(max), &Expr::nat_lit(bits + 1)]),
        expected_shr(max, bits + 1, bits),
    );
}

macro_rules! define_shift_masking_tests {
    ($shl:ident, $shr:ident, $bits:expr,
     $test_shl:ident, $test_shr:ident) => {
        #[test]
        fn $test_shl() {
            check_shl_exact_bitwidth($shl, $bits);
        }

        #[test]
        fn $test_shr() {
            check_shr_exact_bitwidth($shr, $bits);
        }
    };
}

define_shift_masking_tests!(
    reduce_uint8_shl,
    reduce_uint8_shr,
    UINT8_BITS,
    test_uint8_shl_exact_bitwidth_masking,
    test_uint8_shr_exact_bitwidth_masking
);

define_shift_masking_tests!(
    reduce_uint16_shl,
    reduce_uint16_shr,
    UINT16_BITS,
    test_uint16_shl_exact_bitwidth_masking,
    test_uint16_shr_exact_bitwidth_masking
);

define_shift_masking_tests!(
    reduce_uint32_shl,
    reduce_uint32_shr,
    UINT32_BITS,
    test_uint32_shl_exact_bitwidth_masking,
    test_uint32_shr_exact_bitwidth_masking
);

define_shift_masking_tests!(
    reduce_uint64_shl,
    reduce_uint64_shr,
    UINT64_BITS,
    test_uint64_shl_exact_bitwidth_masking,
    test_uint64_shr_exact_bitwidth_masking
);

// No USize shift-masking tests: USize compute removed with the carrier
// BitVec-parity pass (Platform-dependent width => kernel stays stuck).

// ---------------------------------------------------------------------------
// Regression tests: exact Lean v4.30 parity for large shift amounts.
// v4.30 takes the shift amount MOD the bit width (`a <<< b = a <<< (b %
// bits)`), verified live on v4.30.0-rc2 by `#eval` AND kernel `rfl`
// (carrier-parity P0; supersedes the pre-BitVec #3236 saturating pins) and
// pinned corpus-wide by the differential harness
// (`carrier_differential_tests.rs` / `tests/fixtures/carrier_v4_30/`).
// ---------------------------------------------------------------------------

/// UInt64.shiftLeft 1 64 = 1 (shift by 64 % 64 = 0)
#[test]
fn test_uint64_shl_by_64_wraps_to_identity() {
    assert_nat_result(
        reduce_uint64_shl(&[&Expr::nat_lit(1), &Expr::nat_lit(64)]),
        1,
    );
}

/// UInt8.shiftLeft 1 10 = 4 (shift by 10 % 8 = 2)
#[test]
fn test_uint8_shl_by_10_shifts_by_2() {
    assert_nat_result(
        reduce_uint8_shl(&[&Expr::nat_lit(1), &Expr::nat_lit(10)]),
        4,
    );
}

/// UInt8.shiftRight 128 10 = 32 (shift by 10 % 8 = 2)
#[test]
fn test_uint8_shr_128_by_10_shifts_by_2() {
    assert_nat_result(
        reduce_uint8_shr(&[&Expr::nat_lit(128), &Expr::nat_lit(10)]),
        32,
    );
}

/// UInt32.shiftLeft 1 32 = 1 (shift by 32 % 32 = 0)
#[test]
fn test_uint32_shl_by_32_wraps_to_identity() {
    assert_nat_result(
        reduce_uint32_shl(&[&Expr::nat_lit(1), &Expr::nat_lit(32)]),
        1,
    );
}

/// UInt16.shiftLeft 0xFFFF 16 = 0xFFFF (shift by 16 % 16 = 0)
#[test]
fn test_uint16_shl_max_by_bitwidth_wraps_to_identity() {
    assert_nat_result(
        reduce_uint16_shl(&[&Expr::nat_lit(0xFFFF), &Expr::nat_lit(16)]),
        0xFFFF,
    );
}

/// UInt64.shiftRight 1 64 = 1 (shift by 64 % 64 = 0)
#[test]
fn test_uint64_shr_by_64_wraps_to_identity() {
    assert_nat_result(
        reduce_uint64_shr(&[&Expr::nat_lit(1), &Expr::nat_lit(64)]),
        1,
    );
}

// USize shift tests removed: USize compute is no longer native (opaque
// Platform width); the "stays stuck" behavior is pinned by the carrier
// differential harness (test_usize_width_concrete_compute_pin_p1_must_flip).

/// Verify sub-bitwidth shifts still work correctly after the fix.
#[test]
fn test_shift_normal_cases_still_work() {
    // UInt8: 1 << 3 = 8
    assert_nat_result(reduce_uint8_shl(&[&Expr::nat_lit(1), &Expr::nat_lit(3)]), 8);
    // UInt8: 128 >> 3 = 16
    assert_nat_result(
        reduce_uint8_shr(&[&Expr::nat_lit(128), &Expr::nat_lit(3)]),
        16,
    );
    // UInt64: 1 << 63 = 2^63
    assert_nat_result(
        reduce_uint64_shl(&[&Expr::nat_lit(1), &Expr::nat_lit(63)]),
        1u64 << 63,
    );
    // UInt64: u64::MAX >> 63 = 1
    assert_nat_result(
        reduce_uint64_shr(&[&Expr::nat_lit(u64::MAX), &Expr::nat_lit(63)]),
        1,
    );
    // UInt32: 0xFF << 8 = 0xFF00
    assert_nat_result(
        reduce_uint32_shl(&[&Expr::nat_lit(0xFF), &Expr::nat_lit(8)]),
        0xFF00,
    );
}
