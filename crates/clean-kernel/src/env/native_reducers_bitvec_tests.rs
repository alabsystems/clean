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

/// Read the `u128` value of a `Nat`-literal reducer result (panics if the result
/// is missing, not a `Nat` literal, or exceeds `u128`).
fn nat_result_u128(result: Option<Expr>) -> u128 {
    let result = result.expect("expected reducer to produce a Nat literal");
    match result.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            let limbs = n.limbs();
            assert!(limbs.len() <= 2, "result exceeds u128: {n:?}");
            let lo = u128::from(limbs.first().copied().unwrap_or(0));
            let hi = u128::from(limbs.get(1).copied().unwrap_or(0));
            lo | (hi << 64)
        }
        _ => panic!("expected Nat literal, got {result:?}"),
    }
}

#[test]
fn test_bitvec_of_nat_parks_on_ofnat_wrapped_value() {
    // REVERSED PIN (2026-08-28): the wrapped-operand read this test used to
    // assert (e9a172f67) injected raw payload literals into δι spines
    // mid-reduction — `Fin.rec` needs a constructor and wedged (b125's
    // direct-const case). An OfNat-WRAPPED operand now PARKS here and is
    // served at the consumer boundary instead
    // (`reduce_bitvec_to_nat`'s structural peel); the δι tower handles the
    // rest soundly, exactly as before the widening.
    let wrapped = Environment::ofnat_nat_lit(42);
    assert!(reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &wrapped]).is_none());
    let w = Environment::ofnat_nat_lit(8);
    assert!(reduce_bitvec_of_nat(&[&w, &Expr::nat_lit(259)]).is_none());
    // Bare literals keep firing — the payload world is unchanged.
    assert_nat_result(
        reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &Expr::nat_lit(259)]),
        3,
    );
}

#[test]
fn test_bitvec_of_nat_refuses_inconsistent_ofnat_wrapper() {
    // The genuine projection reads the field stored in `instOfNatNat`. An
    // ill-typed wrapper whose class index and stored field disagree must park,
    // never pick either value and thereby manufacture a reduction.
    let inconsistent = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![]),
        [
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::nat_lit(5),
            Expr::app(
                Expr::const_(Name::from_string("instOfNatNat"), vec![]),
                Expr::nat_lit(6),
            ),
        ],
    );
    assert!(reduce_bitvec_of_nat(&[&Expr::nat_lit(8), &inconsistent]).is_none());
    assert!(reduce_bitvec_of_nat(&[&inconsistent, &Expr::nat_lit(8)]).is_none());
}

#[test]
fn test_bitvec_of_nat_multilimb_value() {
    // Multi-limb (≥ 2^64) values now reduce for the whole 0 ≤ N < 2^128 range
    // instead of parking; the payload is emitted via `Expr::nat_lit_u128`.
    // i64::MAX (fits u64) at width 128 — no truncation.
    let i64_max = 9223372036854775807u128;
    assert_eq!(
        nat_result_u128(reduce_bitvec_of_nat(&[
            &Expr::nat_lit(128),
            &Expr::nat_lit_u128(i64_max),
        ])),
        i64_max
    );
    // i64::MIN as a 128-bit two's-complement pattern: 2^128 − 2^63 (multi-limb).
    let i64_min_pat = 0u128.wrapping_sub(1u128 << 63); // == 2^128 - 2^63
    assert_eq!(
        nat_result_u128(reduce_bitvec_of_nat(&[
            &Expr::nat_lit(128),
            &Expr::nat_lit_u128(i64_min_pat),
        ])),
        i64_min_pat
    );
    // i128::MIN pattern: 2^127; i128::MAX: 2^127 − 1 (both multi-limb, < 2^128).
    for v in [1u128 << 127, (1u128 << 127) - 1] {
        assert_eq!(
            nat_result_u128(reduce_bitvec_of_nat(&[
                &Expr::nat_lit(128),
                &Expr::nat_lit_u128(v),
            ])),
            v
        );
    }
    // Multi-limb value truncates at a narrower width: (2^128 − 2^63) mod 2^64
    // keeps the low limb = 2^63.
    assert_eq!(
        nat_result_u128(reduce_bitvec_of_nat(&[
            &Expr::nat_lit(64),
            &Expr::nat_lit_u128(i64_min_pat),
        ])),
        1u128 << 63
    );
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

#[test]
fn test_bitvec_to_nat_multilimb_passthrough() {
    // The u64 cap on the payload identity is lifted: a multi-limb payload
    // (e.g. i64::MIN's 128-bit pattern, 2^128 - 2^63) passes through intact.
    let i64_min_pat = 0u128.wrapping_sub(1u128 << 63);
    assert_eq!(
        nat_result_u128(reduce_bitvec_to_nat(&[
            &Expr::nat_lit(128),
            &Expr::nat_lit_u128(i64_min_pat),
        ])),
        i64_min_pat
    );
}

#[test]
fn test_bitvec_to_nat_peels_stuck_ofnat() {
    // `BitVec.toNat (BitVec.ofNat w n)` now reduces to `n mod 2^w` by a
    // STRUCTURAL peel of the stuck ofNat application — the composed
    // definition's own value — instead of parking.
    let of_nat = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [Expr::nat_lit(64), Expr::nat_lit(42)],
    );
    assert_nat_result(reduce_bitvec_to_nat(&[&Expr::nat_lit(64), &of_nat]), 42);
    // Truncation happens exactly as reduce_bitvec_of_nat would: 259 % 2^8 = 3.
    let of_nat_wrap = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [Expr::nat_lit(8), Expr::nat_lit(259)],
    );
    assert_nat_result(reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &of_nat_wrap]), 3);
    // Multi-limb payload at width 128: the i64::MIN pattern round-trips.
    let i64_min_pat = 0u128.wrapping_sub(1u128 << 63);
    let of_nat_big = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [Expr::nat_lit(128), Expr::nat_lit_u128(i64_min_pat)],
    );
    assert_eq!(
        nat_result_u128(reduce_bitvec_to_nat(&[&Expr::nat_lit(128), &of_nat_big])),
        i64_min_pat
    );
    // OfNat-wrapped payload inside the stuck application is read through the
    // hardened peel exactly as a bare literal is.
    let of_nat_wrapped = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [Expr::nat_lit(64), Environment::ofnat_nat_lit(42)],
    );
    assert_nat_result(
        reduce_bitvec_to_nat(&[&Expr::nat_lit(64), &of_nat_wrapped]),
        42,
    );
}

#[test]
fn test_bitvec_to_nat_ofnatlt_masks_to_identity() {
    // ofNatLT's payload is proved < 2^w, so the mask is the identity on it.
    let of_nat_lt = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNatLT"), vec![]),
        [
            Expr::nat_lit(8),
            Expr::nat_lit(200),
            Expr::const_(Name::from_string("pf"), vec![]),
        ],
    );
    assert_nat_result(reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &of_nat_lt]), 200);
}

#[test]
fn test_bitvec_to_nat_still_parks_on_other_shapes() {
    // ofFin stays parked (its payload sits behind Fin.mk, out of this peel's
    // scope), as does an ofNat whose payload is an open term.
    let of_fin = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofFin"), vec![]),
        [Expr::nat_lit(8), Expr::nat_lit(5)],
    );
    assert!(reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &of_fin]).is_none());
    let open_payload = Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [
            Expr::nat_lit(8),
            Expr::const_(Name::from_string("x"), vec![]),
        ],
    );
    assert!(reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &open_payload]).is_none());
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
    // RE-DECIDED 2026-09-28 (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`,
    // "every world pins only reviewed folds"): `BitVec.ofNat`'s reducer returns
    // a raw `Nat` payload where the prelude's definition returns a `BitVec`
    // constructor, so the review refuses it (leg T) and its row is `refused`:
    // the reducer no longer fires through the kernel, and the term δ-unfolds
    // to the definition. The reducer function itself is still pinned above.
    let mut env = Environment::with_prelude();
    env.init_bitvec_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::app(
            Expr::const_(names::BITVEC_OF_NAT.clone(), vec![]),
            Expr::nat_lit(8),
        ),
        Expr::nat_lit(300),
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "BitVec.ofNat's payload reducer must not fire over the prelude's definition"
    );
    assert!(!env.native_fold_authorized(&names::BITVEC_OF_NAT));
    assert!(env.native_fold_definition_admitted(&names::BITVEC_OF_NAT));
}

#[test]
fn test_reduce_native_fires_for_uint8_to_bitvec() {
    // RE-DECIDED 2026-09-28 (same section): `UInt8.toBitVec`'s reducer reads a
    // raw payload, which no typed input is, so the review never saw it fire and
    // the prelude's row is not `fold`; through the kernel it no longer fires.
    let mut env = Environment::with_prelude();
    env.init_bitvec_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(names::UINT8_TO_BITVEC.clone(), vec![]),
        Expr::nat_lit(42),
    );
    assert!(tc.reduce_native_for_test(&expr).is_none());
    assert_nat_result(reduce_uint8_to_bitvec(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_reduce_native_fires_for_uint32_of_bitvec() {
    // RE-DECIDED 2026-09-26 (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`):
    // `UInt32.ofBitVec` is a CONSTRUCTOR. A constructor application is already
    // a value, and no definition justifies rewriting it; a native reducer
    // registered under a constructor's name no longer fires
    // (`env/native_fold_authority.rs`), in the prelude or anywhere else.
    let env = Environment::with_prelude();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(names::UINT32_OF_BITVEC.clone(), vec![]),
        Expr::nat_lit(1000000),
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "a reducer keyed on a constructor must not fire"
    );
}

// --- BitVec.toNat OfNat-instance peel (b125_c5 shape) ---

/// Build `@OfNat.ofNat (BitVec w) i (@instOfNatBitVec w i')` — the elaborated
/// spelling of a `(i : BitVec w)` literal (consistent when `i == i'`).
fn ofnat_bitvec(w: u64, idx: u64, inst_val: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![]),
        [
            Expr::app(
                Expr::const_(Name::from_string("BitVec"), vec![]),
                Expr::nat_lit(w),
            ),
            Expr::nat_lit(idx),
            Expr::apps(
                Expr::const_(Name::from_string("instOfNatBitVec"), vec![]),
                [Expr::nat_lit(w), Expr::nat_lit(inst_val)],
            ),
        ],
    )
}

#[test]
fn test_bitvec_to_nat_peels_ofnat_instance_wrapper() {
    // `BitVec.toNat 8 (@OfNat.ofNat (BitVec 8) 5 (@instOfNatBitVec 8 5))` = 5.
    // Without the peel the δι fallback unfolds `toNat` to its `Fin.rec` spine
    // first, the inner `ofNat` native-reduces to the raw payload mid-spine,
    // and the recursor wedges (b125_c5, red from e9a172f67).
    assert_nat_result(
        reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &ofnat_bitvec(8, 5, 5)]),
        5,
    );
    // The wrap case: width 2, value 5 → 5 % 4 = 1 — value-distinguishing, so
    // the peel proves genuine `mod`, not identity on the index.
    assert_nat_result(
        reduce_bitvec_to_nat(&[&Expr::nat_lit(2), &ofnat_bitvec(2, 5, 5)]),
        1,
    );
}

#[test]
fn test_bitvec_to_nat_refuses_inconsistent_ofnat_instance() {
    // Index and instance value disagree: an ill-typed wrapper parks — the
    // reducer must never pick either half.
    assert!(reduce_bitvec_to_nat(&[&Expr::nat_lit(8), &ofnat_bitvec(8, 5, 6)]).is_none());
}
