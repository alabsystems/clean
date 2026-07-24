// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for UInt/USize conversion native reducers.

use super::*;

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(expected), "expected {expected}");
    } else {
        panic!("expected Nat literal {expected}, got {:?}", result);
    }
}

// --- ofNat: NO native reducer (δ-unfolds the genuine definition) ---
//
// `<Name>.ofNat` deliberately has no native reducer; it δ-unfolds its real
// definition so the result carries the GENUINE constructor for whichever env is
// loaded. In a pure-clean env (`init_uint_type`) that definition is
// `fun n => <Name>.mk n`, so `<Name>.ofNat n` whnf-reduces to `<Name>.mk n`
// via δ + β (no native shortcut, no fictional ctor). This is the value model
// the olean import then overrides with the BitVec-based `<Name>.ofBitVec` form.

#[test]
fn test_uint_of_nat_native_reducers_are_intentionally_unregistered() {
    let mut env = Environment::new();
    env.init_uint_conv_native_reducers();
    for name in [
        "UInt8.ofNat",
        "UInt16.ofNat",
        "UInt32.ofNat",
        "UInt64.ofNat",
        "USize.ofNat",
    ] {
        assert!(
            env.get_native_reducer(&Name::from_string(name)).is_none(),
            "{name} must have no native reducer; it delta-unfolds the environment's genuine definition"
        );
    }
}

#[test]
fn test_uint8_of_nat_delta_unfolds_to_genuine_ctor() {
    // LEAN v4.30 carrier (carrier BitVec-parity pass): `UInt8` is the structure
    // `structure UInt8 where ofBitVec :: (toBitVec : BitVec 8)`, and
    // `UInt8.ofNat n := UInt8.ofBitVec (BitVec.ofNat 8 n)`. So `UInt8.ofNat 42`
    // δ→ the genuine `UInt8.ofBitVec` ctor with a single `BitVec 8` payload
    // whose underlying `Nat` (`UInt8.toNat`) reduces to 42.
    let env = Environment::with_prelude();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
        Expr::nat_lit(42),
    );
    let w = tc.whnf(&expr);
    let head = w.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "UInt8.ofBitVec",
            "UInt8.ofNat should δ-reduce to the genuine UInt8.ofBitVec ctor"
        ),
        other => panic!("expected UInt8.ofBitVec head, got {:?}", other),
    }
    let args = w.get_app_args();
    assert_eq!(args.len(), 1, "UInt8.ofBitVec takes one BitVec 8 payload");
    // The underlying Nat is recovered by whnf of `UInt8.toNat (UInt8.ofNat 42)`,
    // which ι-reduces through `Fin.val` to the literal 42.
    let to_nat = Expr::app(Expr::const_(Name::from_string("UInt8.toNat"), vec![]), expr);
    let n_w = tc.whnf(&to_nat);
    if let ExprKind::Lit(Literal::Nat(n)) = n_w.kind() {
        assert_eq!(
            n.to_u64(),
            Some(42),
            "UInt8.toNat (UInt8.ofNat 42) must reduce to the literal 42"
        );
    } else {
        panic!("expected Nat payload 42 from UInt8.toNat, got {:?}", n_w);
    }
}

// --- Narrowing conversion tests ---

#[test]
fn test_uint16_to_uint8_narrowing() {
    assert_nat_result(reduce_uint16_to_uint8(&[&Expr::nat_lit(300)]), 44);
    assert_nat_result(reduce_uint16_to_uint8(&[&Expr::nat_lit(255)]), 255);
}

#[test]
fn test_uint32_to_uint8_narrowing() {
    assert_nat_result(reduce_uint32_to_uint8(&[&Expr::nat_lit(1000)]), 232);
}

#[test]
fn test_uint32_to_uint16_narrowing() {
    assert_nat_result(reduce_uint32_to_uint16(&[&Expr::nat_lit(70000)]), 4464);
}

#[test]
fn test_uint64_to_uint8_narrowing() {
    assert_nat_result(reduce_uint64_to_uint8(&[&Expr::nat_lit(257)]), 1);
}

#[test]
fn test_uint64_to_uint16_narrowing() {
    assert_nat_result(reduce_uint64_to_uint16(&[&Expr::nat_lit(65537)]), 1);
}

#[test]
fn test_uint64_to_uint32_narrowing() {
    assert_nat_result(reduce_uint64_to_uint32(&[&Expr::nat_lit(4294967297)]), 1);
}

#[test]
fn test_usize_to_uint8_narrowing() {
    assert_nat_result(reduce_usize_to_uint8(&[&Expr::nat_lit(512)]), 0);
}

#[test]
fn test_usize_to_uint16_narrowing() {
    assert_nat_result(reduce_usize_to_uint16(&[&Expr::nat_lit(131072)]), 0);
}

#[test]
fn test_usize_to_uint32_narrowing() {
    assert_nat_result(reduce_usize_to_uint32(&[&Expr::nat_lit(8589934592)]), 0);
}

// --- Widening conversion tests ---

#[test]
fn test_uint8_to_uint16_widening() {
    assert_nat_result(reduce_uint8_to_uint16(&[&Expr::nat_lit(200)]), 200);
}

#[test]
fn test_uint8_to_uint32_widening() {
    assert_nat_result(reduce_uint8_to_uint32(&[&Expr::nat_lit(255)]), 255);
}

#[test]
fn test_uint8_to_uint64_widening() {
    assert_nat_result(reduce_uint8_to_uint64(&[&Expr::nat_lit(128)]), 128);
}

#[test]
fn test_uint16_to_uint32_widening() {
    assert_nat_result(reduce_uint16_to_uint32(&[&Expr::nat_lit(50000)]), 50000);
}

#[test]
fn test_uint16_to_uint64_widening() {
    assert_nat_result(reduce_uint16_to_uint64(&[&Expr::nat_lit(60000)]), 60000);
}

#[test]
fn test_uint32_to_uint64_widening() {
    assert_nat_result(
        reduce_uint32_to_uint64(&[&Expr::nat_lit(3000000000)]),
        3000000000,
    );
}

#[test]
fn test_uint8_to_usize_widening() {
    assert_nat_result(reduce_uint8_to_usize(&[&Expr::nat_lit(42)]), 42);
}

#[test]
fn test_uint16_to_usize_widening() {
    assert_nat_result(reduce_uint16_to_usize(&[&Expr::nat_lit(60000)]), 60000);
}

#[test]
fn test_uint32_to_usize_widening() {
    assert_nat_result(
        reduce_uint32_to_usize(&[&Expr::nat_lit(3000000000)]),
        3000000000,
    );
}

#[test]
fn test_uint64_to_usize_identity() {
    assert_nat_result(reduce_uint64_to_usize(&[&Expr::nat_lit(999999)]), 999999);
}

#[test]
fn test_usize_to_uint64_identity() {
    assert_nat_result(reduce_usize_to_uint64(&[&Expr::nat_lit(999999)]), 999999);
}

// --- Fin.val tests ---

#[test]
fn test_fin_val_identity() {
    assert_nat_result(reduce_fin_val(&[&Expr::nat_lit(7)]), 7);
    assert_nat_result(reduce_fin_val(&[&Expr::nat_lit(0)]), 0);
}

#[test]
fn test_fin_val_no_args_returns_none() {
    assert!(reduce_fin_val(&[]).is_none());
}

#[test]
fn test_fin_val_non_literal_returns_none() {
    let var = Expr::const_(Name::from_string("x"), vec![]);
    assert!(reduce_fin_val(&[&var]).is_none());
}

// --- Registration test ---

#[test]
fn test_all_conv_reducers_registered() {
    let mut env = Environment::new();
    env.init_uint_conv_native_reducers();

    let expected_names = vec![
        &*names::UINT16_TO_UINT8,
        &*names::UINT32_TO_UINT8,
        &*names::UINT32_TO_UINT16,
        &*names::UINT64_TO_UINT8,
        &*names::UINT64_TO_UINT16,
        &*names::UINT64_TO_UINT32,
        &*names::USIZE_TO_UINT8,
        &*names::USIZE_TO_UINT16,
        &*names::USIZE_TO_UINT32,
        &*names::UINT8_TO_UINT16,
        &*names::UINT8_TO_UINT32,
        &*names::UINT8_TO_UINT64,
        &*names::UINT16_TO_UINT32,
        &*names::UINT16_TO_UINT64,
        &*names::UINT32_TO_UINT64,
        &*names::UINT8_TO_USIZE,
        &*names::UINT16_TO_USIZE,
        &*names::UINT32_TO_USIZE,
        &*names::UINT64_TO_USIZE,
        &*names::USIZE_TO_UINT64,
        &*names::FIN_VAL,
    ];
    for name in expected_names {
        assert!(
            env.get_native_reducer(name).is_some(),
            "expected reducer {} to be registered",
            name
        );
    }
}

// --- End-to-end: ofNat has NO native reducer (declines, δ takes over) ---

#[test]
fn test_reduce_native_declines_for_usize_of_nat() {
    // No native reducer registered for `<Name>.ofNat`; reduce_native declines
    // so the kernel falls through to δ-unfolding the genuine definition.
    let mut env = Environment::new();
    env.init_uint_conv_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(Name::from_string("USize.ofNat"), vec![]),
        Expr::nat_lit(42),
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "USize.ofNat must NOT have a native reducer"
    );
}

#[test]
fn test_reduce_native_declines_for_uint8_of_nat() {
    let mut env = Environment::new();
    env.init_uint_conv_native_reducers();
    let tc = crate::tc::TypeChecker::new(&env);
    let expr = Expr::app(
        Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
        Expr::nat_lit(300),
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "UInt8.ofNat must NOT have a native reducer"
    );
}
