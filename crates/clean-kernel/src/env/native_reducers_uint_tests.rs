// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for UInt native reducer functions (native_reducers_uint.rs).

use super::*;
use crate::tc::TypeChecker;

fn assert_nat_result(result: Option<Expr>, expected: u64) {
    let result = result.expect("expected reducer to produce a Nat literal");
    if let ExprKind::Lit(Literal::Nat(n)) = result.kind() {
        assert_eq!(n.to_u64(), Some(expected));
    } else {
        panic!("expected Nat literal {expected}, got {:?}", result);
    }
}

fn assert_bool_result(result: Option<Expr>, expected: bool) {
    let result = result.expect("expected reducer to produce a Bool constructor");
    let head = result.get_app_fn();
    let expected_name = if expected { "Bool.true" } else { "Bool.false" };
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), expected_name);
    } else {
        panic!("expected {expected_name}, got {:?}", head);
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
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name, expected_name);
    } else {
        panic!("expected {:?}, got {:?}", expected_name, head);
    }
}

fn check_uint_suite(
    add: NativeReducerFn,
    sub: NativeReducerFn,
    mul: NativeReducerFn,
    div: NativeReducerFn,
    modu: NativeReducerFn,
    beq: NativeReducerFn,
    blt: NativeReducerFn,
    ble: NativeReducerFn,
    dec_eq: NativeReducerFn,
    dec_eq_ty: &str,
    max: u64,
) {
    let wrap_factor = (max / 2) + 1;
    // A concrete UInt value is `<T>.ofNat <nat>` — the δ-reducible literal form
    // real proof terms supply and that the reshaped reducers peel
    // (`get_uint_ctor_val`). After the carrier BitVec-parity pass the genuine
    // ctor is `<T>.ofBitVec`, so the old `<T>.mk <nat>` spelling is ill-typed.
    let uint_val = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string(&format!("{dec_eq_ty}.ofNat")), vec![]),
            Expr::nat_lit(n),
        )
    };
    assert_nat_result(add(&[&Expr::nat_lit(1), &Expr::nat_lit(2)]), 3);
    assert_nat_result(add(&[&Expr::nat_lit(max), &Expr::nat_lit(1)]), 0);
    assert_nat_result(sub(&[&Expr::nat_lit(10), &Expr::nat_lit(3)]), 7);
    assert_nat_result(sub(&[&Expr::nat_lit(0), &Expr::nat_lit(1)]), max);
    assert_nat_result(mul(&[&Expr::nat_lit(6), &Expr::nat_lit(7)]), 42);
    assert_nat_result(mul(&[&Expr::nat_lit(wrap_factor), &Expr::nat_lit(2)]), 0);
    assert_nat_result(div(&[&Expr::nat_lit(7), &Expr::nat_lit(3)]), 2);
    assert_nat_result(div(&[&Expr::nat_lit(7), &Expr::nat_lit(0)]), 0);
    assert_nat_result(modu(&[&Expr::nat_lit(7), &Expr::nat_lit(3)]), 1);
    assert_nat_result(modu(&[&Expr::nat_lit(7), &Expr::nat_lit(0)]), 7);
    assert_bool_result(beq(&[&Expr::nat_lit(5), &Expr::nat_lit(5)]), true);
    assert_bool_result(beq(&[&Expr::nat_lit(5), &Expr::nat_lit(6)]), false);
    assert_bool_result(blt(&[&Expr::nat_lit(2), &Expr::nat_lit(5)]), true);
    assert_bool_result(blt(&[&Expr::nat_lit(5), &Expr::nat_lit(2)]), false);
    assert_bool_result(ble(&[&Expr::nat_lit(2), &Expr::nat_lit(5)]), true);
    assert_bool_result(ble(&[&Expr::nat_lit(5), &Expr::nat_lit(5)]), true);
    assert_bool_result(ble(&[&Expr::nat_lit(6), &Expr::nat_lit(5)]), false);
    assert_decidable_result(dec_eq(&[&uint_val(9), &uint_val(9)]), true);
    assert_decidable_result(dec_eq(&[&uint_val(9), &uint_val(10)]), false);
}

fn mk_binary_app(name: &Name, a: u64, b: u64) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(name.clone(), vec![]), Expr::nat_lit(a)),
        Expr::nat_lit(b),
    )
}

/// Collect all 45 UInt reducer function pointers for batch validation.
fn all_uint_reducers() -> Vec<NativeReducerFn> {
    vec![
        reduce_uint8_add,
        reduce_uint8_sub,
        reduce_uint8_mul,
        reduce_uint8_div,
        reduce_uint8_mod,
        reduce_uint8_beq,
        reduce_uint8_blt,
        reduce_uint8_ble,
        reduce_uint8_dec_eq,
        reduce_uint16_add,
        reduce_uint16_sub,
        reduce_uint16_mul,
        reduce_uint16_div,
        reduce_uint16_mod,
        reduce_uint16_beq,
        reduce_uint16_blt,
        reduce_uint16_ble,
        reduce_uint16_dec_eq,
        reduce_uint32_add,
        reduce_uint32_sub,
        reduce_uint32_mul,
        reduce_uint32_div,
        reduce_uint32_mod,
        reduce_uint32_beq,
        reduce_uint32_blt,
        reduce_uint32_ble,
        reduce_uint32_dec_eq,
        reduce_uint64_add,
        reduce_uint64_sub,
        reduce_uint64_mul,
        reduce_uint64_div,
        reduce_uint64_mod,
        reduce_uint64_beq,
        reduce_uint64_blt,
        reduce_uint64_ble,
        reduce_uint64_dec_eq,
        // USize reducers were removed with the carrier BitVec-parity pass:
        // v4.30's USize has a Platform-dependent width, so concrete USize
        // compute stays stuck in the kernel (faithful to Lean). Coverage of
        // that "stays stuck" behavior lives in the carrier differential
        // harness (test_usize_width_concrete_compute_pin_p1_must_flip).
    ]
}

/// Collect all UInt name constants for registration checks (USize excluded —
/// no longer natively reduced; see `all_uint_reducers`).
fn all_uint_names() -> Vec<Name> {
    vec![
        names::UINT8_ADD.clone(),
        names::UINT8_SUB.clone(),
        names::UINT8_MUL.clone(),
        names::UINT8_DIV.clone(),
        names::UINT8_MOD.clone(),
        names::UINT8_BEQ.clone(),
        names::UINT8_BLT.clone(),
        names::UINT8_BLE.clone(),
        names::UINT8_DEC_EQ.clone(),
        names::UINT16_ADD.clone(),
        names::UINT16_SUB.clone(),
        names::UINT16_MUL.clone(),
        names::UINT16_DIV.clone(),
        names::UINT16_MOD.clone(),
        names::UINT16_BEQ.clone(),
        names::UINT16_BLT.clone(),
        names::UINT16_BLE.clone(),
        names::UINT16_DEC_EQ.clone(),
        names::UINT32_ADD.clone(),
        names::UINT32_SUB.clone(),
        names::UINT32_MUL.clone(),
        names::UINT32_DIV.clone(),
        names::UINT32_MOD.clone(),
        names::UINT32_BEQ.clone(),
        names::UINT32_BLT.clone(),
        names::UINT32_BLE.clone(),
        names::UINT32_DEC_EQ.clone(),
        names::UINT64_ADD.clone(),
        names::UINT64_SUB.clone(),
        names::UINT64_MUL.clone(),
        names::UINT64_DIV.clone(),
        names::UINT64_MOD.clone(),
        names::UINT64_BEQ.clone(),
        names::UINT64_BLT.clone(),
        names::UINT64_BLE.clone(),
        names::UINT64_DEC_EQ.clone(),
    ]
}

#[test]
fn test_uint8_reducers() {
    check_uint_suite(
        reduce_uint8_add,
        reduce_uint8_sub,
        reduce_uint8_mul,
        reduce_uint8_div,
        reduce_uint8_mod,
        reduce_uint8_beq,
        reduce_uint8_blt,
        reduce_uint8_ble,
        reduce_uint8_dec_eq,
        "UInt8",
        u8::MAX as u64,
    );
}

#[test]
fn test_uint16_reducers() {
    check_uint_suite(
        reduce_uint16_add,
        reduce_uint16_sub,
        reduce_uint16_mul,
        reduce_uint16_div,
        reduce_uint16_mod,
        reduce_uint16_beq,
        reduce_uint16_blt,
        reduce_uint16_ble,
        reduce_uint16_dec_eq,
        "UInt16",
        u16::MAX as u64,
    );
}

#[test]
fn test_uint32_reducers() {
    check_uint_suite(
        reduce_uint32_add,
        reduce_uint32_sub,
        reduce_uint32_mul,
        reduce_uint32_div,
        reduce_uint32_mod,
        reduce_uint32_beq,
        reduce_uint32_blt,
        reduce_uint32_ble,
        reduce_uint32_dec_eq,
        "UInt32",
        u64::from(u32::MAX),
    );
}

#[test]
fn test_uint64_reducers() {
    check_uint_suite(
        reduce_uint64_add,
        reduce_uint64_sub,
        reduce_uint64_mul,
        reduce_uint64_div,
        reduce_uint64_mod,
        reduce_uint64_beq,
        reduce_uint64_blt,
        reduce_uint64_ble,
        reduce_uint64_dec_eq,
        "UInt64",
        u64::MAX,
    );
}

// No `test_usize_reducers`: USize compute is intentionally not natively
// reduced after the carrier BitVec-parity pass (Platform-dependent width).

#[test]
fn test_usize_core_native_reducers_are_intentionally_unregistered() {
    let mut env = Environment::new();
    env.init_uint_native_reducers();
    for name in [
        &*names::USIZE_ADD,
        &*names::USIZE_SUB,
        &*names::USIZE_MUL,
        &*names::USIZE_DIV,
        &*names::USIZE_MOD,
        &*names::USIZE_BEQ,
        &*names::USIZE_BLT,
        &*names::USIZE_BLE,
        &*names::USIZE_DEC_EQ,
    ] {
        assert!(
            env.get_native_reducer(name).is_none(),
            "{name} must stay unregistered while System.Platform.numBits is abstract"
        );
    }
}

#[test]
fn test_all_uint_reducers_reject_bad_args() {
    let var = Expr::const_(Name::from_string("x"), vec![]);
    for reducer in all_uint_reducers() {
        assert!(reducer(&[]).is_none(), "reducers should reject zero args");
        assert!(
            reducer(&[&Expr::nat_lit(1)]).is_none(),
            "should reject one arg"
        );
        assert!(
            reducer(&[&var, &Expr::nat_lit(1)]).is_none(),
            "should reject non-literal lhs"
        );
        assert!(
            reducer(&[&Expr::nat_lit(1), &var]).is_none(),
            "should reject non-literal rhs"
        );
    }
}

#[test]
fn test_uint_native_reducer_registration() {
    let mut env = Environment::new();
    env.init_uint_native_reducers();
    for name in all_uint_names() {
        assert!(
            env.get_native_reducer(&name).is_some(),
            "expected reducer {} to be registered",
            name
        );
    }
}

#[test]
fn test_reduce_native_fires_for_uint8_add() {
    let mut env = Environment::new();
    env.init_uint_native_reducers();
    let tc = TypeChecker::new(&env);
    let expr = mk_binary_app(&names::UINT8_ADD, u8::MAX as u64, 1);
    assert_nat_result(tc.reduce_native_for_test(&expr), 0);
}

#[test]
fn test_usize_dec_eq_stays_stuck() {
    // After the carrier BitVec-parity pass, USize decidable-equality is NOT
    // natively reduced: v4.30's USize has a Platform-dependent width
    // (`System.Platform.numBits`), so the kernel is provably stuck on concrete
    // USize comparisons — matching Lean. The old width-64 reducer was the
    // def-eq excess removed in that pass. This pins that the shortcut is gone.
    let mut env = Environment::new();
    env.init_uint_native_reducers();
    let tc = TypeChecker::new(&env);
    let mk = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("USize.mk"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let expr = Expr::apps(
        Expr::const_(names::USIZE_DEC_EQ.clone(), vec![]),
        [mk(17), mk(19)],
    );
    assert!(
        tc.reduce_native_for_test(&expr).is_none(),
        "USize decEq must no longer natively reduce (opaque Platform width)"
    );
}

#[test]
fn test_uint_dec_eq_is_sound() {
    use crate::env::Environment;
    fn mentions_sorry(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                s == "sorryAx" || s == "sorry"
            }
            ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                mentions_sorry(t) || mentions_sorry(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
            }
            _ => false,
        }
    }
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let mk = |ty: &str, n: u64| {
        // `<T>.ofNat <nat>` — the reducible literal form the reshaped reducers
        // peel (the ctor is `<T>.ofBitVec` after the BitVec-parity pass).
        Expr::app(
            Expr::const_(Name::from_string(&format!("{ty}.ofNat")), vec![]),
            Expr::nat_lit(n),
        )
    };
    // Both branches, for every concrete UInt width, must be sorry-free and
    // type-check at `Decidable (@Eq <T> a b)`.
    let cases: [(NativeReducerFn, &str); 4] = [
        (reduce_uint8_dec_eq, "UInt8"),
        (reduce_uint16_dec_eq, "UInt16"),
        (reduce_uint32_dec_eq, "UInt32"),
        (reduce_uint64_dec_eq, "UInt64"),
    ];
    for (red, ty) in cases {
        for (x, y) in [(1u64, 1u64), (1, 2)] {
            let a = mk(ty, x);
            let b = mk(ty, y);
            let term = red(&[&a, &b]).expect("uint decEq reduces on mk-form");
            assert!(
                !mentions_sorry(&term),
                "{ty}.decEq must be sorry-free: {term:?}"
            );
            let _ = tc
                .infer_type(&term)
                .unwrap_or_else(|e| panic!("{ty}.decEq output type-checks: {e:?}"));
        }
    }
}

/// SOUNDNESS GATE for ITEM 1 (`UInt*.decLt`): the witness the native reducer
/// emits must (a) be sorry/axiom-free and (b) type-check at `Decidable (@<T>.lt
/// a b)` *inside the kernel* (`reduce_native` trusts it without re-checking, so
/// the kernel must accept it as a subterm). Covers both `<`-true and `<`-false
/// for every UInt width, and verifies the value-level CORRECTNESS (true gives
/// `isTrue`, false gives `isFalse` — never a flipped comparison).
#[test]
fn test_uint_dec_lt_is_sound() {
    use crate::env::Environment;
    fn mentions_sorry(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                s == "sorryAx" || s == "sorry"
            }
            ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                mentions_sorry(t) || mentions_sorry(b)
            }
            ExprKind::Let(_, t, v, b, _) => {
                mentions_sorry(t) || mentions_sorry(v) || mentions_sorry(b)
            }
            _ => false,
        }
    }
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let mk = |ty: &str, n: u64| {
        // `<T>.ofNat <nat>` — the reducible literal form the reshaped reducers
        // peel (the ctor is `<T>.ofBitVec` after the BitVec-parity pass).
        Expr::app(
            Expr::const_(Name::from_string(&format!("{ty}.ofNat")), vec![]),
            Expr::nat_lit(n),
        )
    };
    let cases: [(NativeReducerFn, &str); 4] = [
        (reduce_uint8_dec_lt, "UInt8"),
        (reduce_uint16_dec_lt, "UInt16"),
        (reduce_uint32_dec_lt, "UInt32"),
        (reduce_uint64_dec_lt, "UInt64"),
    ];
    for (red, ty) in cases {
        // (x, y, x<y) — exercise true, false, and the equal (false) boundary.
        for (x, y, expect_true) in [(0u64, 1u64, true), (5, 2, false), (3, 3, false)] {
            let a = mk(ty, x);
            let b = mk(ty, y);
            let term = red(&[&a, &b]).expect("uint decLt reduces on mk-form");
            assert!(
                !mentions_sorry(&term),
                "{ty}.decLt must be sorry-free: {term:?}"
            );
            // value-level correctness: the constructor tag must match x<y.
            assert_decidable_result(Some(term.clone()), expect_true);
            // kernel acceptance: the witness type-checks at its (inferred) type.
            let _ = tc
                .infer_type(&term)
                .unwrap_or_else(|e| panic!("{ty}.decLt output ({x}<{y}) type-checks: {e:?}"));
        }
    }
}

/// END-TO-END (ITEM 1): `decide ((0 : UInt8) < 1)` WHNF-reduces to `Bool.true`
/// (it was stuck at `Decidable.rec` before the native `UInt8.decLt` reducer).
/// Built as `@decide (UInt8.lt a b) (UInt8.decLt a b)` with the operands in
/// `UInt8.ofNat n` form (which δι-WHNFs to `UInt8.mk n`) — exercising BOTH the
/// native `UInt8.decLt` reducer AND the operand pre-WHNF in `reduce_native` that
/// real proof terms (which supply `OfNat.ofNat`/`UInt8.ofNat` literals, not bare
/// `UInt8.mk`) depend on. Independent of olean reconstruction.
#[test]
fn test_decide_uint8_zero_lt_one_whnf_true() {
    use crate::env::Environment;
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());
    // `UInt8.ofNat n := fun n => UInt8.mk n` (data_types_uint.rs) — a δ-reducible
    // alias, mirroring how real literals are NOT in bare `.mk` form.
    let of_nat = |n: u64| {
        Expr::app(
            Expr::const_(Name::from_string("UInt8.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    };
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("UInt8.lt"), vec![]),
        [of_nat(0), of_nat(1)],
    );
    let inst = Expr::apps(
        Expr::const_(names::UINT8_DEC_LT.clone(), vec![]),
        [of_nat(0), of_nat(1)],
    );
    let decide = Expr::apps(
        Expr::const_(Name::from_string("decide"), vec![]),
        [lt_prop, inst],
    );
    let whnf = tc.whnf(&decide);
    assert_bool_result(Some(whnf), true);

    // Negative direction: `decide ((1 : UInt8) < 0)` must WHNF to `Bool.false`
    // (CORRECTNESS — never flip a false comparison to true).
    let inst_f = Expr::apps(
        Expr::const_(names::UINT8_DEC_LT.clone(), vec![]),
        [of_nat(1), of_nat(0)],
    );
    let lt_prop_f = Expr::apps(
        Expr::const_(Name::from_string("UInt8.lt"), vec![]),
        [of_nat(1), of_nat(0)],
    );
    let decide_f = Expr::apps(
        Expr::const_(Name::from_string("decide"), vec![]),
        [lt_prop_f, inst_f],
    );
    assert_bool_result(Some(tc.whnf(&decide_f)), false);
}
