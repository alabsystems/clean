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

// --- WS6.10: every fixed-width reducer accelerates a REAL definition ---
//
// Before WS6.10 the twelve fixed-width conversion names below had a native
// reducer and NO constant: `def widen (a : UInt8) : UInt64 := a.toUInt64`
// was "Unknown identifier" (F-107). `init_uint_conversions` now registers each
// as `<target>.ofNat (<source>.toNat x)` (`Environment::uint_conversion_decl`,
// the one builder both the registration and this test go through).
// A name-keyed reducer that disagreed with the definition it accelerates would
// give one ground term two values, so the agreement below is checked by the
// KERNEL (`is_def_eq` against the δ-unfolded definition), over every width pair
// and the boundary values of both the source and the target width.

use crate::env::data_types_uint::{uint_conversion_name, FIXED_WIDTH_UINTS};
use crate::env::{ConstantKind, Declaration};
use crate::expr::BinderInfo;

/// The twelve fixed-width conversions and the reducer keyed on each name.
fn fixed_width_conversions() -> [(&'static str, &'static str, NativeReducerFn); 12] {
    [
        ("UInt16", "UInt8", reduce_uint16_to_uint8),
        ("UInt32", "UInt8", reduce_uint32_to_uint8),
        ("UInt32", "UInt16", reduce_uint32_to_uint16),
        ("UInt64", "UInt8", reduce_uint64_to_uint8),
        ("UInt64", "UInt16", reduce_uint64_to_uint16),
        ("UInt64", "UInt32", reduce_uint64_to_uint32),
        ("UInt8", "UInt16", reduce_uint8_to_uint16),
        ("UInt8", "UInt32", reduce_uint8_to_uint32),
        ("UInt8", "UInt64", reduce_uint8_to_uint64),
        ("UInt16", "UInt32", reduce_uint16_to_uint32),
        ("UInt16", "UInt64", reduce_uint16_to_uint64),
        ("UInt32", "UInt64", reduce_uint32_to_uint64),
    ]
}

fn width_bits(name: &str) -> u32 {
    match name {
        "UInt8" => 8,
        "UInt16" => 16,
        "UInt32" => 32,
        "UInt64" => 64,
        other => panic!("not a fixed-width UInt: {other}"),
    }
}

/// Source values that exercise the conversion: zero, one, both widths' max,
/// the first wrapping value of the target, and a value that wraps to a
/// non-trivial residue (`300 → 44` at UInt8, `70000 → 4464` at UInt16).
fn sample_values(source: &str, target: &str) -> Vec<u64> {
    let src_max = u64::MAX >> (64 - width_bits(source));
    let tgt_max = u64::MAX >> (64 - width_bits(target));
    let mut values = vec![0, 1, 44, 255, 300, 65_535, 70_000, 4_294_967_297, src_max];
    if tgt_max < src_max {
        values.extend([tgt_max, tgt_max + 1, tgt_max + 2]);
    }
    values.retain(|&v| v <= src_max);
    values.sort_unstable();
    values.dedup();
    values
}

/// Every `(conversion, value, reducer output)` at which the reducer DISAGREES
/// with `<target>.toNat (body (<source>.ofNat value))`, where `body` is the
/// conversion's definition as supplied by `body_of`. Empty = agreement.
fn reducer_disagreements(env: &Environment, body_of: &dyn Fn(&str, &str) -> Expr) -> Vec<String> {
    let tc = crate::tc::TypeChecker::with_mode(env, env.mode());
    let mut bad = Vec::new();
    for (source, target, reducer) in fixed_width_conversions() {
        let body = body_of(source, target);
        let src_of_nat = Expr::const_(Name::from_string(&format!("{source}.ofNat")), vec![]);
        let tgt_to_nat = Expr::const_(Name::from_string(&format!("{target}.toNat")), vec![]);
        for v in sample_values(source, target) {
            let reduced = reducer(&[&Expr::nat_lit(v)])
                .and_then(|e| get_nat_val(&e))
                .unwrap_or_else(|| panic!("{source}->{target} reducer declined on {v}"));
            let converted = Expr::app(
                tgt_to_nat.clone(),
                Expr::app(
                    body.clone(),
                    Expr::app(src_of_nat.clone(), Expr::nat_lit(v)),
                ),
            );
            if !tc.is_def_eq(&converted, &Expr::nat_lit(reduced)) {
                bad.push(format!(
                    "{}({v}): reducer {reduced}",
                    uint_conversion_name(source, target)
                ));
            }
        }
    }
    bad
}

fn registered_value(env: &Environment, source: &str, target: &str) -> Expr {
    let name = uint_conversion_name(source, target);
    env.get_const(&Name::from_string(&name))
        .unwrap_or_else(|| panic!("{name} must be a prelude constant (WS6.10)"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("{name} must be a definition with a value"))
}

/// Positive: all twelve names are axiom-free `Definition`s whose value is the
/// canonical `<target>.ofNat (<source>.toNat x)`, and every reducer agrees with
/// its δ-unfolding at every sampled value.
#[test]
fn ws6_10_fixed_width_conversions_are_definitions_their_reducers_agree_with() {
    let env = Environment::with_prelude();
    for (source, target, _) in fixed_width_conversions() {
        let name = Name::from_string(&uint_conversion_name(source, target));
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} must be a Definition"
        );
        let deps = env.axiom_deps(&name).expect("registered above");
        assert!(deps.is_empty(), "{name} must be axiom-free, got {deps:?}");
        let Declaration::Definition { value, type_, .. } =
            Environment::uint_conversion_decl(source, target)
        else {
            panic!("uint_conversion_decl must build a Definition");
        };
        assert_eq!(info.value.as_ref(), Some(&value), "{name}: canonical body");
        assert_eq!(info.type_, type_, "{name}: canonical type");
    }
    let bad = reducer_disagreements(&env, &|s, t| registered_value(&env, s, t));
    assert!(bad.is_empty(), "reducer/definition disagreement: {bad:?}");
}

/// Mutation control: a WELL-TYPED definition that widens through `ofNat` of
/// the WRONG width (`UInt32.toUInt64 x := UInt64.ofNat (UInt16.toNat
/// (UInt16.ofNat (UInt32.toNat x)))`) is caught by the agreement check, and
/// only that conversion is named — so the check discriminates, and the
/// positive test above is not vacuous.
#[test]
fn ws6_10_wrong_width_widening_is_refused_by_reducer_agreement() {
    let env = Environment::with_prelude();
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let mutant = {
        let mut b = crate::env::decl_builder::EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(c("UInt32"));
        let narrowed = Expr::app(c("UInt16.ofNat"), Expr::app(c("UInt32.toNat"), x));
        let body = Expr::app(c("UInt64.ofNat"), Expr::app(c("UInt16.toNat"), narrowed));
        let e = b.mk_lam(x_id, BinderInfo::Default, c("UInt32"), body);
        b.finish(e)
    };
    // The mutant is a well-typed `UInt32 → UInt64`: only the agreement check
    // can refuse it, not the type checker.
    let tc = crate::tc::TypeChecker::with_mode(&env, env.mode());
    tc.check_type(
        &mutant,
        &Expr::pi(BinderInfo::Default, c("UInt32"), c("UInt64")),
    )
    .expect("the mutant must be well-typed");
    drop(tc);

    let bad = reducer_disagreements(&env, &|s, t| {
        if (s, t) == ("UInt32", "UInt64") {
            mutant.clone()
        } else {
            registered_value(&env, s, t)
        }
    });
    assert!(
        bad.iter()
            .any(|m| m == "UInt32.toUInt64(70000): reducer 70000"),
        "the wrong-width widening must be named at 70000, got {bad:?}"
    );
    assert!(
        bad.iter().all(|m| m.starts_with("UInt32.toUInt64(")),
        "only the mutated conversion may be named, got {bad:?}"
    );
}

/// The eight `USize` conversions keep their reducers but gain NO constant: the
/// native prelude has no platform-width-bound `USize.ofNat` to define them by.
#[test]
fn ws6_10_usize_conversions_stay_undefined() {
    let env = Environment::with_prelude();
    for name in [
        &*names::USIZE_TO_UINT8,
        &*names::USIZE_TO_UINT16,
        &*names::USIZE_TO_UINT32,
        &*names::USIZE_TO_UINT64,
        &*names::UINT8_TO_USIZE,
        &*names::UINT16_TO_USIZE,
        &*names::UINT32_TO_USIZE,
        &*names::UINT64_TO_USIZE,
    ] {
        assert!(
            env.get_const(name).is_none(),
            "{name} must stay undefined until USize's width is bound"
        );
        assert!(
            env.get_native_reducer(name).is_some(),
            "{name} reducer kept"
        );
    }
    assert_eq!(FIXED_WIDTH_UINTS.len() * (FIXED_WIDTH_UINTS.len() - 1), 12);
}
