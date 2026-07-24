// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MData transparency tests (Prover P1-795, proof_coverage).

use super::*;
use clean_kernel::Expr;

/// Test that MData-wrapped expressions translate identically to unwrapped.
///
/// `translate_expr_inner` (translate.rs:40) transparently unwraps MData.
/// MData is common in real .olean files (compiler annotations, source positions).
/// Previously untested — Prover P1 iter 795.
#[test]
fn test_mdata_transparent_unwrap() {
    use clean_kernel::name::Name;
    use clean_kernel::MDataValue;

    let mut backend = AyBackend::new(AyLogic::QfLia);

    let fvar_id = FVarId::new(100);
    backend.register_fvar_int(fvar_id);

    // Translate bare FVar
    let bare = Expr::fvar(fvar_id);
    let bare_term = backend
        .translate_expr(&bare)
        .expect("bare FVar should translate");

    // Wrap the same FVar in MData
    let metadata = vec![(Name::from_string("source_pos"), MDataValue::Nat(42))];
    let wrapped = Expr::mdata(metadata, Expr::fvar(fvar_id));
    let wrapped_term = backend
        .translate_expr(&wrapped)
        .expect("MData-wrapped FVar should translate");

    // Both should produce the same ay term
    assert_eq!(
        bare_term, wrapped_term,
        "MData wrapping should be transparent: bare FVar and MData(FVar) must produce identical ay terms"
    );
}

/// Test that MData-wrapped Nat literals translate correctly.
///
/// Exercises MData transparency for literal expressions, verifying the
/// unwrap doesn't lose the literal value.
/// Previously untested — Prover P1 iter 795.
#[test]
fn test_mdata_wrapped_literal_translates() {
    use clean_kernel::name::Name;
    use clean_kernel::MDataValue;

    let mut backend = AyBackend::new(AyLogic::QfLia);

    // Translate bare literal
    let bare = Expr::nat_lit(42);
    let bare_term = backend
        .translate_expr(&bare)
        .expect("bare literal should translate");

    // Wrap in MData
    let metadata = vec![(Name::from_string("pp_numeral"), MDataValue::Bool(true))];
    let wrapped = Expr::mdata(metadata, Expr::nat_lit(42));
    let wrapped_term = backend
        .translate_expr(&wrapped)
        .expect("MData-wrapped literal should translate");

    assert_eq!(
        bare_term, wrapped_term,
        "MData wrapping should be transparent for literals"
    );
}

/// Test that MData-wrapped expressions interact correctly with the
/// expression cache in `translate_expr`.
///
/// The cache uses `Expr` as key. Since `MData(_, e)` != `e` structurally,
/// a cache hit on `e` should NOT match `MData(_, e)`. This test verifies
/// that both paths produce correct results despite different cache behavior.
/// Previously untested — Prover P1 iter 795.
#[test]
fn test_mdata_cache_interaction() {
    use clean_kernel::name::Name;
    use clean_kernel::MDataValue;

    let mut backend = AyBackend::new(AyLogic::QfLia);

    let fvar_id = FVarId::new(200);
    backend.register_fvar_int(fvar_id);

    // First call: cache miss, translates bare FVar
    let bare = Expr::fvar(fvar_id);
    let t1 = backend.translate_expr(&bare).expect("first translate");

    // Second call: cache hit for bare FVar
    let t2 = backend.translate_expr(&bare).expect("cached translate");
    assert_eq!(t1, t2, "cached result should match");

    // Third call: MData-wrapped — may or may not hit cache depending
    // on whether the cache key is the outer MData or the unwrapped inner
    let metadata = vec![(Name::from_string("info"), MDataValue::Bool(false))];
    let wrapped = Expr::mdata(metadata, Expr::fvar(fvar_id));
    let t3 = backend.translate_expr(&wrapped).expect("MData translate");
    assert_eq!(
        t1, t3,
        "MData-wrapped expression must produce same ay term as bare"
    );
}

/// Regression (#2261): MData on function head inside App spine should be transparent.
///
/// When `get_app_fn()` returns `MData(_, Const("And"))`, `translate_app` must
/// strip the MData to recognize the head as a Const for dispatch to classify_expr.
#[test]
fn test_translate_app_mdata_on_head_in_app_spine() {
    use clean_kernel::name::Name;
    use clean_kernel::MDataValue;

    let mut backend = AyBackend::new(AyLogic::QfLia);

    let a_id = FVarId::new(300);
    let b_id = FVarId::new(301);
    backend.register_fvar_bool(a_id);
    backend.register_fvar_bool(b_id);

    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);

    // Build And(a, b) with MData wrapping the And constant inside the App spine:
    // App(App(MData(_, Const("And")), a), b)
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let metadata = vec![(Name::from_string("simp"), MDataValue::Bool(true))];
    let mdata_and = Expr::mdata(metadata, and_const);

    let mdata_app = Expr::app(Expr::app(mdata_and, a.clone()), b.clone());

    // This should succeed — the MData on the head should be stripped
    let result = backend.translate_expr(&mdata_app);
    assert!(
        result.is_ok(),
        "MData on App head should be transparent: {:?}",
        result.err()
    );
}
