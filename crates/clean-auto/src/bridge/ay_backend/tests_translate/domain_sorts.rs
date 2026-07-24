// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FuncDecl cache domain sort consistency tests (#2265).

use super::support::build_fvar_app;
use super::*;
use clean_kernel::Expr;

/// Test that FVar applied with different argument sorts at two call sites
/// is rejected (#2265).
///
/// Scenario: f is first seen as f(x : Int) → declares FuncDecl { domain: [Sort::Int] }.
/// Second call f(y : Bool) has arity 1 (passes arity check) but Sort::Bool != Sort::Int.
/// Before the fix, this silently produced a malformed ay term in release builds
/// because ay's apply() only checks sorts via debug_assert.
#[test]
fn test_fvar_app_domain_sort_mismatch_rejected() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);

    // f : Bool (registered sort used as UF return type)
    // x : Int, y : Bool
    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_bool(y_id);

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    // First call: f(x) where x : Int → declares FuncDecl { domain: [Sort::Int] }
    let fx = build_fvar_app(f_id, &[x]);
    backend
        .translate_expr(&fx)
        .expect("f(x : Int) should translate");

    // Second call: f(y) where y : Bool → arity matches but domain sort doesn't
    let fy = build_fvar_app(f_id, &[y]);
    let result = backend.translate_expr(&fy);
    assert!(
        result.is_err(),
        "f(y : Bool) reusing f's FuncDecl(domain=[Int]) should be rejected"
    );

    // Verify the error is a TypeMismatch, not UnsupportedExpr
    let err = result.expect_err("f(y : Bool) should produce an error");
    assert!(
        matches!(&err, AyError::TypeMismatch { expected, got }
            if expected.contains("domain sort") && got.contains("Bool")),
        "expected TypeMismatch mentioning domain sort and Bool, got: {err:?}"
    );
}

/// Test that FVar applied with consistent sorts at two call sites succeeds (#2265).
///
/// Complement test: f(x : Int) followed by f(z : Int) should both translate
/// successfully since domain sorts are consistent.
#[test]
fn test_fvar_app_domain_sort_consistent_succeeds() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let z_id = FVarId::new(40);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_int(z_id);

    let x = Expr::fvar(x_id);
    let z = Expr::fvar(z_id);

    // First call: f(x : Int) — declares FuncDecl { domain: [Sort::Int] }
    let fx = build_fvar_app(f_id, &[x]);
    backend
        .translate_expr(&fx)
        .expect("f(x : Int) should translate");

    // Second call: f(z : Int) — same domain sort, should succeed
    let fz = build_fvar_app(f_id, &[z]);
    backend
        .translate_expr(&fz)
        .expect("f(z : Int) should translate (consistent domain sorts)");
}

/// Test multi-arity domain sort mismatch: f(x : Int, y : Int) then f(a : Int, b : Bool) (#2265).
///
/// Second argument sort differs. Arity check passes (both arity 2), but
/// domain[1] = Sort::Int vs actual Sort::Bool should be caught.
#[test]
fn test_fvar_app_multi_arity_domain_sort_mismatch() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);
    let a_id = FVarId::new(40);
    let b_id = FVarId::new(50);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_int(y_id);
    backend.register_fvar_int(a_id);
    backend.register_fvar_bool(b_id);

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);
    let a = Expr::fvar(a_id);
    let b = Expr::fvar(b_id);

    // First call: f(x : Int, y : Int) → declares FuncDecl { domain: [Int, Int] }
    let fxy = build_fvar_app(f_id, &[x, y]);
    backend
        .translate_expr(&fxy)
        .expect("f(Int, Int) should translate");

    // Second call: f(a : Int, b : Bool) → domain[1] mismatch
    let fab = build_fvar_app(f_id, &[a, b]);
    let result = backend.translate_expr(&fab);
    assert!(
        result.is_err(),
        "f(Int, Bool) reusing f's FuncDecl(domain=[Int, Int]) should be rejected"
    );
}
