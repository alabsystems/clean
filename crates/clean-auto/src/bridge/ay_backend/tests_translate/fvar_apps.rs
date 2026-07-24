// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FVar application congruence tests (#2249).

use super::support::build_fvar_app;
use super::*;
use clean_kernel::Expr;

/// Test that f(x) != f(y) is SAT when x != y (#2249)
///
/// Before the fix, f(x) and f(y) mapped to the same ay constant,
/// making f(x) = f(y) a tautology and f(x) != f(y) unsatisfiable.
/// With uninterpreted functions, f(x) != f(y) is satisfiable when x != y.
#[test]
fn test_fvar_app_distinct_args_not_conflated() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_int(y_id);

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    // Build f(x) and f(y) as FVar applications
    let fx = build_fvar_app(f_id, &[x]);
    let fy = build_fvar_app(f_id, &[y]);

    // Translate both
    let fx_term = backend.translate_expr(&fx).expect("f(x) should translate");
    let fy_term = backend.translate_expr(&fy).expect("f(y) should translate");

    // f(x) and f(y) should be different terms (not conflated)
    // Assert x != y and f(x) != f(y) — should be SAT
    let x_term = backend
        .translate_expr(&Expr::fvar(x_id))
        .expect("x should translate");
    let y_term = backend
        .translate_expr(&Expr::fvar(y_id))
        .expect("y should translate");
    let x_neq_y = backend.neq(x_term, y_term);
    let fx_neq_fy = backend.neq(fx_term, fy_term);
    backend.assert_term(x_neq_y);
    backend.assert_term(fx_neq_fy);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "f(x) != f(y) with x != y should be SAT (uninterpreted function)"
    );
}

/// Test that f(x) = f(x) is provable via congruence (#2249)
///
/// The EUF theory should recognize that f applied to the same argument
/// produces the same result. This verifies congruence closure works.
#[test]
fn test_fvar_app_same_args_congruent() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);

    let x = Expr::fvar(x_id);

    let fx1 = build_fvar_app(f_id, std::slice::from_ref(&x));
    let fx2 = build_fvar_app(f_id, std::slice::from_ref(&x));

    let fx1_term = backend.translate_expr(&fx1).expect("f(x) translate 1");
    let fx2_term = backend.translate_expr(&fx2).expect("f(x) translate 2");

    // Assert f(x) != f(x) — should be UNSAT (congruence)
    let fx_neq_fx = backend.neq(fx1_term, fx2_term);
    backend.assert_term(fx_neq_fx);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Unsat,
        "f(x) != f(x) should be UNSAT (congruence closure)"
    );
}

/// Test that x = y implies f(x) = f(y) via congruence (#2249)
///
/// This is the key property of uninterpreted functions: congruence axiom.
/// If x = y then f(x) = f(y). The solver should prove this automatically.
#[test]
fn test_fvar_app_congruence_axiom() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_int(y_id);

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    let fx = build_fvar_app(f_id, &[x]);
    let fy = build_fvar_app(f_id, &[y]);

    let x_term = backend
        .translate_expr(&Expr::fvar(x_id))
        .expect("x should translate");
    let y_term = backend
        .translate_expr(&Expr::fvar(y_id))
        .expect("y should translate");
    let fx_term = backend.translate_expr(&fx).expect("f(x) should translate");
    let fy_term = backend.translate_expr(&fy).expect("f(y) should translate");

    // Assert x = y AND f(x) != f(y) — should be UNSAT (violates congruence)
    let x_eq_y = backend.eq(x_term, y_term);
    let fx_neq_fy = backend.neq(fx_term, fy_term);
    backend.assert_term(x_eq_y);
    backend.assert_term(fx_neq_fy);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Unsat,
        "x = y AND f(x) != f(y) should be UNSAT (congruence axiom)"
    );
}

/// Regression for the #2386 benchmark path: opaque Lean types must stay in
/// the uninterpreted-sort lane when registering values and UF codomains as `A`
/// for `translate_fvar_app`.
#[test]
fn test_fvar_app_congruence_from_unknown_lean_types() {
    use clean_kernel::name::Name;

    let mut backend = AyBackend::new(AyLogic::QfUf);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // FVar-headed applications infer argument sorts from the translated args and
    // use the registered sort as the UF codomain.
    backend
        .register_fvar_from_lean_type(f_id, &a_ty)
        .expect("type A is opaque, not rejected");
    backend
        .register_fvar_from_lean_type(x_id, &a_ty)
        .expect("type A is opaque, not rejected");
    backend
        .register_fvar_from_lean_type(y_id, &a_ty)
        .expect("type A is opaque, not rejected");

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);
    let fx = build_fvar_app(f_id, std::slice::from_ref(&x));
    let fy = build_fvar_app(f_id, std::slice::from_ref(&y));

    let x_term = backend.translate_expr(&x).expect("x should translate");
    let y_term = backend.translate_expr(&y).expect("y should translate");
    let fx_term = backend.translate_expr(&fx).expect("f(x) should translate");
    let fy_term = backend.translate_expr(&fy).expect("f(y) should translate");

    assert_eq!(
        backend.solver.term_sort(x_term.into_inner()),
        Sort::Uninterpreted("A".to_string()),
        "opaque Lean value types should stay uninterpreted"
    );
    assert_eq!(
        backend.solver.term_sort(fx_term.into_inner()),
        Sort::Uninterpreted("A".to_string()),
        "opaque Lean function codomains should stay uninterpreted"
    );

    let x_eq_y = backend.eq(x_term, y_term);
    let fx_neq_fy = backend.neq(fx_term, fy_term);
    backend.assert_term(x_eq_y);
    backend.assert_term(fx_neq_fy);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Unsat,
        "opaque-type registration should preserve QF_UF congruence"
    );
}

/// Test that unregistered FVar in application head is rejected (#2249)
#[test]
fn test_fvar_app_unregistered_rejected() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);

    // Register x but NOT f
    backend.register_fvar_int(x_id);

    let x = Expr::fvar(x_id);
    let fx = build_fvar_app(f_id, &[x]);

    let result = backend.translate_expr(&fx);
    assert!(
        result.is_err(),
        "FVar application with unregistered head should be rejected"
    );
}

/// Test that FVar applied with different arities at different call sites is rejected (#2249)
///
/// If f is first seen as f(x) (arity 1), then f(x, y) (arity 2) should fail
/// rather than silently passing wrong arity to ay's apply() (which only checks
/// via debug_assert in debug builds).
#[test]
fn test_fvar_app_arity_mismatch_rejected() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x_id = FVarId::new(20);
    let y_id = FVarId::new(30);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x_id);
    backend.register_fvar_int(y_id);

    let x = Expr::fvar(x_id);
    let y = Expr::fvar(y_id);

    // First call: f(x) — declares arity-1 function
    let fx = build_fvar_app(f_id, std::slice::from_ref(&x));
    backend.translate_expr(&fx).expect("f(x) should translate");

    // Second call: f(x, y) — arity mismatch, should be rejected
    let fxy = build_fvar_app(f_id, &[x, y]);
    let result = backend.translate_expr(&fxy);
    assert!(
        result.is_err(),
        "FVar applied with different arity should be rejected"
    );
}

/// Test multi-arity FVar congruence: x1=y1 AND x2=y2 implies f(x1,x2)=f(y1,y2)
///
/// All existing congruence tests use arity-1 (single argument). This exercises
/// the argument translation loop in translate_fvar_app for 2+ arguments, which
/// is the common case for Lean FVars (curried applications flatten to multi-arg).
/// Regression test for P1 iter 794.
#[test]
fn test_fvar_app_multi_arity_congruence() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x1_id = FVarId::new(20);
    let x2_id = FVarId::new(21);
    let y1_id = FVarId::new(30);
    let y2_id = FVarId::new(31);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x1_id);
    backend.register_fvar_int(x2_id);
    backend.register_fvar_int(y1_id);
    backend.register_fvar_int(y2_id);

    let x1 = Expr::fvar(x1_id);
    let x2 = Expr::fvar(x2_id);
    let y1 = Expr::fvar(y1_id);
    let y2 = Expr::fvar(y2_id);

    // Build f(x1, x2) and f(y1, y2) — 2-argument FVar applications
    let fxx = build_fvar_app(f_id, &[x1, x2]);
    let fyy = build_fvar_app(f_id, &[y1, y2]);

    let x1_term = backend
        .translate_expr(&Expr::fvar(x1_id))
        .expect("x1 translate");
    let x2_term = backend
        .translate_expr(&Expr::fvar(x2_id))
        .expect("x2 translate");
    let y1_term = backend
        .translate_expr(&Expr::fvar(y1_id))
        .expect("y1 translate");
    let y2_term = backend
        .translate_expr(&Expr::fvar(y2_id))
        .expect("y2 translate");
    let fxx_term = backend
        .translate_expr(&fxx)
        .expect("f(x1,x2) should translate");
    let fyy_term = backend
        .translate_expr(&fyy)
        .expect("f(y1,y2) should translate");

    // Assert x1=y1 AND x2=y2 AND f(x1,x2) != f(y1,y2)
    // Should be UNSAT by multi-arity congruence axiom.
    let x1_eq_y1 = backend.eq(x1_term, y1_term);
    let x2_eq_y2 = backend.eq(x2_term, y2_term);
    let fxx_neq_fyy = backend.neq(fxx_term, fyy_term);
    backend.assert_term(x1_eq_y1);
    backend.assert_term(x2_eq_y2);
    backend.assert_term(fxx_neq_fyy);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Unsat,
        "x1=y1 AND x2=y2 AND f(x1,x2)!=f(y1,y2) should be UNSAT (multi-arity congruence)"
    );
}

/// Test multi-arity FVar application with distinct args is SAT
///
/// Complement to multi-arity congruence: when arguments differ, the results
/// can differ (uninterpreted function makes no assumptions about values).
#[test]
fn test_fvar_app_multi_arity_distinct_sat() {
    let mut backend = AyBackend::new(AyLogic::QfUflia);

    let f_id = FVarId::new(10);
    let x1_id = FVarId::new(20);
    let x2_id = FVarId::new(21);
    let y1_id = FVarId::new(30);

    backend.register_fvar_bool(f_id);
    backend.register_fvar_int(x1_id);
    backend.register_fvar_int(x2_id);
    backend.register_fvar_int(y1_id);

    let x1 = Expr::fvar(x1_id);
    let x2 = Expr::fvar(x2_id);
    let y1 = Expr::fvar(y1_id);

    // f(x1, x2) vs f(y1, x2) — first arg differs
    let fxx = build_fvar_app(f_id, &[x1, x2.clone()]);
    let fyx = build_fvar_app(f_id, &[y1, x2]);

    let x1_term = backend
        .translate_expr(&Expr::fvar(x1_id))
        .expect("x1 translate");
    let y1_term = backend
        .translate_expr(&Expr::fvar(y1_id))
        .expect("y1 translate");
    let fxx_term = backend.translate_expr(&fxx).expect("f(x1,x2) translate");
    let fyx_term = backend.translate_expr(&fyx).expect("f(y1,x2) translate");

    // x1 != y1 AND f(x1,x2) != f(y1,x2) — should be SAT
    let x1_neq_y1 = backend.neq(x1_term, y1_term);
    let fxx_neq_fyx = backend.neq(fxx_term, fyx_term);
    backend.assert_term(x1_neq_y1);
    backend.assert_term(fxx_neq_fyx);

    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "f(x1,x2) != f(y1,x2) with x1!=y1 should be SAT (UF makes no value assumptions)"
    );
}
