// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real lowering tests for the native ay translator (#2794, #2796, #2800).
//!
//! Verifies that constructor-form `Real.ofNat` / `Real.ofInt`, direct
//! `Real.add` / `Real.sub` / `Real.mul`, and direct `Real.lt` / `Real.le`
//! expressions translate correctly, and that unsupported non-concrete inputs
//! fail closed where required.

use super::support::build_h_binop;
use super::*;
use clean_kernel::name::Name;
use clean_kernel::Expr;

fn real_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn real_of_int_neg_succ(n: u64) -> Expr {
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    );
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn real_lt(lhs: Expr, rhs: Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let inst = Expr::const_(Name::from_string("instLTReal"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("LT.lt"), vec![]), real_ty),
                inst,
            ),
            lhs,
        ),
        rhs,
    )
}

fn real_lt_direct(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.lt"), vec![]), lhs),
        rhs,
    )
}

fn real_le_direct(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.le"), vec![]), lhs),
        rhs,
    )
}

fn real_eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![]),
                Expr::const_(Name::from_string("Real"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

#[test]
fn test_real_ofnat_concrete_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofNat(3)
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(3),
    );
    let term = backend
        .translate_expr(&expr)
        .expect("Real.ofNat(3) should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.ofNat(3) should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_ofnat_zero_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofNat(0)
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    let term = backend
        .translate_expr(&expr)
        .expect("Real.ofNat(0) should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.ofNat(0) should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_ofint_positive_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofInt(Int.ofNat(5))
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(5),
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    );
    let term = backend
        .translate_expr(&expr)
        .expect("Real.ofInt(Int.ofNat(5)) should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.ofInt(Int.ofNat(5)) should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_ofint_negative_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofInt(Int.negSucc(0)) = Real(-1)
    let int_expr = Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(0),
    );
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    );
    let term = backend
        .translate_expr(&expr)
        .expect("Real.ofInt(Int.negSucc(0)) should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.ofInt(Int.negSucc(0)) should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_ofnat_non_concrete_fails_closed() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofNat(fvar) — non-concrete, must fail
    let fvar_id = FVarId::new(42);
    backend.register_fvar_int(fvar_id);
    let fvar = Expr::fvar(fvar_id);
    let expr = Expr::app(Expr::const_(Name::from_string("Real.ofNat"), vec![]), fvar);
    assert!(
        backend.translate_expr(&expr).is_err(),
        "Real.ofNat with non-concrete argument should fail"
    );
}

#[test]
fn test_real_ofint_non_concrete_fails_closed() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofInt(fvar) — non-concrete, must fail
    let fvar_id = FVarId::new(42);
    backend.register_fvar_int(fvar_id);
    let fvar = Expr::fvar(fvar_id);
    let expr = Expr::app(Expr::const_(Name::from_string("Real.ofInt"), vec![]), fvar);
    assert!(
        backend.translate_expr(&expr).is_err(),
        "Real.ofInt with non-concrete argument should fail"
    );
}

#[test]
fn test_real_ofint_with_bare_nat_lit_produces_real() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.ofInt(NatLit(7)) — bare Nat literal as non-negative Int
    let expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        Expr::nat_lit(7),
    );
    let term = backend
        .translate_expr(&expr)
        .expect("Real.ofInt(NatLit(7)) should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.ofInt(NatLit(7)) should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_lt_with_constructor_endpoints_translates_to_bool() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    let expr = real_lt(real_of_nat(0), real_of_nat(1));
    let term = backend
        .translate_expr(&expr)
        .expect("Real constructor comparison should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_bool(),
        "Real constructor comparison should produce Bool sort, got: {sort:?}"
    );
}

#[test]
fn test_real_lt_with_registered_real_fvar_and_constructor_bound_translates() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let x_id = FVarId::new(77);
    backend.register_fvar_real(x_id);

    let expr = real_lt(Expr::fvar(x_id), real_of_int_neg_succ(0));
    let term = backend
        .translate_expr(&expr)
        .expect("Real FVar comparison against constructor bound should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_bool(),
        "Real FVar comparison should produce Bool sort, got: {sort:?}"
    );
}

#[test]
fn test_direct_real_lt_with_constructor_endpoints_translates() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    let expr = real_lt_direct(real_of_nat(0), real_of_nat(1));
    let term = backend
        .translate_expr(&expr)
        .expect("direct Real.lt constructor comparison should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_bool(),
        "direct Real.lt comparison should produce Bool sort, got: {sort:?}"
    );
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "direct Real.lt should lower to a satisfiable arithmetic comparison"
    );
}

#[test]
fn test_direct_real_le_with_constructor_endpoints_translates() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    let expr = real_le_direct(real_of_int_neg_succ(0), real_of_nat(0));
    let term = backend
        .translate_expr(&expr)
        .expect("direct Real.le constructor comparison should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_bool(),
        "direct Real.le comparison should produce Bool sort, got: {sort:?}"
    );
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "direct Real.le should lower to a satisfiable arithmetic comparison"
    );
}

// ===================================================================
// Real division — exact constant-denominator only (#2795)
// ===================================================================

/// Build `Real.div lhs rhs` — direct Real division.
fn real_div(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.div"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_hdiv_real_concrete_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // HDiv.hDiv Real Real Real inst (Real.ofNat 6) (Real.ofNat 2) → Real-sorted term
    let expr = build_h_binop("HDiv.hDiv", "Real", real_of_nat(6), real_of_nat(2));
    let term = backend
        .translate_expr(&expr)
        .expect("HDiv.hDiv Real with concrete divisor should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "HDiv.hDiv Real with concrete divisor should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_div_direct_concrete_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // Real.div (Real.ofNat 6) (Real.ofNat 2) → Real-sorted term
    let expr = real_div(real_of_nat(6), real_of_nat(2));
    let term = backend
        .translate_expr(&expr)
        .expect("Real.div with concrete divisor should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.div with concrete divisor should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_hdiv_real_symbolic_denominator_fails_closed() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let x_id = FVarId::new(88);
    backend.register_fvar_real(x_id);

    // HDiv.hDiv Real Real Real inst (Real.ofNat 1) fvar → error (symbolic denominator)
    let expr = build_h_binop("HDiv.hDiv", "Real", real_of_nat(1), Expr::fvar(x_id));
    assert!(
        backend.translate_expr(&expr).is_err(),
        "HDiv.hDiv Real with symbolic denominator should fail closed"
    );
}

#[test]
fn test_real_div_direct_symbolic_denominator_fails_closed() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let x_id = FVarId::new(88);
    backend.register_fvar_real(x_id);

    // Real.div (Real.ofNat 3) fvar → error (symbolic denominator)
    let expr = real_div(real_of_nat(3), Expr::fvar(x_id));
    assert!(
        backend.translate_expr(&expr).is_err(),
        "Real.div with symbolic denominator should fail closed"
    );
}

#[test]
fn test_hdiv_real_nat_literal_denominator_produces_real() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    // HDiv.hDiv Real Real Real inst (Real.ofNat 5) (NatLit 2) → Real-sorted
    let expr = build_h_binop("HDiv.hDiv", "Real", real_of_nat(5), Expr::nat_lit(2));
    let term = backend
        .translate_expr(&expr)
        .expect("HDiv.hDiv Real with Nat literal denominator should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "HDiv.hDiv Real with Nat literal denominator should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_rat_smt_hdiv_rat_concrete_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);

    let expr = build_h_binop(
        "HDiv.hDiv",
        "Rat",
        Expr::const_(Name::from_string("Rat.one"), vec![]),
        Expr::nat_lit(2),
    );
    let term = backend
        .translate_expr(&expr)
        .expect("HDiv.hDiv Rat with concrete divisor should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "HDiv.hDiv Rat with concrete divisor should produce Real sort, got: {sort:?}"
    );
}

// --- Direct Real.add / Real.sub / Real.mul tests (#2796) ---

/// Build `Real.add lhs rhs` (direct 2-arg form).
fn real_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.add"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.sub lhs rhs` (direct 2-arg form).
fn real_sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.sub"), vec![]), lhs),
        rhs,
    )
}

/// Build `Real.mul lhs rhs` (direct 2-arg form).
fn real_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Real.mul"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_real_add_direct_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_add(real_of_nat(3), real_of_nat(5));
    let term = backend
        .translate_expr(&expr)
        .expect("Real.add should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.add should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_add_direct_preserves_ground_value() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_eq(real_add(real_of_nat(2), real_of_nat(3)), real_of_nat(5));
    let term = backend
        .translate_expr(&expr)
        .expect("ground Real.add equality should translate");
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "Real.add should lower to arithmetic addition on the native solver path"
    );
}

#[test]
fn test_real_sub_direct_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_sub(real_of_nat(7), real_of_nat(2));
    let term = backend
        .translate_expr(&expr)
        .expect("Real.sub should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.sub should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_sub_direct_preserves_ground_value() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_eq(real_sub(real_of_nat(7), real_of_nat(2)), real_of_nat(5));
    let term = backend
        .translate_expr(&expr)
        .expect("ground Real.sub equality should translate");
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "Real.sub should lower to arithmetic subtraction on the native solver path"
    );
}

#[test]
fn test_real_mul_direct_produces_real_sort() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_mul(real_of_nat(4), real_of_nat(6));
    let term = backend
        .translate_expr(&expr)
        .expect("Real.mul should translate");
    let sort = backend.solver.term_sort(term.into_inner());
    assert!(
        sort.is_real(),
        "Real.mul should produce Real sort, got: {sort:?}"
    );
}

#[test]
fn test_real_mul_direct_preserves_ground_value() {
    let mut backend = AyBackend::new(AyLogic::QfLra);
    let expr = real_eq(real_mul(real_of_nat(2), real_of_nat(3)), real_of_nat(6));
    let term = backend
        .translate_expr(&expr)
        .expect("ground Real.mul equality should translate");
    backend.assert_term(term);
    assert_eq!(
        backend.check_sat(),
        AySolveResult::Sat,
        "Real.mul should lower to arithmetic multiplication on the native solver path"
    );
}
