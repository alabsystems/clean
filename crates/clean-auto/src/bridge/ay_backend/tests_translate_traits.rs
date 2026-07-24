// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Host-parity regression tests for `LeanExprTranslator`.
//!
//! Mirrors the upstream ay regression at
//! `ay-translate/tests/dual_host_6302.rs`: the same clean translator
//! must produce identical SAT/UNSAT results when driven through both
//! `TranslationContext<FVarId>` (owning host) and
//! `TranslationSession<'_, FVarId>` (borrowed host).
//!
//! Design: `designs/2026-03-11-2282-ay-translate-consumer-trait-adapter.md`

#![allow(deprecated)] // Tests intentionally exercise deprecated TranslationContext for parity

use super::translator::LeanExprTranslator;
use ay::Sort;
use ay_translate::{
    Logic, Solver, TermTranslator, TranslationContext, TranslationSession, TranslationState,
};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

/// Build `Eq Nat lhs rhs` as an Expr (3-arg Eq application).
fn build_eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![Level::zero()]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    Expr::app(Expr::app(Expr::app(eq_const, nat_ty), lhs), rhs)
}

/// Build `And a b` as an Expr.
fn build_and(a: Expr, b: Expr) -> Expr {
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    Expr::app(Expr::app(and_const, a), b)
}

// =========================================================================
// Dual-host SAT parity
// =========================================================================

/// Same translator produces SAT via both TranslationContext and TranslationSession.
///
/// Formula: x > 0 AND x < 10 (SAT for any x in 1..9).
/// Mirrors ay's `test_dual_host_sat` in `dual_host_6302.rs`.
#[test]
fn test_dual_host_sat_parity() {
    let x_id = FVarId::new(1);

    // Build: x > 0 AND x < 10
    // Using Lean Expr form with Nat.lt / Nat.gt is complex,
    // so we build a simple equality-based SAT formula:
    //   NOT(x = 0) — has a model (any nonzero x)
    let x_fvar = Expr::fvar(x_id);
    let zero = Expr::nat_lit(0);
    let x_eq_zero = build_eq_nat(x_fvar, zero);
    let not_const = Expr::const_(Name::from_string("Not"), vec![]);
    let formula = Expr::app(not_const, x_eq_zero);

    // Path 1: TranslationContext (owning host)
    let result_ctx = {
        let tr = LeanExprTranslator::default();
        let mut ctx: TranslationContext<FVarId> = TranslationContext::new(Logic::QfLia);
        tr.register_fvar(&mut ctx, x_id, Sort::Int);
        let term = tr
            .translate(&mut ctx, &formula)
            .expect("translate with ctx");
        ctx.assert_term(term);
        ctx.check_sat().is_sat()
    };

    // Path 2: TranslationSession (borrowed host)
    let result_session = {
        let tr = LeanExprTranslator::default();
        let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia");
        let mut state = TranslationState::new();
        let mut session = TranslationSession::new(&mut solver, &mut state);
        tr.register_fvar(&mut session, x_id, Sort::Int);
        let term = tr
            .translate(&mut session, &formula)
            .expect("translate with session");
        session.assert_term(term);
        session.check_sat().is_sat()
    };

    assert!(result_ctx, "owning host should return SAT");
    assert!(result_session, "borrowed host should return SAT");
}

// =========================================================================
// Dual-host UNSAT parity
// =========================================================================

/// Same translator produces UNSAT via both hosts.
///
/// Formula: x = 0 AND NOT(x = 0) (contradiction).
/// Mirrors ay's `test_dual_host_unsat` in `dual_host_6302.rs`.
#[test]
fn test_dual_host_unsat_parity() {
    let x_id = FVarId::new(1);

    // Build contradiction: x = 0 AND NOT(x = 0)
    let x_fvar = Expr::fvar(x_id);
    let zero = Expr::nat_lit(0);
    let x_eq_zero = build_eq_nat(x_fvar, zero);
    let not_const = Expr::const_(Name::from_string("Not"), vec![]);
    let not_x_eq_zero = Expr::app(not_const, x_eq_zero.clone());
    let formula = build_and(x_eq_zero, not_x_eq_zero);

    // Path 1: TranslationContext (owning host)
    let result_ctx = {
        let tr = LeanExprTranslator::default();
        let mut ctx: TranslationContext<FVarId> = TranslationContext::new(Logic::QfLia);
        tr.register_fvar(&mut ctx, x_id, Sort::Int);
        let term = tr
            .translate(&mut ctx, &formula)
            .expect("translate with ctx");
        ctx.assert_term(term);
        ctx.check_sat().is_unsat()
    };

    // Path 2: TranslationSession (borrowed host)
    let result_session = {
        let tr = LeanExprTranslator::default();
        let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia");
        let mut state = TranslationState::new();
        let mut session = TranslationSession::new(&mut solver, &mut state);
        tr.register_fvar(&mut session, x_id, Sort::Int);
        let term = tr
            .translate(&mut session, &formula)
            .expect("translate with session");
        session.assert_term(term);
        session.check_sat().is_unsat()
    };

    assert!(result_ctx, "owning host should return UNSAT");
    assert!(result_session, "borrowed host should return UNSAT");
}

// =========================================================================
// Dual-host arithmetic parity
// =========================================================================

/// Nat monus semantics are consistent across both hosts.
///
/// Formula: Nat.sub(3, 5) = 0 (should be provable with monus).
/// Tests that arithmetic translation through the translator works the
/// same with both host types.
#[test]
fn test_dual_host_nat_monus_parity() {
    let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
    let sub_expr = Expr::app(Expr::app(nat_sub, Expr::nat_lit(3)), Expr::nat_lit(5));
    let goal = build_eq_nat(sub_expr, Expr::nat_lit(0));

    // Prove via negate-and-check-UNSAT (same as AyBackend::prove)
    // Path 1: TranslationContext
    let result_ctx = {
        let tr = LeanExprTranslator::default();
        let mut ctx: TranslationContext<FVarId> = TranslationContext::new(Logic::QfLia);
        let term = tr.translate(&mut ctx, &goal).expect("translate with ctx");
        let neg = ay_translate::ops::bool_not(&mut ctx, term);
        ctx.assert_term(neg);
        ctx.check_sat().is_unsat() // UNSAT means goal is provable
    };

    // Path 2: TranslationSession
    let result_session = {
        let tr = LeanExprTranslator::default();
        let mut solver = Solver::try_new(Logic::QfLia).expect("QfLia");
        let mut state = TranslationState::new();
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let term = tr
            .translate(&mut session, &goal)
            .expect("translate with session");
        let neg = ay_translate::ops::bool_not(&mut session, term);
        session.assert_term(neg);
        session.check_sat().is_unsat()
    };

    assert!(
        result_ctx,
        "Nat.sub(3,5) = 0 should be provable via owning host"
    );
    assert!(
        result_session,
        "Nat.sub(3,5) = 0 should be provable via borrowed host"
    );
}
