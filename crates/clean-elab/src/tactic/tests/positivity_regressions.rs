// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for positivity tactic classification (#2985).
//!
//! Covers all addition and multiplication (PositivityResult, PositivityResult)
//! combinations to prevent future regressions in analyze_positivity.

use super::*;
use crate::tactic::positivity::{self, PositivityResult};
use crate::tactic::tc_app;

fn nat_hadd(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::mk_tc_hbinop(
        Expr::const_(Name::from_string("HAdd.hAdd"), vec![]),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_arith_inst("HAdd.hAdd"),
        lhs,
        rhs,
    )
}

fn nat_hmul(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::mk_tc_hbinop(
        Expr::const_(Name::from_string("HMul.hMul"), vec![]),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_type(),
        tc_app::nat_arith_inst("HMul.hMul"),
        lhs,
        rhs,
    )
}

/// Helper: expression that analyze_positivity classifies as Positive (Nat.one)
fn positive_expr() -> Expr {
    Expr::const_(Name::from_string("Nat.one"), vec![])
}

/// Helper: expression that analyze_positivity classifies as NonNegative (nat lit 0)
fn nonneg_expr() -> Expr {
    Expr::nat_lit(0)
}

/// Helper: expression that analyze_positivity classifies as Unknown (free var)
fn unknown_expr() -> Expr {
    Expr::const_(Name::from_string("x"), vec![])
}

// ── Addition classification ──────────────────────────────────────────

#[test]
fn test_add_positive_positive_is_positive() {
    let result = positivity::analyze_positivity(&nat_hadd(positive_expr(), positive_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Positive),
        "positive + positive should be Positive, got: {result:?}"
    );
}

#[test]
fn test_add_positive_nonnegative_is_positive() {
    let result = positivity::analyze_positivity(&nat_hadd(positive_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Positive),
        "positive + nonnegative should be Positive, got: {result:?}"
    );
}

#[test]
fn test_add_nonnegative_positive_is_positive() {
    let result = positivity::analyze_positivity(&nat_hadd(nonneg_expr(), positive_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Positive),
        "nonnegative + positive should be Positive, got: {result:?}"
    );
}

#[test]
fn test_add_nonnegative_nonnegative_is_nonnegative() {
    let result = positivity::analyze_positivity(&nat_hadd(nonneg_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::NonNegative),
        "nonnegative + nonnegative should be NonNegative, got: {result:?}"
    );
}

#[test]
fn test_add_positive_unknown_stays_unknown() {
    let result = positivity::analyze_positivity(&nat_hadd(positive_expr(), unknown_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Unknown),
        "positive + unknown must stay Unknown (soundness), got: {result:?}"
    );
}

#[test]
fn test_add_unknown_nonnegative_stays_unknown() {
    let result = positivity::analyze_positivity(&nat_hadd(unknown_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Unknown),
        "unknown + nonnegative must stay Unknown (soundness), got: {result:?}"
    );
}

// ── Multiplication classification ────────────────────────────────────

#[test]
fn test_mul_positive_positive_is_positive() {
    let result = positivity::analyze_positivity(&nat_hmul(positive_expr(), positive_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Positive),
        "positive * positive should be Positive, got: {result:?}"
    );
}

#[test]
fn test_mul_positive_nonnegative_is_nonnegative() {
    let result = positivity::analyze_positivity(&nat_hmul(positive_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::NonNegative),
        "positive * nonnegative should be NonNegative (not Unknown), got: {result:?}"
    );
}

#[test]
fn test_mul_nonnegative_positive_is_nonnegative() {
    let result = positivity::analyze_positivity(&nat_hmul(nonneg_expr(), positive_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::NonNegative),
        "nonnegative * positive should be NonNegative (not Unknown), got: {result:?}"
    );
}

#[test]
fn test_mul_nonnegative_nonnegative_is_nonnegative() {
    let result = positivity::analyze_positivity(&nat_hmul(nonneg_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::NonNegative),
        "nonnegative * nonnegative should be NonNegative, got: {result:?}"
    );
}

#[test]
fn test_mul_positive_unknown_stays_unknown() {
    let result = positivity::analyze_positivity(&nat_hmul(positive_expr(), unknown_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Unknown),
        "positive * unknown must stay Unknown (soundness), got: {result:?}"
    );
}

#[test]
fn test_mul_unknown_nonnegative_stays_unknown() {
    let result = positivity::analyze_positivity(&nat_hmul(unknown_expr(), nonneg_expr()))
        .expect("analysis should run");
    assert!(
        matches!(result, PositivityResult::Unknown),
        "unknown * nonnegative must stay Unknown (soundness), got: {result:?}"
    );
}
