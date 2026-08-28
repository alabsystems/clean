// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for calc block elaboration (`elab_calc.rs`).
//!
//! Covers: single-step calc, empty calc error, multi-step trans chaining,
//! and mixed-relation chain dispatch (LE+LT, EQ+LE, etc.).
//! Uses `Environment::with_prelude()` so that `Eq`, `Trans.trans`, etc. are
//! declared in the environment (#1795).

use super::*;
use clean_kernel::Level;

fn const_head_name(expr: &Expr) -> Option<String> {
    match expr.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn infer_expr_type_with_prelude(input: &str) -> Expr {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr(input).expect("expression should parse");
    let expr = ctx
        .elaborate(&surface)
        .expect("expression should elaborate with prelude");
    ctx.infer_type(&expr)
        .expect("expression type should infer with prelude")
}

fn pi_body_const_head_name(expr: &Expr) -> Option<String> {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        current = body;
    }
    const_head_name(current)
}

/// Single-step calc block: `calc a = a := rfl`
///
/// With one step, elab_calc returns the step's proof directly (no Trans.trans).
/// We verify:
///   1. Elaboration succeeds (no panic, no error)
///   2. Result is an expression (the proof term)
#[test]
fn test_elab_calc_single_step_succeeds() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "calc Bool.true = Bool.true := rfl")
        .expect("calc single step should elaborate with prelude");
    assert_eq!(
        const_head_name(&expr).as_deref(),
        Some("rfl"),
        "single-step calc should elaborate to bare rfl, got {expr:?}"
    );
}

/// Empty calc block should return a clear error, not panic.
///
/// Tests the guard at elab_calc.rs:33-35.
#[test]
fn test_elab_calc_empty_steps_returns_error() {
    // We can't parse an empty calc block via the parser (it requires at least
    // one step), so we construct the AST directly and call elab_calc.
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elab_calc(&[]);
    assert!(result.is_err(), "empty calc should return Err");
    let err = result.unwrap_err();
    let msg = format!("{err:?}");
    assert!(
        msg.contains("empty calc block"),
        "error should mention 'empty calc block', got: {msg}"
    );
}

/// Two-step calc block chains through `mk_calc_trans`.
///
/// `calc Type = Type := rfl; _ = Type := rfl`
///
/// With two steps, `elab_calc` calls `mk_calc_trans`; for an eq/eq chain the
/// `Trans Eq Eq` instance is `Eq.trans`, which is what the dispatch test above
/// pins and what this chain must produce. We verify:
///   1. Elaboration succeeds (see the note in the body — it did not, before
///      the 2026-08-22 hole-universe repair)
///   2. The head of the result is `Eq.trans`
#[test]
fn test_elab_calc_two_step_trans_chain() {
    let env = Environment::with_prelude();
    let result = elab_with_env(&env, "calc Type = Type := rfl; _ = Type := rfl");
    // UPDATED 2026-08-22 (U2 hole-universe repair). This test used to accept an
    // error branch too, on the stated grounds that "two-step calc requires
    // Trans.trans with correct universe levels [and] a TypeMismatch (universe
    // level conflict) ... is acceptable". Measured at origin/main `51c893ce5`,
    // that is the branch it was passing on:
    //
    //     Err(TypeMismatch { expected: "FVar(9223372036854775811)",
    //                        actual: "universe level conflict: 0 vs 2" })
    //
    // and the conflict was not intrinsic to `calc` at all — it was the `_` in
    // the second step meeting `elab_hole`'s hardcoded `Sort 1` hole type, the
    // same defect as `tests/fixtures/universes/p37_hole_universe_polymorphic.lean`
    // wearing a third face. With that literal replaced by a fresh level
    // metavariable the chain elaborates, so the error branch is now
    // unreachable and accepting it would only re-hide the bug.
    //
    // The head is `Eq.trans`, not `Trans.trans`, and that is correct rather
    // than a near miss: `Trans Eq Eq` reduces to `Eq.trans` in Lean, and
    // Clean's own dispatch table says so — `test_calc_elab_dispatch_eq_eq_to_eq_trans`
    // above pins eq+eq to `Eq.trans`. This test asserted the generic head only
    // because it never got far enough to produce one.
    let expr = result
        .expect("two-step eq/eq calc must elaborate; it failed only on the hole-universe bug");
    assert_eq!(
        const_head_name(&expr).as_deref(),
        Some("Eq.trans"),
        "two-step eq/eq calc should produce an Eq.trans chain, got {expr:?}"
    );
}

#[test]
fn test_elab_calc_term_justification_infers_eq_relation() {
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "calc Bool.true = Bool.true := rfl")
        .expect("term-justified calc should elaborate");
    let rel_type = infer_expr_type_with_prelude("calc Bool.true = Bool.true := rfl");
    assert_eq!(
        const_head_name(&expr).as_deref(),
        Some("rfl"),
        "term-justified calc should elaborate the proof to bare rfl, got {expr:?}"
    );
    assert_eq!(
        pi_body_const_head_name(&rel_type).as_deref(),
        Some("Eq"),
        "term-justified calc should infer an Eq relation, got {rel_type:?}"
    );
}

// =========================================================================
// Mixed-relation chain dispatch tests (Part of #3082)
//
// These tests verify that match_goal_rel correctly identifies relation
// types from constructed expressions, and that lookup_trans_rule returns
// the correct lemma for each relation pair. Combined, these guarantee
// that mk_calc_trans will dispatch correctly.
//
// Note: Direct mk_calc_trans tests require ElabCtx::new() which triggers
// stack overflow in the test thread's init_instances_from_env path
// (pre-existing issue). The dispatch logic is verified through the
// match + lookup composition instead.
// =========================================================================

use crate::tactic::calc::CalcRel;
use crate::tactic::calc_trans::lookup_trans_rule;
use crate::tactic::calc_trans_match::match_goal_rel;

/// Helper: build `@LE.le.{0} Nat instLENat lhs rhs`
fn mk_le_type(lhs: &Expr, rhs: &Expr) -> Expr {
    crate::tactic::tc_app::nat_le_tc(lhs.clone(), rhs.clone())
}

/// Helper: build `@LT.lt.{0} Nat instLTNat lhs rhs`
fn mk_lt_type(lhs: &Expr, rhs: &Expr) -> Expr {
    crate::tactic::tc_app::nat_lt_tc(lhs.clone(), rhs.clone())
}

/// Helper: build `@Eq.{0} Nat lhs rhs`
fn mk_eq_type(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// Helper: build `@GE.ge.{0} Nat instLENat lhs rhs`
fn mk_ge_type(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("GE.ge"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLENat"), vec![]),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// Helper: build `@GT.gt.{0} Nat instLTNat lhs rhs`
fn mk_gt_type(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("GT.gt"), vec![Level::zero()]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                Expr::const_(Name::from_string("instLTNat"), vec![]),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// Verify the full dispatch pipeline: match_goal_rel detects the relation,
/// then lookup_trans_rule finds the correct lemma. This is the exact logic
/// that mk_calc_trans uses internally.
fn assert_dispatch(
    left_type: &Expr,
    right_type: &Expr,
    expected_lemma: &str,
    expected_result_rel: CalcRel,
) {
    let left_match =
        match_goal_rel(left_type).expect("left type should be recognized as a calc relation");
    let right_match =
        match_goal_rel(right_type).expect("right type should be recognized as a calc relation");

    let (rel_a, _ty, _lhs, _mid, _levels) = left_match;
    let (rel_b, _, _, _rhs, _) = right_match;

    let rule = lookup_trans_rule(rel_a, rel_b).unwrap_or_else(|| {
        panic!(
            "lookup_trans_rule should find a rule for {:?} + {:?}",
            rel_a, rel_b
        )
    });

    assert_eq!(
        rule.lemma_name, expected_lemma,
        "{:?} + {:?} should dispatch {expected_lemma}, got {}",
        rel_a, rel_b, rule.lemma_name
    );
    assert_eq!(
        rule.result_rel, expected_result_rel,
        "{:?} + {:?} result should be {expected_result_rel:?}, got {:?}",
        rel_a, rel_b, rule.result_rel
    );
}

/// Test: LE + LE dispatches le_trans.
#[test]
fn test_calc_elab_dispatch_le_le_to_le_trans() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_le_type(&a, &b),
        &mk_le_type(&b, &c),
        "le_trans",
        CalcRel::Le,
    );
}

/// Test: LT + LT dispatches lt_trans.
#[test]
fn test_calc_elab_dispatch_lt_lt_to_lt_trans() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_lt_type(&a, &b),
        &mk_lt_type(&b, &c),
        "lt_trans",
        CalcRel::Lt,
    );
}

/// Test: LE + LT dispatches lt_of_le_of_lt (result is LT).
#[test]
fn test_calc_elab_dispatch_le_lt_to_lt_of_le_of_lt() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_le_type(&a, &b),
        &mk_lt_type(&b, &c),
        "lt_of_le_of_lt",
        CalcRel::Lt,
    );
}

/// Test: LT + LE dispatches lt_of_lt_of_le (result is LT).
#[test]
fn test_calc_elab_dispatch_lt_le_to_lt_of_lt_of_le() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_lt_type(&a, &b),
        &mk_le_type(&b, &c),
        "lt_of_lt_of_le",
        CalcRel::Lt,
    );
}

/// Test: EQ + LE dispatches le_of_eq_of_le (result is LE).
#[test]
fn test_calc_elab_dispatch_eq_le_to_le_of_eq_of_le() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_eq_type(&a, &b),
        &mk_le_type(&b, &c),
        "le_of_eq_of_le",
        CalcRel::Le,
    );
}

/// Test: LE + EQ dispatches le_of_le_of_eq (result is LE).
#[test]
fn test_calc_elab_dispatch_le_eq_to_le_of_le_of_eq() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_le_type(&a, &b),
        &mk_eq_type(&b, &c),
        "le_of_le_of_eq",
        CalcRel::Le,
    );
}

/// Test: EQ + LT dispatches lt_of_eq_of_lt (result is LT).
#[test]
fn test_calc_elab_dispatch_eq_lt_to_lt_of_eq_of_lt() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_eq_type(&a, &b),
        &mk_lt_type(&b, &c),
        "lt_of_eq_of_lt",
        CalcRel::Lt,
    );
}

/// Test: EQ + EQ dispatches Eq.trans (result is EQ).
#[test]
fn test_calc_elab_dispatch_eq_eq_to_eq_trans() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_eq_type(&a, &b),
        &mk_eq_type(&b, &c),
        "Eq.trans",
        CalcRel::Eq,
    );
}

/// Test: GE + GT dispatches gt_of_ge_of_gt (result is GT).
#[test]
fn test_calc_elab_dispatch_ge_gt_to_gt_of_ge_of_gt() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_ge_type(&a, &b),
        &mk_gt_type(&b, &c),
        "gt_of_ge_of_gt",
        CalcRel::Gt,
    );
}

/// Test: GT + GE dispatches gt_of_gt_of_ge (result is GT).
#[test]
fn test_calc_elab_dispatch_gt_ge_to_gt_of_gt_of_ge() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    assert_dispatch(
        &mk_gt_type(&a, &b),
        &mk_ge_type(&b, &c),
        "gt_of_gt_of_ge",
        CalcRel::Gt,
    );
}

/// Test: unrecognized relation type makes match_goal_rel return None,
/// so mk_calc_trans would fall back to Trans.trans.
#[test]
fn test_calc_elab_dispatch_unrecognized_returns_none() {
    let custom_rel = Expr::const_(Name::from_string("CustomRel"), vec![]);
    assert!(
        match_goal_rel(&custom_rel).is_none(),
        "unrecognized relation should not be matched by match_goal_rel"
    );
}

/// Test: three-step chain LE + LT + EQ produces correct result relations.
///
/// a <= b, b < c, c = d:
///   step 1+2: LE + LT -> LT (via lt_of_le_of_lt)
///   step (1+2)+3: LT + EQ -> LT (via lt_of_lt_of_eq)
/// Final result: a < d
#[test]
fn test_calc_elab_dispatch_three_step_le_lt_eq_chain() {
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    // Step 1+2: LE + LT => LT
    let le_ab = mk_le_type(&a, &b);
    let lt_bc = mk_lt_type(&b, &c);
    let left_match = match_goal_rel(&le_ab).expect("LE type should match");
    let right_match = match_goal_rel(&lt_bc).expect("LT type should match");
    let rule1 = lookup_trans_rule(left_match.0, right_match.0).expect("LE+LT should have a rule");
    assert_eq!(rule1.lemma_name, "lt_of_le_of_lt");
    assert_eq!(rule1.result_rel, CalcRel::Lt);

    // Step (1+2)+3: LT + EQ => LT
    // After step 1+2, result rel is LT, and the next step is EQ
    let eq_cd = mk_eq_type(&c, &d);
    let eq_match = match_goal_rel(&eq_cd).expect("EQ type should match");
    let rule2 = lookup_trans_rule(rule1.result_rel, eq_match.0).expect("LT+EQ should have a rule");
    assert_eq!(rule2.lemma_name, "lt_of_lt_of_eq");
    assert_eq!(rule2.result_rel, CalcRel::Lt);
}
