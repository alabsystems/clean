// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for trigger pattern extraction and scoring (trigger.rs).
//!
//! Covers: TriggerPattern construction/scoring, TriggerExtractor via
//! SmtBridge::extract_triggers, theory symbol filtering, deduplication.

use super::super::*;
use super::setup_env;
use std::sync::Arc;

fn squash(inner: Expr) -> Expr {
    Expr::from_kind(ExprKind::Squash(Arc::new(inner)))
}

fn wrap_transparent(inner: Expr) -> Expr {
    Expr::proj(
        Name::from_string("Wrap.proj"),
        0,
        Expr::mdata(vec![], squash(inner)),
    )
}

fn wrapped_nested_trigger() -> Expr {
    let g_y_7 = Expr::app(
        Expr::app(
            wrap_transparent(Expr::const_(Name::from_string("g"), vec![])),
            wrap_transparent(Expr::bvar(1)),
        ),
        wrap_transparent(Expr::nat_lit(7)),
    );

    wrap_transparent(Expr::app(
        Expr::app(
            wrap_transparent(Expr::const_(Name::from_string("f"), vec![])),
            wrap_transparent(Expr::bvar(0)),
        ),
        wrap_transparent(g_y_7),
    ))
}

// ========================================================================
// TriggerPattern scoring tests
// ========================================================================

#[test]
fn test_trigger_pattern_app_scores_positive() {
    // f(x) as a trigger pattern should have a positive score:
    // +10 (app bonus) - 3 (size: App + Const + BVar) + 5 (constant bonus for f) = 12
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_x = Expr::app(f, Expr::bvar(0));
    let tp = TriggerPattern::new(f_x, vec![0]);
    assert!(
        tp.score > 0,
        "App trigger should score positive, got {}",
        tp.score
    );
}

#[test]
fn test_trigger_pattern_missing_bvar_penalty() {
    // Pattern f(x) with bound_vars [0, 1] — BVar(1) is missing from pattern.
    // The -100 penalty per missing var should dominate.
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_x = Expr::app(f, Expr::bvar(0));
    let tp = TriggerPattern::new(f_x, vec![0, 1]);
    assert!(
        tp.score < -50,
        "Missing BVar should cause large penalty, got {}",
        tp.score
    );
}

#[test]
fn test_trigger_pattern_all_bvars_present_no_penalty() {
    // f(x, y) with bound_vars [0, 1] — both present, no penalty
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_xy = Expr::app(Expr::app(f, Expr::bvar(0)), Expr::bvar(1));
    let tp = TriggerPattern::new(f_xy, vec![0, 1]);
    // Should be positive: +10 (app) + 5 (constant) - size
    assert!(
        tp.score > 0,
        "All BVars present should yield positive score, got {}",
        tp.score
    );
}

#[test]
fn test_trigger_pattern_constant_bonus() {
    // Pattern with a constant (f) should score higher than one without (just BVars)
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_x = Expr::app(f, Expr::bvar(0));
    let with_const = TriggerPattern::new(f_x, vec![0]);

    // FVar-headed app has no constant
    let fv = Expr::fvar(FVarId::new(1));
    let fv_x = Expr::app(fv, Expr::bvar(0));
    let without_const = TriggerPattern::new(fv_x, vec![0]);

    assert!(
        with_const.score > without_const.score,
        "Constant trigger ({}) should score higher than FVar trigger ({})",
        with_const.score,
        without_const.score
    );
}

#[test]
fn test_trigger_pattern_larger_is_penalized() {
    // f(x) vs f(g(x)) — deeper nesting means more nodes, higher size penalty
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    let f_x = Expr::app(f.clone(), Expr::bvar(0));
    let small = TriggerPattern::new(f_x, vec![0]);

    let g_x = Expr::app(g, Expr::bvar(0));
    let f_gx = Expr::app(f, g_x);
    let large = TriggerPattern::new(f_gx, vec![0]);

    // Both have constant bonus and app bonus, but large has more size penalty
    assert!(
        small.score > large.score,
        "Smaller pattern ({}) should score higher than larger ({})",
        small.score,
        large.score
    );
}

#[test]
fn test_trigger_pattern_transparent_wrappers_do_not_change_score() {
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let plain = Expr::app(f.clone(), Expr::bvar(0));
    let root_wrapped = wrap_mdata(plain.clone());
    let wrapped_arg = Expr::proj(
        Name::from_string("Wrap"),
        0,
        Expr::mdata(
            vec![],
            Expr::from_kind(ExprKind::Squash(Arc::new(Expr::bvar(0)))),
        ),
    );
    let wrapped = Expr::app(f, wrapped_arg);

    let plain_score = TriggerPattern::new(plain, vec![0]).score;
    let root_wrapped_score = TriggerPattern::new(root_wrapped, vec![0]).score;
    let wrapped_score = TriggerPattern::new(wrapped, vec![0]).score;

    assert_eq!(
        wrapped_score, plain_score,
        "transparent trigger wrappers should not change scoring"
    );
    assert_eq!(
        root_wrapped_score, plain_score,
        "root transparent wrappers should not change scoring"
    );
}

// ========================================================================
// Trigger extraction tests (via SmtBridge::extract_triggers)
// ========================================================================

#[test]
fn test_extract_triggers_from_simple_body() {
    // Body: f(x) = a, bound_vars: [0]
    // Should extract f(x) as a trigger (non-theory head)
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let f_x = Expr::app(f, Expr::bvar(0));
    let body = super::make_eq(ty, f_x, a);

    let triggers = bridge.extract_triggers(&body, &[0]);
    assert!(
        !triggers.is_empty(),
        "Should extract at least one trigger from f(x) = a"
    );

    // f(x) should be among the triggers
    let has_f_head = triggers.iter().any(|t| {
        let head = t.pattern.get_app_fn();
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == "f")
    });
    assert!(has_f_head, "Should find trigger with head symbol f");
}

#[test]
fn test_extract_triggers_filters_eq_head() {
    // Body is just Eq(A, x, x) — Eq is a theory symbol, should not be a trigger
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = super::make_eq(ty, Expr::bvar(0), Expr::bvar(0));

    let triggers = bridge.extract_triggers(&body, &[0]);

    // Eq-headed applications should be filtered out
    let has_eq_head = triggers.iter().any(|t| {
        let head = t.pattern.get_app_fn();
        matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == "Eq")
    });
    assert!(
        !has_eq_head,
        "Eq-headed patterns should be filtered as theory symbols"
    );
}

#[test]
fn test_extract_triggers_sorted_descending() {
    // Create body with multiple potential triggers of different quality
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let ty = Expr::const_(Name::from_string("A"), vec![]);

    // f(x) and g(f(x)) — g(f(x)) is larger, so f(x) should score higher
    let f_x = Expr::app(f.clone(), Expr::bvar(0));
    let g_fx = Expr::app(g, f_x.clone());
    let body = super::make_eq(ty, g_fx, f_x);

    let triggers = bridge.extract_triggers(&body, &[0]);
    assert!(
        triggers.len() >= 2,
        "Need at least 2 triggers to test sorting, got {}",
        triggers.len()
    );
    // Verify sorted by score descending
    for window in triggers.windows(2) {
        assert!(
            window[0].score >= window[1].score,
            "Triggers should be sorted descending: score {} >= {}",
            window[0].score,
            window[1].score
        );
    }
}

#[test]
fn test_extract_triggers_deduplicates() {
    // If the same pattern appears in multiple positions, extract_triggers deduplicates
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let f_x = Expr::app(f, Expr::bvar(0));

    // f(x) = f(x) — same trigger on both sides
    let body = super::make_eq(ty, f_x.clone(), f_x);

    let triggers = bridge.extract_triggers(&body, &[0]);
    // Count how many have head 'f'
    let f_count = triggers
        .iter()
        .filter(|t| {
            let head = t.pattern.get_app_fn();
            matches!(head.kind(), ExprKind::Const(name, _) if name.to_string() == "f")
        })
        .count();
    assert_eq!(f_count, 1, "Duplicate f(x) triggers should be deduplicated");
}

#[test]
fn test_extract_triggers_constant_body_empty() {
    // Body is just a constant (no applications) — no triggers
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let triggers = bridge.extract_triggers(&a, &[0]);
    assert!(
        triggers.is_empty(),
        "Constant body should yield no triggers, got {}",
        triggers.len()
    );
}

#[test]
fn test_extract_triggers_fvar_headed_app_valid() {
    // FVar-headed applications should be valid triggers (not theory symbols)
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let fv = Expr::fvar(FVarId::new(42));
    let fv_x = Expr::app(fv, Expr::bvar(0));
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let body = super::make_eq(ty, fv_x, a);

    let triggers = bridge.extract_triggers(&body, &[0]);
    let has_fvar_head = triggers.iter().any(|t| {
        let head = t.pattern.get_app_fn();
        matches!(head.kind(), ExprKind::FVar(_))
    });
    assert!(has_fvar_head, "FVar-headed apps should be valid triggers");
}

#[test]
fn test_extract_triggers_recurses_through_proj_mdata_squash_wrappers() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let body = super::make_eq(ty, wrapped_nested_trigger(), a);

    let triggers = bridge.extract_triggers(&body, &[0, 1]);
    assert!(
        triggers
            .iter()
            .any(|t| t.pattern.get_app_num_args() == 2 && t.bound_vars == vec![0, 1]),
        "wrapped trigger app should survive extraction with both bound variables, got {triggers:?}"
    );
}

#[test]
fn test_extract_ematch_triggers_unwraps_wrapped_nested_apps_and_literals() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let triggers = bridge.extract_ematch_triggers(&wrapped_nested_trigger(), &[0, 1]);
    let expected = crate::egraph::Pattern::app(
        "f",
        vec![
            crate::egraph::Pattern::var("?x0"),
            crate::egraph::Pattern::app(
                "g",
                vec![
                    crate::egraph::Pattern::var("?x1"),
                    crate::egraph::Pattern::constant("nat_7"),
                ],
            ),
        ],
    );

    assert!(
        triggers
            .iter()
            .any(|trigger| trigger.patterns == vec![expected.clone()]),
        "wrapped nested apps and literals should normalize into a usable E-matching pattern, got {triggers:?}"
    );
}

// ========================================================================
// Regression tests for transparent wrapper traversal (#3035)
// ========================================================================

/// Helper: wrap an expression in MData
fn wrap_mdata(expr: Expr) -> Expr {
    Expr::mdata(vec![], expr)
}

#[test]
fn test_extract_triggers_deduplicates_wrapped_and_unwrapped_apps() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let wrapped_arg = Expr::proj(
        Name::from_string("Wrap"),
        0,
        Expr::mdata(
            vec![],
            Expr::from_kind(ExprKind::Squash(Arc::new(Expr::bvar(0)))),
        ),
    );
    let inner = Expr::app(
        Expr::mdata(vec![], Expr::const_(Name::from_string("f"), vec![])),
        wrapped_arg,
    );
    let wrapped = Expr::mdata(vec![], inner.clone());
    let body = super::make_eq(ty, wrapped, inner);

    let triggers = bridge.extract_triggers(&body, &[0]);
    let f_headed: Vec<_> = triggers
        .iter()
        .filter(|t| {
            matches!(
                t.pattern.get_app_fn().kind(),
                ExprKind::Const(name, _) if name.to_string() == "f"
            )
        })
        .collect();

    assert_eq!(
        f_headed.len(),
        1,
        "wrapped and unwrapped variants should normalize to one trigger"
    );

    let ematch = bridge.extract_ematch_triggers(&body, &[0]);
    assert_eq!(
        ematch.len(),
        1,
        "wrapped and unwrapped trigger variants should normalize to one E-matching trigger"
    );
    assert_eq!(ematch[0].variables(), vec!["?x0".to_string()]);
}
