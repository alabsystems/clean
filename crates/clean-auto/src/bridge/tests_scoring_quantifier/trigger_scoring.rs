// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trigger-combination scoring coverage.

use super::*;

#[test]
fn test_trigger_combination_scoring_prefers_single() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_xy = TriggerPattern {
        pattern: Expr::app(
            Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
            Expr::bvar(1),
        ),
        bound_vars: vec![0, 1],
        score: 8,
    };
    let g_x = TriggerPattern {
        pattern: Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
        bound_vars: vec![0],
        score: 9,
    };
    let h_y = TriggerPattern {
        pattern: Expr::app(Expr::const_(Name::from_string("h"), vec![]), Expr::bvar(1)),
        bound_vars: vec![1],
        score: 9,
    };

    let single_score = bridge.score_trigger_combination(&[&f_xy]);
    let pair_score = bridge.score_trigger_combination(&[&g_x, &h_y]);

    assert!(
        single_score > pair_score,
        "Single trigger ({single_score}) should score higher than pair ({pair_score})"
    );
}

#[test]
fn test_trigger_combination_scoring_penalizes_overlap() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_x = TriggerPattern {
        pattern: Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        bound_vars: vec![0],
        score: 9,
    };
    let g_xy = TriggerPattern {
        pattern: Expr::app(
            Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
            Expr::bvar(1),
        ),
        bound_vars: vec![0, 1],
        score: 7,
    };
    let h_x = TriggerPattern {
        pattern: Expr::app(Expr::const_(Name::from_string("h"), vec![]), Expr::bvar(0)),
        bound_vars: vec![0],
        score: 9,
    };
    let j_y = TriggerPattern {
        pattern: Expr::app(Expr::const_(Name::from_string("j"), vec![]), Expr::bvar(1)),
        bound_vars: vec![1],
        score: 9,
    };

    let overlapping_score = bridge.score_trigger_combination(&[&f_x, &g_xy]);
    let non_overlapping_score = bridge.score_trigger_combination(&[&h_x, &j_y]);

    assert!(
        non_overlapping_score > overlapping_score,
        "Non-overlapping ({non_overlapping_score}) should score higher than overlapping ({overlapping_score})"
    );
}

fn assert_triggers_sorted_descending(
    bridge: &SmtBridge,
    head_names: &[String],
    body: &Expr,
    bound_vars: &[u32],
) {
    let raw_patterns = bridge.extract_triggers(body, bound_vars);
    let mut expected_scores: Vec<(&str, i32)> = Vec::new();
    for pat in &raw_patterns {
        let head_name = pat.pattern.get_app_fn();
        if let ExprKind::Const(ref name, _) = head_name.kind() {
            let score = bridge.score_trigger_combination(&[pat]);
            expected_scores.push((if name.to_string() == "f" { "f" } else { "g" }, score));
        }
    }
    for i in 1..head_names.len() {
        let prev_score = expected_scores
            .iter()
            .find(|(n, _)| *n == head_names[i - 1])
            .map(|(_, s)| *s)
            .unwrap_or(0);
        let curr_score = expected_scores
            .iter()
            .find(|(n, _)| *n == head_names[i])
            .map(|(_, s)| *s)
            .unwrap_or(0);
        assert!(
            prev_score >= curr_score,
            "Triggers should be sorted by score descending: trigger[{}] ({}, score={}) should have score >= trigger[{}] ({}, score={})",
            i - 1,
            head_names[i - 1],
            prev_score,
            i,
            head_names[i],
            curr_score
        );
    }
}

#[test]
fn test_extract_ematch_triggers_sorted_by_score() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_xy = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::bvar(1),
    );
    let g_xy = Expr::app(
        Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
        Expr::bvar(1),
    );

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty.clone(), f_xy, g_xy);

    let bound_vars = vec![0, 1];
    let triggers = bridge.extract_ematch_triggers(&body, &bound_vars);

    assert_eq!(
        triggers.len(),
        2,
        "Should extract exactly 2 triggers, got {}",
        triggers.len()
    );

    for (i, trigger) in triggers.iter().enumerate() {
        assert_eq!(
            trigger.patterns.len(),
            1,
            "All triggers should be single-pattern, but trigger[{i}] has {} patterns",
            trigger.patterns.len()
        );
    }

    let head_names: Vec<String> = triggers
        .iter()
        .filter_map(|t| {
            if let crate::egraph::Pattern::App(sym, _) = &t.patterns[0] {
                Some(sym.name().to_string())
            } else {
                None
            }
        })
        .collect();
    assert!(
        head_names.contains(&"f".to_string()),
        "Missing head f: {head_names:?}"
    );
    assert!(
        head_names.contains(&"g".to_string()),
        "Missing head g: {head_names:?}"
    );

    assert_triggers_sorted_descending(&bridge, &head_names, &body, &bound_vars);
}
