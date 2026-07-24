// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trigger extraction and trigger-shape coverage.

use super::*;

#[test]
fn test_trigger_extraction_simple() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty, f_x.clone(), g_x.clone());

    let bound_vars = vec![0];
    let triggers = bridge.extract_triggers(&body, &bound_vars);

    assert!(
        triggers.len() >= 2,
        "Should find at least 2 triggers, found {}",
        triggers.len()
    );

    let has_f = triggers.iter().any(|t| {
        if let ExprKind::App(head, _) = t.pattern.kind() {
            matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "f")
        } else {
            false
        }
    });
    let has_g = triggers.iter().any(|t| {
        if let ExprKind::App(head, _) = t.pattern.kind() {
            matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "g")
        } else {
            false
        }
    });
    assert!(has_f, "Should find f(x) as trigger");
    assert!(has_g, "Should find g(x) as trigger");
}

#[test]
fn test_trigger_extraction_nested() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let f_g_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), g_x.clone());
    let h_x = Expr::app(Expr::const_(Name::from_string("h"), vec![]), Expr::bvar(0));

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty, f_g_x.clone(), h_x.clone());

    let bound_vars = vec![0];
    let triggers = bridge.extract_triggers(&body, &bound_vars);

    assert!(
        triggers.len() >= 2,
        "Should find at least 2 triggers, found {}",
        triggers.len()
    );

    let head_names: Vec<String> = triggers
        .iter()
        .filter_map(|t| {
            let h = t.pattern.get_app_fn();
            if let ExprKind::Const(ref name, _) = h.kind() {
                Some(name.to_string())
            } else {
                None
            }
        })
        .collect();
    assert!(
        head_names.contains(&"h".to_string()),
        "Should find h(x) as a trigger, got heads: {head_names:?}"
    );
    assert!(
        head_names.contains(&"f".to_string()) || head_names.contains(&"g".to_string()),
        "Should find f(g(x)) or g(x) as a trigger, got heads: {head_names:?}"
    );
}

#[test]
fn test_trigger_extraction_multi_arg() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_xy = Expr::app(
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        Expr::bvar(1),
    );
    let g_yx = Expr::app(
        Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty, f_xy.clone(), g_yx.clone());

    let bound_vars = vec![0, 1];
    let triggers = bridge.extract_triggers(&body, &bound_vars);

    assert!(
        !triggers.is_empty(),
        "Should find triggers for multi-variable formula"
    );

    let has_both_vars = triggers
        .iter()
        .any(|t| t.bound_vars.contains(&0) && t.bound_vars.contains(&1));
    assert!(
        has_both_vars,
        "At least one trigger should cover both bound variables 0 and 1, got triggers: {:?}",
        triggers.iter().map(|t| &t.bound_vars).collect::<Vec<_>>()
    );
}

#[test]
fn test_extract_ematch_triggers_combines_bound_vars() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(1));
    let g_y = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty.clone(), f_x, g_y);

    let bound_vars = vec![0, 1];
    let triggers = bridge.extract_ematch_triggers(&body, &bound_vars);

    let covers_all = triggers.iter().any(|t| {
        let vars = t.variables();
        vars.contains(&"?x0".to_string()) && vars.contains(&"?x1".to_string())
    });

    assert!(
        covers_all,
        "Combined triggers should cover all bound variables for multi-forall"
    );
}

#[test]
fn test_trigger_pattern_scoring() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let f_g_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), g_x);
    let h_f_g_x = Expr::app(Expr::const_(Name::from_string("h"), vec![]), f_g_x);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let body = make_eq(ty, f_x.clone(), h_f_g_x.clone());

    let bound_vars = vec![0];
    let triggers = bridge.extract_triggers(&body, &bound_vars);

    assert!(
        triggers.len() >= 2,
        "Should extract at least 2 triggers (f(x) and h(f(g(x)))), got {}",
        triggers.len()
    );
    assert!(
        triggers[0].score > 0,
        "Best trigger should have positive score (guards against all-zero scorer bug), got score={}",
        triggers[0].score
    );

    for i in 1..triggers.len() {
        assert!(
            triggers[i - 1].score >= triggers[i].score,
            "Triggers should be sorted by score descending: trigger[{}].score={} < trigger[{}].score={}",
            i - 1,
            triggers[i - 1].score,
            i,
            triggers[i].score
        );
    }

    let f_score = triggers
        .iter()
        .find(|t| {
            matches!(t.pattern.get_app_fn().kind(), ExprKind::Const(ref n, _) if n.to_string() == "f")
        })
        .map(|t| t.score);
    let h_score = triggers
        .iter()
        .find(|t| {
            matches!(t.pattern.get_app_fn().kind(), ExprKind::Const(ref n, _) if n.to_string() == "h")
        })
        .map(|t| t.score);
    if let (Some(f), Some(h)) = (f_score, h_score) {
        assert!(
            f > h,
            "Simple trigger f(x) (score={f}) should score strictly higher than complex h(f(g(x))) (score={h})"
        );
    }
}

#[test]
fn test_trigger_to_ematch_pattern() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let f_x = Expr::app(
        Expr::const_(Name::from_string("myFunc"), vec![]),
        Expr::bvar(0),
    );

    let trigger = TriggerPattern::new(f_x, vec![0]);
    let ematch_trigger = bridge.trigger_from_patterns(&[&trigger]);

    assert!(
        ematch_trigger.is_some(),
        "Should convert to E-match pattern"
    );
    let ematch = ematch_trigger.expect("trigger should convert to an E-match pattern");
    assert_eq!(ematch.patterns.len(), 1, "Should have one pattern");

    assert!(
        matches!(&ematch.patterns[0], crate::egraph::Pattern::App(_, _)),
        "Expected App pattern, got {:?}",
        ematch.patterns[0]
    );
    let crate::egraph::Pattern::App(sym, children) = &ematch.patterns[0] else {
        return;
    };
    assert_eq!(sym.name(), "myFunc");
    assert_eq!(children.len(), 1);
    assert!(matches!(&children[0], crate::egraph::Pattern::Var(name) if name == "?x0"));
}

#[test]
fn test_trigger_theory_symbol_filtering() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let add_xy = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Add.add"), vec![]),
            Expr::bvar(0),
        ),
        Expr::bvar(1),
    );
    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));

    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = make_eq(ty, add_xy, f_x);

    let bound_vars = vec![0, 1];
    let triggers = bridge.extract_triggers(&body, &bound_vars);

    assert_eq!(
        triggers.len(),
        1,
        "Should extract exactly 1 trigger (f), not Add.add"
    );

    let head_fn = triggers[0].pattern.get_app_fn();
    assert!(
        matches!(head_fn.kind(), ExprKind::Const(ref name, _) if name.to_string() == "f"),
        "Trigger head should be f, got {:?}",
        head_fn.kind()
    );

    let has_add = triggers.iter().any(|t| {
        let h = t.pattern.get_app_fn();
        matches!(h.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Add.add")
    });
    assert!(
        !has_add,
        "Theory symbol Add.add should be filtered from triggers"
    );
}
