// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier priority and pending-forall ordering coverage.

use super::*;

#[test]
fn test_pattern_score_variable() {
    use crate::egraph::Pattern;

    let var = Pattern::var("?x");
    let score = QuantifierPriorityScorer::pattern_score(&var);
    assert_eq!(score, 0);
}

#[test]
fn test_pattern_score_constant() {
    use crate::egraph::Pattern;

    let c = Pattern::constant("c");
    let score = QuantifierPriorityScorer::pattern_score(&c);
    assert_eq!(score, 1);
}

#[test]
fn test_pattern_score_unary_app() {
    use crate::egraph::Pattern;

    let f_x = Pattern::app("f", vec![Pattern::var("?x")]);
    let score = QuantifierPriorityScorer::pattern_score(&f_x);
    assert_eq!(score, 2);
}

#[test]
fn test_pattern_score_binary_app() {
    use crate::egraph::Pattern;

    let f_xy = Pattern::app("f", vec![Pattern::var("?x"), Pattern::var("?y")]);
    let score = QuantifierPriorityScorer::pattern_score(&f_xy);
    assert_eq!(score, 3);
}

#[test]
fn test_pattern_score_nested() {
    use crate::egraph::Pattern;

    let g_x = Pattern::app("g", vec![Pattern::var("?x")]);
    let f_gx = Pattern::app("f", vec![g_x]);
    let score = QuantifierPriorityScorer::pattern_score(&f_gx);
    assert_eq!(score, 4);
}

pub(in super::super) fn make_pending_forall(
    tys: Vec<Expr>,
    trigger: crate::egraph::Trigger,
    bound_vars: Vec<u32>,
    instantiation_count: u32,
) -> PendingForall {
    PendingForall {
        _tys: tys,
        body: Expr::bvar(0),
        triggers: vec![trigger],
        bound_vars,
        priority: 0,
        instantiation_count,
        origin: None,
    }
}

#[test]
fn test_priority_scorer_fewer_vars_better() {
    use crate::egraph::{Pattern, Trigger};

    let scorer = QuantifierPriorityScorer::new();

    let one_var = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );
    let two_var = make_pending_forall(
        vec![
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("B"), vec![]),
        ],
        Trigger::single(Pattern::app(
            "f",
            vec![Pattern::var("?x0"), Pattern::var("?x1")],
        )),
        vec![0, 1],
        0,
    );

    let one_score = scorer.score(&one_var);
    let two_score = scorer.score(&two_var);

    assert!(
        one_score > two_score,
        "one_var score {one_score} should be > two_var score {two_score}"
    );
}

#[test]
fn test_priority_scorer_single_trigger_bonus() {
    use crate::egraph::{Pattern, Trigger};

    let scorer = QuantifierPriorityScorer::new();

    let single = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );
    let multi = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::multi(vec![
            Pattern::app("f", vec![Pattern::var("?x0")]),
            Pattern::app("g", vec![Pattern::var("?x0")]),
        ]),
        vec![0],
        0,
    );

    let single_score = scorer.score(&single);
    let multi_score = scorer.score(&multi);

    assert!(
        single_score > multi_score,
        "single trigger score {single_score} should be > multi trigger score {multi_score}"
    );
}

#[test]
fn test_priority_scorer_fairness_penalty() {
    use crate::egraph::{Pattern, Trigger};

    let scorer = QuantifierPriorityScorer::new();

    let fresh = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );
    let used = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        3,
    );

    let fresh_score = scorer.score(&fresh);
    let used_score = scorer.score(&used);

    assert!(
        fresh_score > used_score,
        "fresh score {fresh_score} should be > used score {used_score}"
    );
    assert_eq!(fresh_score - used_score, 30);
}

#[test]
fn test_pending_foralls_sorted_by_priority() {
    let env = Environment::new();
    let mut bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_xy = Expr::app(Expr::app(f.clone(), Expr::bvar(1)), Expr::bvar(0));
    let f_yx = Expr::app(Expr::app(f, Expr::bvar(0)), Expr::bvar(1));
    let eq_2var = make_eq(ty_a.clone(), f_xy, f_yx);
    let forall_2var = Expr::pi(
        BinderInfo::Default,
        ty_a.clone(),
        Expr::pi(BinderInfo::Default, ty_a.clone(), eq_2var),
    );

    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_x = Expr::app(g, Expr::bvar(0));
    let eq_1var = make_eq(ty_a.clone(), g_x, Expr::bvar(0));
    let forall_1var = Expr::pi(BinderInfo::Default, ty_a.clone(), eq_1var);

    bridge
        .add_hypothesis(&forall_2var)
        .expect("two-variable forall should register");
    bridge
        .add_hypothesis(&forall_1var)
        .expect("one-variable forall should register");

    assert_eq!(bridge.pending_foralls.len(), 2);

    let p1 = bridge.pending_foralls[0].priority;
    let p2 = bridge.pending_foralls[1].priority;
    assert!(p1 > 0, "2-var forall priority should be non-zero, got {p1}");
    assert!(p2 > 0, "1-var forall priority should be non-zero, got {p2}");
    assert!(
        p2 > p1,
        "1-var forall (p2={p2}) should have higher priority than 2-var (p1={p1})"
    );
}
