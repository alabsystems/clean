// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for goal-directed instantiation and premise selection.

use super::super::*;
use super::setup_env;
use super::tests_scoring_quantifier::make_pending_forall;
use clean_kernel::Level;
use std::collections::HashMap;

// ========================================================================
// Goal-Directed Instantiation Tests
// ========================================================================

#[test]
fn test_goal_patterns_empty() {
    let patterns = GoalPatterns::new();
    assert!(patterns.is_empty());
    assert!(patterns.ground_terms.is_empty());
    assert!(patterns.function_symbols.is_empty());
}

#[test]
fn test_goal_patterns_contains_symbol() {
    use crate::egraph::Symbol;

    let mut patterns = GoalPatterns::new();
    let sym_f = Symbol::new("f");
    let sym_g = Symbol::new("g");

    patterns.function_symbols.insert(sym_f.clone());

    assert!(patterns.contains_symbol(&sym_f));
    assert!(!patterns.contains_symbol(&sym_g));
    assert!(!patterns.is_empty());
}

#[test]
fn test_goal_patterns_relevance_score_no_match() {
    use crate::egraph::{Pattern, Trigger};

    let patterns = GoalPatterns::new(); // Empty patterns

    // Trigger with function h that's not in goal
    let trigger = Trigger::single(Pattern::app("h", vec![Pattern::var("?x")]));

    // No relevance since goal patterns are empty
    assert_eq!(patterns.relevance_score(&trigger), 0);
}

#[test]
fn test_goal_patterns_relevance_score_symbol_match() {
    use crate::egraph::{Pattern, Symbol, Trigger};

    let mut patterns = GoalPatterns::new();
    patterns.function_symbols.insert(Symbol::new("f"));

    // Trigger with function f that IS in goal
    let trigger = Trigger::single(Pattern::app("f", vec![Pattern::var("?x")]));

    // Should get bonus for matching symbol
    let score = patterns.relevance_score(&trigger);
    assert!(score > 0, "Should have positive relevance score: {score}");
}

#[test]
fn test_goal_patterns_relevance_score_ground_term_match() {
    use crate::egraph::{Pattern, Symbol, Trigger};

    let mut patterns = GoalPatterns::new();
    let sym_f = Symbol::new("f");
    patterns.function_symbols.insert(sym_f.clone());
    patterns.ground_terms.push(GroundTermPattern {
        symbol: sym_f,
        arity: 1,
    });

    // Trigger with exact arity match
    let trigger = Trigger::single(Pattern::app("f", vec![Pattern::var("?x")]));

    // Should get bonus for symbol + bonus for ground term with matching arity
    let score = patterns.relevance_score(&trigger);
    // Symbol match: 10, Ground term match: 20 = 30
    assert!(
        score >= 30,
        "Should have high relevance for ground term match: {score}"
    );
}

#[test]
fn test_goal_patterns_nested_relevance() {
    use crate::egraph::{Pattern, Symbol, Trigger};

    let mut patterns = GoalPatterns::new();
    patterns.function_symbols.insert(Symbol::new("f"));
    patterns.function_symbols.insert(Symbol::new("g"));

    // Nested trigger f(g(?x))
    let trigger = Trigger::single(Pattern::app(
        "f",
        vec![Pattern::app("g", vec![Pattern::var("?x")])],
    ));

    // Should get bonus for both f and g
    let score = patterns.relevance_score(&trigger);
    // f: 10, g: 10 = 20
    assert!(
        score >= 20,
        "Should have bonus for nested matching symbols: {score}"
    );
}

#[test]
fn test_goal_directed_scorer_basic() {
    use crate::egraph::{Pattern, Symbol, Trigger};

    // Create goal patterns with symbol f
    let mut goal_patterns = GoalPatterns::new();
    goal_patterns.function_symbols.insert(Symbol::new("f"));

    let scorer = GoalDirectedScorer::new(goal_patterns);
    assert!(scorer.has_goal_patterns());

    let pending_match = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );
    let pending_no_match = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("h", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );

    let score_match = scorer.score(&pending_match);
    let score_no_match = scorer.score(&pending_no_match);

    assert!(
        score_match > score_no_match,
        "Goal-matching forall should score higher: {score_match} > {score_no_match}"
    );
}

#[test]
fn test_goal_directed_scorer_relevance_weight() {
    use crate::egraph::{Pattern, Symbol, Trigger};

    let mut goal_patterns = GoalPatterns::new();
    goal_patterns.function_symbols.insert(Symbol::new("f"));

    let low_weight_scorer =
        GoalDirectedScorer::with_weights(goal_patterns.clone(), QuantifierPriorityScorer::new(), 1);
    let high_weight_scorer =
        GoalDirectedScorer::with_weights(goal_patterns, QuantifierPriorityScorer::new(), 10);

    let pending = make_pending_forall(
        vec![Expr::const_(Name::from_string("A"), vec![])],
        Trigger::single(Pattern::app("f", vec![Pattern::var("?x0")])),
        vec![0],
        0,
    );

    let low_score = low_weight_scorer.score(&pending);
    let high_score = high_weight_scorer.score(&pending);

    assert!(
        high_score > low_score,
        "Higher weight should give higher score: {high_score} > {low_score}"
    );
}

#[test]
fn test_goal_pattern_extractor_equality() {
    let expr_to_term: HashMap<ExprKey, TermId> = HashMap::new();
    let mut extractor = GoalPatternExtractor::new(&expr_to_term);

    // Create equality goal: f(a) = g(b)
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let f_a = Expr::app(f, a);
    let g_b = Expr::app(g, b);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = LogicalForm::Eq {
        ty: nat_ty,
        lhs: f_a,
        rhs: g_b,
    };
    let patterns = extractor.extract(&goal);

    // Should have extracted function symbols including f and g
    assert!(!patterns.function_symbols.is_empty());
    assert!(
        patterns.function_symbols.len() >= 2,
        "Should have at least f and g: {:?}",
        patterns.function_symbols
    );
    assert!(
        patterns.contains_symbol(&crate::egraph::Symbol::new("f")),
        "Should contain symbol f, got: {:?}",
        patterns.function_symbols
    );
    assert!(
        patterns.contains_symbol(&crate::egraph::Symbol::new("g")),
        "Should contain symbol g, got: {:?}",
        patterns.function_symbols
    );
}

#[test]
fn test_goal_pattern_extractor_implication() {
    let expr_to_term: HashMap<ExprKey, TermId> = HashMap::new();
    let mut extractor = GoalPatternExtractor::new(&expr_to_term);

    // Create implication goal: P(a) → Q(b)
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let p_a = Expr::app(p, a);
    let q_b = Expr::app(q, b);

    let goal = LogicalForm::Implies(p_a, q_b);
    let patterns = extractor.extract(&goal);

    // Should have extracted function symbols P and Q
    assert!(
        patterns.function_symbols.len() >= 2,
        "Should have at least P and Q: {:?}",
        patterns.function_symbols
    );
    assert!(
        patterns.contains_symbol(&crate::egraph::Symbol::new("P")),
        "Should contain symbol P, got: {:?}",
        patterns.function_symbols
    );
    assert!(
        patterns.contains_symbol(&crate::egraph::Symbol::new("Q")),
        "Should contain symbol Q, got: {:?}",
        patterns.function_symbols
    );
}

#[test]
fn test_goal_pattern_extractor_squash_atom() {
    use std::sync::Arc;

    let expr_to_term: HashMap<ExprKey, TermId> = HashMap::new();
    let mut extractor = GoalPatternExtractor::new(&expr_to_term);

    // Create a squashed goal atom: Squash(App(f, a))
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let f_a = Expr::app(f, a);
    let squashed = Expr::from_kind(ExprKind::Squash(Arc::new(f_a)));

    let goal = LogicalForm::Atom(squashed);
    let patterns = extractor.extract(&goal);

    // The extractor should see through Squash and record symbol f
    assert!(
        patterns.contains_symbol(&crate::egraph::Symbol::new("f")),
        "Should extract symbol f from squashed atom, got: {:?}",
        patterns.function_symbols
    );
    assert!(
        !patterns.function_symbols.is_empty(),
        "Squashed goal atom should not produce empty patterns"
    );
}

#[test]
fn test_premise_origin_creation() {
    use crate::premise::PremiseId;

    let name = Name::from_string("my_theorem");
    let id = PremiseId(42);

    // Full constructor
    let origin = PremiseOrigin::new(name.clone(), id);
    assert_eq!(origin.name(), Some(&name));
    assert_eq!(origin.premise_id(), Some(id));
    assert!(!origin.is_empty());

    // Name only
    let origin_name = PremiseOrigin::from_name(name.clone());
    assert_eq!(origin_name.name(), Some(&name));
    assert_eq!(origin_name.premise_id(), None);
    assert!(!origin_name.is_empty());

    // ID only
    let origin_id = PremiseOrigin::from_premise_id(id);
    assert_eq!(origin_id.name(), None);
    assert_eq!(origin_id.premise_id(), Some(id));
    assert!(!origin_id.is_empty());

    // Empty
    let origin_empty = PremiseOrigin::default();
    assert!(origin_empty.is_empty());
}

#[test]
fn test_premise_score_configuration() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let mut scores = HashMap::new();
    scores.insert(PremiseId(1), 0.9);
    scores.insert(PremiseId(2), 0.5);
    scores.insert(PremiseId(3), 0.1);
    bridge.set_premise_scores(scores.clone());

    assert_eq!(bridge.premise_scores.len(), 3);
    assert!((bridge.premise_scores.get(&PremiseId(1)).unwrap() - 0.9).abs() < 0.001);
}

#[test]
fn test_premise_origin_threaded_through_hypothesis() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Create a Type-typed forall with function applications that produce
    // E-matching triggers: ∀ x : T, Eq T (f x) (g x)
    let forall = make_fx_eq_gx_forall();

    // Add with premise origin
    let origin = PremiseOrigin::new(Name::from_string("identity"), PremiseId(99));
    bridge
        .add_hypothesis_with_premise(&forall, None, Some(origin))
        .expect("add_hypothesis_with_premise failed");

    // The forall body has function applications (f, g) that generate
    // E-matching triggers, so a PendingForall should be created with the origin.
    assert_eq!(
        bridge.pending_foralls.len(),
        1,
        "Type-typed forall with triggers should create exactly one pending forall"
    );
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::premise_id),
        Some(PremiseId(99)),
        "Pending forall should carry the premise ID from the origin"
    );
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::name),
        Some(&Name::from_string("identity")),
        "Pending forall should carry the name from the origin"
    );
}

#[test]
fn test_origin_survives_flattening() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    // Create a nested Type-typed forall: ∀ x : T, ∀ y : T, Eq T (f x) (g y)
    // flatten_forall should combine both binders, and the origin should survive.
    let ty_t = Expr::const_(Name::from_string("T"), vec![]);
    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(1));
    let g_y = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_applied = Expr::app(Expr::app(Expr::app(eq_const, ty_t.clone()), f_x), g_y);
    let inner_forall = Expr::pi(BinderInfo::Default, ty_t.clone(), eq_applied);
    let outer_forall = Expr::pi(BinderInfo::Default, ty_t, inner_forall);

    let origin_name = Name::from_string("nested_theorem");
    let origin_id = PremiseId(123);
    let origin = PremiseOrigin::new(origin_name.clone(), origin_id);
    bridge
        .add_hypothesis_with_premise(&outer_forall, None, Some(origin))
        .expect("add_hypothesis_with_premise failed");

    // After flattening, the forall should produce a pending forall with
    // both binder types and the origin intact.
    assert_eq!(
        bridge.pending_foralls.len(),
        1,
        "Nested Type-typed forall with triggers should create one pending forall"
    );
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::premise_id),
        Some(origin_id),
        "Origin premise ID should survive flattening"
    );
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::name),
        Some(&origin_name),
        "Origin name should survive flattening"
    );
}

#[test]
fn test_local_quantifier_origin_inferred_from_fvar() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let forall = make_fx_eq_gx_forall();
    let fvar = FVarId::new(77);

    bridge
        .add_hypothesis_with_fvar(&forall, Some(fvar))
        .expect("add_hypothesis_with_fvar failed");

    assert_eq!(bridge.pending_foralls.len(), 1);
    assert!(matches!(
        bridge.pending_foralls[0].origin.as_ref(),
        Some(QuantifierOrigin::Local { fvar_id }) if *fvar_id == fvar
    ));
    assert_eq!(
        bridge.pending_foralls[0].compute_premise_bonus(&HashMap::from([(PremiseId(99), 1.0)])),
        0,
        "local quantifiers should remain neutral under premise scoring"
    );
}

#[test]
fn test_premise_bonus_ordering() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let mut scores = HashMap::new();
    scores.insert(PremiseId(1), 1.0);
    scores.insert(PremiseId(2), 0.1);
    bridge.set_premise_scores(scores);

    // Use a Type-typed forall that generates E-matching triggers
    let forall = make_fx_eq_gx_forall();

    let origin_low = PremiseOrigin::from_premise_id(PremiseId(2));
    bridge
        .add_hypothesis_with_premise(&forall, None, Some(origin_low))
        .expect("add low-score premise failed");

    let origin_high = PremiseOrigin::from_premise_id(PremiseId(1));
    bridge
        .add_hypothesis_with_premise(&forall, None, Some(origin_high))
        .expect("add high-score premise failed");

    assert_eq!(
        bridge.pending_foralls.len(),
        2,
        "Both foralls should generate pending foralls with triggers"
    );

    // Verify that the high-score premise gets higher priority than the low-score one
    let high_pf = bridge
        .pending_foralls
        .iter()
        .find(|pf| pf.origin.as_ref().and_then(QuantifierOrigin::premise_id) == Some(PremiseId(1)))
        .expect("Should find pending forall with PremiseId(1)");
    let low_pf = bridge
        .pending_foralls
        .iter()
        .find(|pf| pf.origin.as_ref().and_then(QuantifierOrigin::premise_id) == Some(PremiseId(2)))
        .expect("Should find pending forall with PremiseId(2)");
    assert!(
        high_pf.total_priority(&bridge.premise_scores)
            > low_pf.total_priority(&bridge.premise_scores),
        "Higher-score premise should win after origin bonus: {} vs {}",
        high_pf.total_priority(&bridge.premise_scores),
        low_pf.total_priority(&bridge.premise_scores)
    );
}

/// Helper: build the common `∀ x : T, f(x) = g(x)` forall used in premise tests.
fn make_fx_eq_gx_forall() -> Expr {
    let ty_t = Expr::const_(Name::from_string("T"), vec![]);
    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let g_x = Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0));
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_applied = Expr::app(Expr::app(Expr::app(eq_const, ty_t.clone()), f_x), g_x);
    Expr::pi(BinderInfo::Default, ty_t, eq_applied)
}

#[test]
fn test_premise_selection_affects_instantiation_order() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let mut scores = HashMap::new();
    scores.insert(PremiseId(100), 1.0);
    scores.insert(PremiseId(200), 0.5);
    scores.insert(PremiseId(300), 0.0);
    bridge.set_premise_scores(scores);

    let forall_fxgx = make_fx_eq_gx_forall();

    // Add in reverse priority order to test sorting
    for id in [300, 100, 200] {
        bridge
            .add_hypothesis_with_premise(
                &forall_fxgx,
                None,
                Some(PremiseOrigin::from_premise_id(PremiseId(id))),
            )
            .unwrap();
    }

    let ids: Vec<_> = bridge
        .pending_foralls
        .iter()
        .filter_map(|pf| pf.origin.as_ref().and_then(QuantifierOrigin::premise_id))
        .collect();

    assert_eq!(
        ids.len(),
        3,
        "All 3 foralls should track their premise origin IDs"
    );
    for id in [100, 200, 300] {
        assert!(
            ids.contains(&PremiseId(id)),
            "PremiseId({id}) should be tracked"
        );
    }

    // Verify that higher-scoring premises get higher priority in pending_foralls.
    // PremiseId(100) has score 1.0, PremiseId(200) has 0.5, PremiseId(300) has 0.0.
    let priority_100 = bridge
        .pending_foralls
        .iter()
        .find(|pf| {
            pf.origin.as_ref().and_then(QuantifierOrigin::premise_id) == Some(PremiseId(100))
        })
        .unwrap()
        .total_priority(&bridge.premise_scores);
    let priority_300 = bridge
        .pending_foralls
        .iter()
        .find(|pf| {
            pf.origin.as_ref().and_then(QuantifierOrigin::premise_id) == Some(PremiseId(300))
        })
        .unwrap()
        .total_priority(&bridge.premise_scores);
    assert!(
        priority_100 > priority_300,
        "Premise with score 1.0 should have >= priority than score 0.0: {} vs {}",
        priority_100,
        priority_300
    );
}
