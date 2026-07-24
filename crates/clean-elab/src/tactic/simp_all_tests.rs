// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::simp_all::{SimpAllConfig, SimpAllResult, SimpAllState, SimpHypothesis, SimpStepResult};
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

fn mk_prop() -> Expr {
    Expr::sort(Level::zero())
}

fn mk_true() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}

fn mk_nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn mk_eq(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_simp_all_config_default() {
    let config = SimpAllConfig::default();

    assert_eq!(config.max_iterations, 100);
    assert!(!config.only_mode);
    assert!(config.lemmas.is_empty());
    assert!(!config.use_arith);
    assert!(config.remove_trivial);
    assert!(!config.trace);
}

#[test]
fn test_simp_all_config_only() {
    let lemmas = vec![Name::from_string("h1"), Name::from_string("h2")];
    let config = SimpAllConfig::only(lemmas.clone());

    assert!(config.only_mode);
    assert_eq!(config.lemmas, lemmas);
    assert_eq!(config.max_iterations, 100);
    assert!(!config.use_arith);
}

#[test]
fn test_simp_all_config_with_arith() {
    let config = SimpAllConfig::with_arith();

    assert!(config.use_arith);
    assert_eq!(config.max_iterations, 100);
    assert!(!config.only_mode);
    assert!(config.remove_trivial);
}

#[test]
fn test_simp_all_config_to_simp_config() {
    let lemmas = vec![
        Name::from_string("h_local"),
        Name::from_string("arith_norm"),
    ];
    let config = SimpAllConfig::new()
        .with_max_iterations(23)
        .with_only_mode(true)
        .with_lemmas(lemmas.clone())
        .with_use_arith(true);
    let simp_config = config.to_simp_config();

    assert_eq!(simp_config.max_steps, 23);
    assert!(simp_config.only);
    assert!(simp_config.only_simplify);
    assert!(simp_config.use_hypotheses);
    assert_eq!(
        simp_config.extra_lemmas,
        lemmas.iter().map(ToString::to_string).collect::<Vec<_>>()
    );
    assert!(simp_config.beta);
    assert!(simp_config.eta);
}

#[test]
fn test_simp_all_state_new() {
    let hypotheses = vec![
        SimpHypothesis::new(Name::from_string("h1"), mk_true()),
        SimpHypothesis::new(
            Name::from_string("h2"),
            mk_eq(&mk_nat(), &mk_const("a"), &mk_const("b")),
        ),
    ];
    let goal = mk_eq(&mk_nat(), &mk_const("a"), &mk_const("b"));
    let state = SimpAllState::new(hypotheses.clone(), goal.clone());

    assert_eq!(state.hypotheses, hypotheses);
    assert_eq!(state.goal, goal);
    assert!(!state.goal_changed);
    assert_eq!(state.iterations, 0);
}

#[test]
fn test_simp_all_state_empty_hypotheses() {
    let goal = mk_prop();
    let state = SimpAllState::new(vec![], goal.clone());

    assert!(state.hypotheses.is_empty());
    assert_eq!(state.goal, goal);
    assert!(!state.goal_changed);
    assert_eq!(state.iterations, 0);
}

#[test]
fn test_simp_hypothesis_trivial_true() {
    let mut hyp = SimpHypothesis::new(Name::from_string("h_true"), mk_true());
    let result = hyp.simplify(&SimpAllConfig::default());

    assert_eq!(result, SimpStepResult::Removed);
    assert!(hyp.changed);
    assert!(hyp.removed);
    assert_eq!(hyp.expr, mk_true());
}

#[test]
fn test_simp_hypothesis_trivial_equality() {
    let a = mk_const("a");
    let mut hyp = SimpHypothesis::new(Name::from_string("h_eq"), mk_eq(&mk_nat(), &a, &a));
    let result = hyp.simplify(&SimpAllConfig::default());

    assert_eq!(result, SimpStepResult::Removed);
    assert!(hyp.changed);
    assert!(hyp.removed);
    assert_eq!(hyp.expr, mk_eq(&mk_nat(), &a, &a));
}

#[test]
fn test_simp_hypothesis_no_change() {
    let a = mk_const("a");
    let b = mk_const("b");
    let original = mk_eq(&mk_nat(), &a, &b);
    let mut hyp = SimpHypothesis::new(Name::from_string("h_keep"), original.clone());
    let result = hyp.simplify(&SimpAllConfig::default());

    assert_eq!(result, SimpStepResult::Unchanged);
    assert!(!hyp.changed);
    assert!(!hyp.removed);
    assert_eq!(hyp.expr, original);
}

#[test]
fn test_simp_goal_no_change() {
    let goal = mk_eq(&mk_nat(), &mk_const("x"), &mk_const("y"));
    let mut state = SimpAllState::new(vec![], goal.clone());
    let result = state.simplify_goal(&SimpAllConfig::default());

    assert_eq!(result, SimpStepResult::Unchanged);
    assert_eq!(state.goal, goal);
    assert!(!state.goal_changed);
}

#[test]
fn test_simp_all_state_run_one_pass() {
    let a = mk_const("a");
    let b = mk_const("b");
    let mut state = SimpAllState::new(
        vec![
            SimpHypothesis::new(Name::from_string("h_true"), mk_true()),
            SimpHypothesis::new(Name::from_string("h_refl"), mk_eq(&mk_nat(), &a, &a)),
            SimpHypothesis::new(Name::from_string("h_rw"), mk_eq(&mk_nat(), &a, &b)),
        ],
        mk_eq(&mk_nat(), &a, &b),
    );

    let changed = state.run_one_pass(&SimpAllConfig::default());

    assert!(changed);
    assert_eq!(state.iterations, 1);
    assert!(state.hypotheses[0].removed);
    assert!(state.hypotheses[1].removed);
    assert!(!state.hypotheses[2].removed);
    assert!(state.goal_changed);
    assert_eq!(state.goal, mk_eq(&mk_nat(), &b, &b));
}

#[test]
fn test_simp_all_state_run_fixpoint() {
    let a = mk_const("a");
    let b = mk_const("b");
    let c = mk_const("c");
    let mut state = SimpAllState::new(
        vec![
            SimpHypothesis::new(Name::from_string("h_ab"), mk_eq(&mk_nat(), &a, &b)),
            SimpHypothesis::new(Name::from_string("h_bc"), mk_eq(&mk_nat(), &b, &c)),
        ],
        mk_eq(&mk_nat(), &a, &c),
    );

    let result = state.run_fixpoint(&SimpAllConfig::default());

    assert!(result.changed);
    assert!(result.goal_changed);
    assert!(result.reached_fixpoint);
    assert_eq!(result.goal, mk_eq(&mk_nat(), &c, &c));
    assert_eq!(result.iterations, 3);
    assert_eq!(result.changed_hypotheses, 0);
    assert_eq!(result.removed_hypotheses, 0);
}

#[test]
fn test_simp_all_state_max_iterations() {
    let a = mk_const("a");
    let b = mk_const("b");
    let c = mk_const("c");
    let mut state = SimpAllState::new(
        vec![
            SimpHypothesis::new(Name::from_string("h_ab"), mk_eq(&mk_nat(), &a, &b)),
            SimpHypothesis::new(Name::from_string("h_bc"), mk_eq(&mk_nat(), &b, &c)),
        ],
        mk_eq(&mk_nat(), &a, &c),
    );
    let config = SimpAllConfig::new().with_max_iterations(1);

    let result = state.run_fixpoint(&config);

    assert!(result.changed);
    assert!(result.goal_changed);
    assert!(!result.reached_fixpoint);
    assert_eq!(result.iterations, 1);
    assert_eq!(result.goal, mk_eq(&mk_nat(), &b, &c));
}

#[test]
fn test_simp_all_result_fields() {
    let hypothesis = SimpHypothesis {
        name: Name::from_string("h"),
        expr: mk_true(),
        changed: true,
        removed: true,
    };
    let result = SimpAllResult {
        hypotheses: vec![hypothesis.clone()],
        goal: mk_eq(&mk_nat(), &mk_const("x"), &mk_const("x")),
        changed: true,
        goal_changed: true,
        iterations: 2,
        reached_fixpoint: true,
        changed_hypotheses: 1,
        removed_hypotheses: 1,
    };

    assert_eq!(result.hypotheses.len(), 1);
    assert_eq!(result.hypotheses[0], hypothesis);
    assert_eq!(
        result.goal,
        mk_eq(&mk_nat(), &mk_const("x"), &mk_const("x"))
    );
    assert!(result.changed);
    assert!(result.goal_changed);
    assert_eq!(result.iterations, 2);
    assert!(result.reached_fixpoint);
    assert_eq!(result.changed_hypotheses, 1);
    assert_eq!(result.removed_hypotheses, 1);
}

#[test]
fn test_simp_all_config_builder_chain() {
    let lemmas = vec![Name::from_string("h1"), Name::from_string("h2")];
    let config = SimpAllConfig::new()
        .with_max_iterations(7)
        .with_only_mode(true)
        .with_lemmas(lemmas.clone())
        .with_use_arith(true)
        .with_remove_trivial(false)
        .with_trace(true);

    assert_eq!(config.max_iterations, 7);
    assert!(config.only_mode);
    assert_eq!(config.lemmas, lemmas);
    assert!(config.use_arith);
    assert!(!config.remove_trivial);
    assert!(config.trace);
}
