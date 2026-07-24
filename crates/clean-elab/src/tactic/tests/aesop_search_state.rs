// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for AesopSearchState diagnostics and enhanced search engine features.
//!
//! Covers:
//! - AesopConfig defaults and max_iterations field
//! - AesopSearchState construction and diagnostic accessors
//! - RuleAttempt tracking through search
//! - Iteration limit enforcement
//! - Search diagnostics in error messages
//!
//! Part of #3082: Aesop tactic enhancements

use super::super::search::{AesopConfig, AesopStrategy};
use super::*;

// =============================================================================
// AesopConfig Tests
// =============================================================================

/// Test: AesopConfig::default() has max_iterations = 1000
#[test]
fn test_aesop_config_default_max_iterations() {
    let config = AesopConfig::default();
    assert_eq!(
        config.max_iterations, 1000,
        "default max_iterations should be 1000"
    );
}

/// Test: AesopConfig fields are independently settable
#[test]
fn test_aesop_config_custom_max_iterations() {
    let config = AesopConfig {
        max_iterations: 42,
        ..Default::default()
    };
    assert_eq!(config.max_iterations, 42);
    // Other fields should retain defaults
    assert_eq!(config.max_depth, 10);
    assert_eq!(config.max_goals, 100);
    assert!(config.use_simp);
    assert!(config.use_unfold);
}

/// Test: AesopConfig with all fields set explicitly
#[test]
fn test_aesop_config_all_fields() {
    let config = AesopConfig {
        max_depth: 5,
        max_goals: 50,
        max_iterations: 200,
        use_simp: false,
        use_unfold: false,
        strategy: AesopStrategy::DepthFirst,
        rule_sets: vec![Name::from_string("MyRules")],
    };
    assert_eq!(config.max_depth, 5);
    assert_eq!(config.max_goals, 50);
    assert_eq!(config.max_iterations, 200);
    assert!(!config.use_simp);
    assert!(!config.use_unfold);
    assert_eq!(config.strategy, AesopStrategy::DepthFirst);
    assert_eq!(config.rule_sets.len(), 1);
}

// =============================================================================
// AesopSearchState Tests
// =============================================================================

/// Test: AesopSearchState starts with zero iterations and zero attempts
#[test]
fn test_search_state_initial_counters() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let ps = ProofState::new(env, target);
    let goal = ps.current_goal().unwrap().clone();

    let search_state = AesopSearchState::new(goal);
    assert_eq!(
        search_state.iteration_count(),
        0,
        "initial iteration_count should be 0"
    );
    assert_eq!(
        search_state.total_attempts(),
        0,
        "initial total_attempts should be 0"
    );
    assert_eq!(
        search_state.successful_attempts(),
        0,
        "initial successful_attempts should be 0"
    );
}

/// Test: AesopSearchState tree root is accessible
#[test]
fn test_search_state_tree_root() {
    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let ps = ProofState::new(env, target);
    let goal = ps.current_goal().unwrap().clone();

    let search_state = AesopSearchState::new(goal);
    let tree = search_state.tree();

    // Root should exist and be neither proven nor unprovable initially
    assert!(
        !tree.is_root_proven(),
        "root should not be proven initially"
    );
    assert!(
        !tree.is_root_unprovable(),
        "root should not be unprovable initially"
    );
}

// =============================================================================
// RuleAttempt Tracking Tests
// =============================================================================

/// Test: RuleAttempt fields are correctly stored
#[test]
fn test_rule_attempt_fields() {
    let attempt = RuleAttempt {
        rule_name: "safe_rules".to_string(),
        success: true,
        subgoals_produced: 0,
    };
    assert_eq!(attempt.rule_name, "safe_rules");
    assert!(attempt.success);
    assert_eq!(attempt.subgoals_produced, 0);
}

/// Test: Failed RuleAttempt
#[test]
fn test_rule_attempt_failed() {
    let attempt = RuleAttempt {
        rule_name: "candidate_0".to_string(),
        success: false,
        subgoals_produced: 0,
    };
    assert_eq!(attempt.rule_name, "candidate_0");
    assert!(!attempt.success);
}

/// Test: RuleAttempt with subgoals
#[test]
fn test_rule_attempt_with_subgoals() {
    let attempt = RuleAttempt {
        rule_name: "candidate_1".to_string(),
        success: true,
        subgoals_produced: 3,
    };
    assert!(attempt.success);
    assert_eq!(attempt.subgoals_produced, 3);
}

// =============================================================================
// Iteration Limit Enforcement Tests
// =============================================================================

/// Test: max_iterations limits search effort on unprovable goals
#[test]
fn test_max_iterations_limits_search() {
    let env = setup_search_state_env();
    // R has no proof — search should exhaust iterations
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, r);

    let config = AesopConfig {
        max_iterations: 5,
        use_simp: false,
        use_unfold: false,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(
        result.is_err(),
        "aesop should fail on unprovable goal within max_iterations"
    );
}

/// Test: max_iterations = 1 still allows one expansion
#[test]
fn test_max_iterations_one_allows_single_expansion() {
    let env = setup_search_state_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Trivially provable with assumption (hp : P in context)
    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "hp".to_string(),
            ty: p,
            value: None,
        }],
    );

    let config = AesopConfig {
        max_iterations: 1,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    // With max_iterations=1, aesop gets one iteration to try closing the goal.
    // A trivial assumption goal should succeed within 1 iteration.
    assert!(
        result.is_ok(),
        "trivial assumption goal should succeed within 1 iteration, got: {:?}",
        result.err()
    );
}

// =============================================================================
// Search Diagnostics in Error Messages
// =============================================================================

/// Test: SearchExhausted errors include iteration and attempt counts
#[test]
fn test_search_exhausted_error_includes_diagnostics() {
    let env = setup_search_state_env();
    // R has no proof — search will fail
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, r);

    let config = AesopConfig {
        max_iterations: 10,
        use_simp: false,
        use_unfold: false,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(result.is_err());

    match result.unwrap_err() {
        TacticError::SearchExhausted { tactic, detail } => {
            assert_eq!(tactic, "aesop");
            // Detail should mention iterations and rule attempts
            assert!(
                detail.contains("iteration"),
                "error detail should mention iterations: {}",
                detail
            );
            assert!(
                detail.contains("rule attempt"),
                "error detail should mention rule attempts: {}",
                detail
            );
        }
        other => panic!("expected SearchExhausted, got: {:?}", other),
    }
}

// =============================================================================
// Integration: Safe Rules with Diagnostics
// =============================================================================

/// Test: Successful aesop search closes all goals and leaves state complete
#[test]
fn test_aesop_success_closes_all_goals() {
    let env = setup_search_state_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Goal: P → P (solvable by intro + assumption)
    let goal = Expr::arrow(p.clone(), p);
    let mut state = ProofState::new(env, goal);

    let config = AesopConfig {
        max_iterations: 100,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(
        result.is_ok(),
        "P → P should be solvable: {:?}",
        result.err()
    );
    assert!(state.is_complete(), "all goals should be closed");
}

/// Test: aesop with normalization enabled finds proof via assumption
#[test]
fn test_aesop_with_normalization() {
    let env = setup_search_state_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Trivially provable: P with hp in context
    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(100),
            name: "hp".to_string(),
            ty: p,
            value: None,
        }],
    );

    let config = AesopConfig {
        use_simp: true,
        max_iterations: 100,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(
        result.is_ok(),
        "aesop with normalization should find proof via assumption: {:?}",
        result.err()
    );
}

// =============================================================================
// AesopConfig with Strategy + max_iterations interaction
// =============================================================================

/// Test: max_iterations is independent of strategy
#[test]
fn test_max_iterations_independent_of_strategy() {
    for strategy in [
        AesopStrategy::BestFirst,
        AesopStrategy::DepthFirst,
        AesopStrategy::BreadthFirst,
    ] {
        let env = setup_search_state_env();
        let r = Expr::const_(Name::from_string("R"), vec![]);
        let mut state = ProofState::new(env, r);

        let config = AesopConfig {
            strategy,
            max_iterations: 3,
            use_simp: false,
            use_unfold: false,
            ..Default::default()
        };

        let result = aesop_with_config(&mut state, config);
        assert!(
            result.is_err(),
            "unprovable goal should fail regardless of strategy {:?}",
            strategy
        );
    }
}

// =============================================================================
// Helper
// =============================================================================

/// Setup environment with propositions P, Q, R (R has no proof)
fn setup_search_state_env() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Declare propositions P, Q, R
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // Add proof axioms for P and Q only (R is unprovable)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp_ax"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hq_ax"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .unwrap();

    env
}
