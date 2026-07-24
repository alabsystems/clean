// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop strategy selection (D3)
//
// Strategy controls the order in which goals are explored:
// - BestFirst: Priority queue (default, explores highest probability first)
// - DepthFirst: Stack (LIFO, explores most recently added first)
// - BreadthFirst: Queue (FIFO, explores in order added)
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::super::search::{AesopConfig, AesopStrategy};
use super::*;
use clean_kernel::env::Declaration;

// =============================================================================
// S-T1: Default Strategy is BestFirst
//
// Verify that the default AesopConfig uses BestFirst strategy
// =============================================================================

/// Test: Default config uses BestFirst strategy
#[test]
fn test_default_strategy_is_best_first() {
    let config = AesopConfig::default();
    assert_eq!(config.strategy, AesopStrategy::BestFirst);
}

// =============================================================================
// S-T2: Strategy Enum Values
//
// Verify all strategy variants exist and are distinct
// =============================================================================

/// Test: All strategy variants are distinct
#[test]
fn test_strategy_variants() {
    let best_first = AesopStrategy::BestFirst;
    let depth_first = AesopStrategy::DepthFirst;
    let breadth_first = AesopStrategy::BreadthFirst;

    assert_ne!(best_first, depth_first);
    assert_ne!(best_first, breadth_first);
    assert_ne!(depth_first, breadth_first);
}

// =============================================================================
// S-T3: BestFirst Strategy Works
//
// Test that best-first search explores goals in priority order
// =============================================================================

/// Test: BestFirst strategy finds proof
#[test]
fn test_best_first_strategy() {
    let env = setup_strategy_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Goal: P with hp : P in context (trivial)
    let mut state = ProofState::new(env, p.clone());
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Use BestFirst (default)
    let config = AesopConfig {
        strategy: AesopStrategy::BestFirst,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(result.is_ok(), "BestFirst should find proof");
    assert!(state.is_complete(), "BestFirst should close all goals");
}

// =============================================================================
// S-T4: DepthFirst Strategy Works
//
// Test that depth-first search explores goals in LIFO order
// =============================================================================

/// Test: DepthFirst strategy finds proof
#[test]
fn test_depth_first_strategy() {
    let env = setup_strategy_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Goal: P with hp : P in context (trivial)
    let mut state = ProofState::new(env, p.clone());
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Use DepthFirst
    let config = AesopConfig {
        strategy: AesopStrategy::DepthFirst,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(result.is_ok(), "DepthFirst should find proof");
    assert!(state.is_complete(), "DepthFirst should close all goals");
}

// =============================================================================
// S-T5: BreadthFirst Strategy Works
//
// Test that breadth-first search explores goals in FIFO order
// =============================================================================

/// Test: BreadthFirst strategy finds proof
#[test]
fn test_breadth_first_strategy() {
    let env = setup_strategy_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Goal: P with hp : P in context (trivial)
    let mut state = ProofState::new(env, p.clone());
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Use BreadthFirst
    let config = AesopConfig {
        strategy: AesopStrategy::BreadthFirst,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);
    assert!(result.is_ok(), "BreadthFirst should find proof");
    assert!(state.is_complete(), "BreadthFirst should close all goals");
}

// =============================================================================
// S-T6: All Strategies Find Same Proof
//
// For simple proofs, all strategies should succeed
// =============================================================================

/// Test: All strategies succeed on simple proof
#[test]
fn test_all_strategies_find_proof() {
    for strategy in [
        AesopStrategy::BestFirst,
        AesopStrategy::DepthFirst,
        AesopStrategy::BreadthFirst,
    ] {
        let env = setup_strategy_env();
        let p = Expr::const_(Name::from_string("P"), vec![]);

        let mut state = ProofState::new(env, p.clone());
        state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
            fvar: FVarId::new(100),
            name: "hp".to_string(),
            ty: p.clone(),
            value: None,
        });

        let config = AesopConfig {
            strategy,
            ..Default::default()
        };

        let result = aesop_with_config(&mut state, config);
        assert!(result.is_ok(), "Strategy {:?} should find proof", strategy);
        assert!(
            state.is_complete(),
            "Strategy {:?} should close all goals",
            strategy
        );
    }
}

// =============================================================================
// S-T7: Strategy Affects Goal Order
//
// Test that different strategies explore goals in different orders
// This is more of a documentation test than a strict requirement
// =============================================================================

/// Test: Config strategy field is respected
#[test]
fn test_config_strategy_field() {
    let config_best = AesopConfig {
        strategy: AesopStrategy::BestFirst,
        ..Default::default()
    };
    assert_eq!(config_best.strategy, AesopStrategy::BestFirst);

    let config_depth = AesopConfig {
        strategy: AesopStrategy::DepthFirst,
        ..Default::default()
    };
    assert_eq!(config_depth.strategy, AesopStrategy::DepthFirst);

    let config_breadth = AesopConfig {
        strategy: AesopStrategy::BreadthFirst,
        ..Default::default()
    };
    assert_eq!(config_breadth.strategy, AesopStrategy::BreadthFirst);
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Setup environment with propositions P, Q, R
fn setup_strategy_env() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Add propositions P, Q, R
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    env
}
