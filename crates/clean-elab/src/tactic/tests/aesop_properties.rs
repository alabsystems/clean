// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Property-based tests for aesop search invariants
//
// These tests verify structural properties that ANY correct aesop implementation
// must satisfy, regardless of specific search strategy.
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::Declaration;
use proptest::prelude::*;

// =============================================================================
// Property: Soundness
// If aesop returns Ok, the proof state must have no remaining goals
// =============================================================================

#[test]
fn property_soundness_no_remaining_goals() {
    // When aesop succeeds, there must be no remaining goals
    let env = setup_env_for_property_tests();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Create provable goal using hypothesis
    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p,
            value: None,
        }],
    );

    // Goal P with hp : P in context — trivially provable via assumption.
    // Aesop MUST succeed here; failure indicates a regression.
    aesop(&mut state).expect("aesop must prove P from hp : P (trivially provable)");

    // Soundness property: success implies no goals
    assert!(
        state.goals().is_empty(),
        "SOUNDNESS VIOLATION: aesop returned Ok but goals remain: {:?}",
        state.goals().len()
    );
}

/// Setup environment for property tests
///
/// NOTE: This is different from the shared `setup_env_with_and_or()` in mod.rs:
/// - Adds more propositions (P, Q, R, S, T) for testing unprovable goals
/// - Uses `hp`/`hq` naming convention for proofs (matching test LocalDecl names)
fn setup_env_for_property_tests() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    for name in ["P", "Q", "R", "S", "T"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // Add proofs
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hp"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hq"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .unwrap();

    env
}

// =============================================================================
// Property: Determinism
// Same input should produce same result (for deterministic configuration)
// =============================================================================

#[test]
fn property_determinism_same_result() {
    let env1 = setup_env_for_property_tests();
    let env2 = setup_env_for_property_tests();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    let mut state1 = ProofState::with_context(
        env1,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p.clone(),
            value: None,
        }],
    );

    let mut state2 = ProofState::with_context(
        env2,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p,
            value: None,
        }],
    );

    let result1 = aesop(&mut state1);
    let result2 = aesop(&mut state2);

    // Determinism property: same input produces same success/failure
    assert_eq!(
        result1.is_ok(),
        result2.is_ok(),
        "DETERMINISM VIOLATION: same input produced different results"
    );
}

// =============================================================================
// Property: Safe Rules Are Idempotent
// Applying safe rules multiple times shouldn't change provability
// =============================================================================

#[test]
fn property_safe_rules_idempotent() {
    let env = setup_env_for_property_tests();

    // Goal: P → P (requires intro safe rule)
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let goal = Expr::arrow(p.clone(), p);

    let mut state = ProofState::new(env.clone(), goal.clone());

    // First application
    let result1 = aesop(&mut state);
    let goals_after_1 = state.goals().len();

    // Create fresh state and run again
    let mut state2 = ProofState::new(env, goal);
    let result2 = aesop(&mut state2);
    let goals_after_2 = state2.goals().len();

    // Idempotent property: repeated applications produce same result
    assert_eq!(
        result1.is_ok(),
        result2.is_ok(),
        "IDEMPOTENT VIOLATION: repeated aesop calls produced different success"
    );
    assert_eq!(
        goals_after_1, goals_after_2,
        "IDEMPOTENT VIOLATION: goal counts differ after repeated calls"
    );
}

// =============================================================================
// Property: Monotonicity
// Adding more hypotheses should not make provable goals unprovable
// =============================================================================

#[test]
fn property_monotonicity_more_hyps_no_worse() {
    let env1 = setup_env_for_property_tests();
    let env2 = setup_env_for_property_tests();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // State with minimal hypotheses
    let mut state_minimal = ProofState::with_context(
        env1,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p.clone(),
            value: None,
        }],
    );

    // State with extra hypothesis (should be at least as good)
    let mut state_extra = ProofState::with_context(
        env2,
        p.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hp".to_string(),
                ty: p,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hq".to_string(),
                ty: q,
                value: None,
            },
        ],
    );

    let result_minimal = aesop(&mut state_minimal);
    let result_extra = aesop(&mut state_extra);

    // Monotonicity property: if minimal succeeds, extra must also succeed
    if result_minimal.is_ok() {
        assert!(
            result_extra.is_ok(),
            "MONOTONICITY VIOLATION: adding hypotheses made proof fail"
        );
    }
}

// =============================================================================
// Property: Max Depth Bounds Search
// Setting max_depth = 0 should prevent any deep search
// =============================================================================

#[test]
fn property_max_depth_respected() {
    let env = setup_env_for_property_tests();
    // Use R which has no proof in the environment (P and Q have hp and hq)
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // Unprovable goal (no hypothesis for R)
    let mut state = ProofState::new(env, r);

    let config = AesopConfig {
        max_depth: 0,
        max_goals: 1,
        use_simp: false,
        use_unfold: false,
        ..Default::default()
    };

    let result = aesop_with_config(&mut state, config);

    // With max_depth 0, aesop shouldn't explore deep branches
    // It should fail quickly rather than hang
    assert!(
        result.is_err(),
        "Expected failure with max_depth=0 on unprovable goal"
    );
}

// =============================================================================
// Property: Max Goals Bounds Expansion
// Setting max_goals should limit how many goals get processed
// =============================================================================

#[test]
fn property_max_goals_respected() {
    let env = setup_env_for_property_tests();

    // Create a goal that would generate many subgoals using unprovable props
    // R and S have no proof axioms (only P and Q have proofs in setup_env)
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let s = Expr::const_(Name::from_string("S"), vec![]);
    let and = Expr::const_(Name::from_string("And"), vec![]);

    // R ∧ S ∧ R ∧ S (generates 4 subgoals with split, all unprovable)
    let rs = Expr::app(Expr::app(and.clone(), r.clone()), s.clone());
    let goal = Expr::app(Expr::app(and, rs.clone()), rs);

    let mut state = ProofState::new(env, goal);

    let config = AesopConfig {
        max_depth: 10,
        max_goals: 1, // Very restrictive
        use_simp: false,
        use_unfold: false,
        ..Default::default()
    };

    // With max_goals = 1, aesop cannot solve a 4-subgoal conjunction of unprovable props
    let result = aesop_with_config(&mut state, config);
    assert!(
        result.is_err(),
        "aesop with max_goals=1 should fail on a 4-subgoal conjunction of unprovable propositions"
    );
    assert!(
        !state.is_complete(),
        "proof should not be complete under max_goals=1 restriction"
    );
}

// =============================================================================
// Property: Completeness for Safe Goals
// Goals solvable by safe rules alone should always succeed
// =============================================================================

#[test]
fn property_safe_rule_completeness() {
    let env = setup_env_for_property_tests();

    // Goal: P → Q → P (solvable with just intro + assumption)
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let goal = Expr::arrow(p.clone(), Expr::arrow(q, p));

    let mut state = ProofState::new(env, goal);

    let result = aesop(&mut state);

    // P → Q → P is solvable with just intro + assumption (safe rules)
    assert!(
        result.is_ok(),
        "P → Q → P should be solvable by safe rules, got: {:?}",
        result.err()
    );
    assert!(
        state.is_complete(),
        "safe rules should close P → Q → P goal completely"
    );
}

// =============================================================================
// Property-Based Test Using proptest
// =============================================================================

proptest! {
    /// Property: Config validation
    /// Any non-negative config values should be accepted
    #[test]
    fn prop_config_valid(max_depth in 0usize..100, max_goals in 1usize..1000) {
        let config = AesopConfig {
            max_depth,
            max_goals,
            use_simp: true,
            use_unfold: true,
            ..Default::default()
        };

        // Config should be created without panic
        prop_assert_eq!(config.max_depth, max_depth);
        prop_assert_eq!(config.max_goals, max_goals);
    }

    /// Property: Termination
    /// Aesop should always terminate within bounds
    #[test]
    fn prop_termination(depth in 1usize..5, goals in 1usize..10) {
        let env = setup_env_for_property_tests();
        // Use R which has no proof axiom (only P and Q have proofs in setup_env)
        let r = Expr::const_(Name::from_string("R"), vec![]);
        let mut state = ProofState::new(env, r);

        let config = AesopConfig {
            max_depth: depth,
            max_goals: goals,
            use_simp: false,
            use_unfold: false,
            ..Default::default()
        };

        // Must terminate (not hang) and fail — R has no proof axiom
        let result = aesop_with_config(&mut state, config);
        prop_assert!(result.is_err(), "proposition R (no proof axiom) should be unprovable by aesop");
    }
}

// =============================================================================
// Invariant Tests for Future AND-OR Tree Implementation
// =============================================================================

// AND-OR tree invariants (Part of #15):
// 1. AND nodes: all children must be solved. OR nodes: at least one.
// 2. Probability: Π(children) for AND, max(children) for OR.
// 3. Backtracking: state restored on branch failure (undo side effects).
// 4. Safe rules: mark goals inactive, no backtracking needed.
// 5. Termination: bounded by max_depth and max_goals.
