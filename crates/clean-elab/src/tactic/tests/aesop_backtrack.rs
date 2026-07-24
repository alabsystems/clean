// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop backtracking behavior
//
// These tests validate that aesop implements proper AND-OR tree search
// with backtracking on unsafe rules. They are designed to:
// - FAIL on linear/first-match implementations
// - PASS only with correct AND-OR tree + backtracking
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::{AesopIndexMode, AesopRule, AesopRuleBuilder, AesopRulePhase, Declaration};

/// Setup environment for backtracking tests
/// Creates propositions and implications that require backtracking to solve
fn setup_backtrack_env() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Propositions A, B, C, D, E, X (X used as dead-end in backtrack tests)
    for name in ["A", "B", "C", "D", "E", "X"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    env
}

/// Setup environment for disjunction backtracking
/// Goal: A ∨ B where only B is provable
/// Linear approach: tries `left`, fails on A, gives up
/// Backtracking approach: tries `left`, fails, backtracks to `right`, succeeds on B
fn setup_disjunction_backtrack_env() -> Environment {
    let mut env = setup_backtrack_env();

    // Proof of B (but not A)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hB"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .unwrap();

    env
}

// =============================================================================
// Backtracking Required Tests
// These tests SHOULD FAIL on the current linear implementation
// =============================================================================

/// Test: Disjunction where right side is provable
///
/// Goal: A ∨ B
/// Available: proof of B
///
/// Linear (wrong): tries `left`, can't prove A, fails
/// Backtracking (correct): tries `left`, fails, backtracks to `right`, proves B
#[test]
fn test_aesop_disjunction_backtrack_right() {
    let env = setup_disjunction_backtrack_env();

    // Goal: A ∨ B
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let or_type = Expr::const_(Name::from_string("Or"), vec![]);
    let goal = Expr::app(Expr::app(or_type, a), b);

    // With hypothesis hB : B
    let mut state = ProofState::with_context(
        env,
        goal,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hB".to_string(),
            ty: Expr::const_(Name::from_string("B"), vec![]),
            value: None,
        }],
    );

    // Current implementation will fail here because it tries `left` first
    // (due to priority 50 for both) and doesn't backtrack when A is unprovable
    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop must backtrack from `left` to `right` to prove A ∨ B when only B is available"
    );
    assert!(
        state.goals().is_empty(),
        "all goals must be closed after backtracking"
    );
}

/// Replacement-parity corpus case for unsafe priority plus backtracking.
///
/// A high-priority unsafe apply rule reaches the target first but leaves an
/// unprovable `A` subgoal. AESOP must roll that branch back and still solve the
/// original `A ∨ B` goal via the lower-priority right branch from `hB : B`.
#[test]
fn test_aesop_unsafe_priority_backtracks_after_dead_end() {
    let mut env = setup_disjunction_backtrack_env();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let or = Expr::const_(Name::from_string("Or"), vec![]);
    let goal = Expr::app(Expr::app(or, a.clone()), b.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bad_left"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), goal.clone()),
    })
    .unwrap();
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("bad_left"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hB".to_string(),
            ty: b,
            value: None,
        }],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop must backtrack from the high-priority unsafe dead end: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "all goals must be closed after unsafe-rule backtracking"
    );
}

/// Test: Nested disjunction requiring multiple backtracks
///
/// Goal: (A ∨ B) ∧ (C ∨ D)
/// Available: proofs of B and D (not A or C)
///
/// This requires backtracking TWICE:
/// 1. left of first disjunction fails, backtrack to right
/// 2. left of second disjunction fails, backtrack to right
#[test]
fn test_aesop_nested_backtrack() {
    let mut env = setup_backtrack_env();

    // Add proofs of B and D
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hB"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hD"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("D"), vec![]),
    })
    .unwrap();

    // Goal: (A ∨ B) ∧ (C ∨ D)
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let d = Expr::const_(Name::from_string("D"), vec![]);
    let or = Expr::const_(Name::from_string("Or"), vec![]);
    let and = Expr::const_(Name::from_string("And"), vec![]);

    let a_or_b = Expr::app(Expr::app(or.clone(), a), b.clone());
    let c_or_d = Expr::app(Expr::app(or, c), d.clone());
    let goal = Expr::app(Expr::app(and, a_or_b), c_or_d);

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hB".to_string(),
                ty: b,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hD".to_string(),
                ty: d,
                value: None,
            },
        ],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop must backtrack multiple times to prove nested disjunctions"
    );
    assert!(state.goals().is_empty());
}

/// Test: Implication chain requiring correct application order
///
/// Goal: E
/// Available: A, A → B, B → C, C → D, D → E
///           Also: A → X (dead end)
///
/// Linear (wrong): might apply A → X first, dead end, fails
/// Backtracking (correct): explores all paths, finds A → B → C → D → E
#[test]
fn test_aesop_implication_chain_backtrack() {
    let mut env = setup_backtrack_env();

    // Add the chain
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let d = Expr::const_(Name::from_string("D"), vec![]);
    let e = Expr::const_(Name::from_string("E"), vec![]);

    // Proof of A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hA"),
        level_params: vec![],
        type_: a.clone(),
    })
    .unwrap();

    // A → B
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ab"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), b.clone()),
    })
    .unwrap();

    // B → C
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bc"),
        level_params: vec![],
        type_: Expr::arrow(b.clone(), c.clone()),
    })
    .unwrap();

    // C → D
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("cd"),
        level_params: vec![],
        type_: Expr::arrow(c.clone(), d.clone()),
    })
    .unwrap();

    // D → E
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("de"),
        level_params: vec![],
        type_: Expr::arrow(d.clone(), e.clone()),
    })
    .unwrap();

    // Dead end: A → X (X is unprovable)
    let x = Expr::const_(Name::from_string("X"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ax_deadend"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), x),
    })
    .unwrap();

    // Goal: E
    let mut state = ProofState::with_context(
        env,
        e,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hA".to_string(),
            ty: a,
            value: None,
        }],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop must find the correct chain A → B → C → D → E"
    );
    assert!(state.goals().is_empty());
}

// =============================================================================
// AND-OR Tree Structure Tests
// These verify the search tree is being built correctly
// =============================================================================

/// Test: Conjunction requires both branches (AND node)
///
/// Goal: A ∧ B
/// Available: proofs of A and B
///
/// This tests AND node behavior: both subgoals must be proven
#[test]
fn test_aesop_conjunction_and_node() {
    let mut env = setup_backtrack_env();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // Add proofs
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hA"),
        level_params: vec![],
        type_: a.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hB"),
        level_params: vec![],
        type_: b.clone(),
    })
    .unwrap();

    // Goal: A ∧ B
    let and = Expr::const_(Name::from_string("And"), vec![]);
    let goal = Expr::app(Expr::app(and, a.clone()), b.clone());

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hA".to_string(),
                ty: a,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hB".to_string(),
                ty: b,
                value: None,
            },
        ],
    );

    // This should work even without backtracking (both branches provable)
    let result = aesop(&mut state);

    // Both A and B proofs are in context, so conjunction should be solvable
    assert!(
        result.is_ok(),
        "aesop must solve A ∧ B when both A and B have proofs in context: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "aesop should close all goals when conjunction is provable"
    );
}

// =============================================================================
// Probability Weighting Tests
// These verify goals are explored in probability order
// =============================================================================

/// Test: Probability-weighted goal ordering
///
/// This test verifies that the AND-OR tree with priority queue:
/// 1. Can solve goals when multiple paths exist
/// 2. Uses priority ordering (higher priority candidates first)
///
/// Setup:
/// - left_ has priority 50
/// - right_ has priority 50
/// - Both A and B have proofs, so either path works
///
/// The priority queue ensures systematic exploration by priority.
/// Currently both left/right have equal priority, so the first one
/// added (left) is tried first. When @[aesop] attributes are added
/// (Phase B), user-defined priorities will affect ordering.
#[test]
fn test_aesop_probability_ordering() {
    let mut env = setup_backtrack_env();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // Add proofs for both A and B
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hA"),
        level_params: vec![],
        type_: a.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hB"),
        level_params: vec![],
        type_: b.clone(),
    })
    .unwrap();

    // Goal: A ∨ B
    let or = Expr::const_(Name::from_string("Or"), vec![]);
    let goal = Expr::app(Expr::app(or, a.clone()), b.clone());

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "hA".to_string(),
                ty: a,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hB".to_string(),
                ty: b,
                value: None,
            },
        ],
    );

    // With AND-OR tree and priority queue, aesop explores candidates
    // by priority order and can solve goals via either path.
    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop must solve A ∨ B when both A and B have proofs in context"
    );
    assert!(state.goals().is_empty(), "all goals must be closed");

    // Note: To verify WHICH path was taken (proof term inspection),
    // we would need to track the proof term. This is a Phase C
    // enhancement - for now we verify the priority queue mechanism
    // finds a solution via systematic exploration.
}

// =============================================================================
// Regression Tests - Current Behavior
// These document what currently works (should remain passing)
// =============================================================================

#[test]
fn test_aesop_intro_safe_rule() {
    let env = setup_backtrack_env();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);

    // Goal: A → B → A (intro should handle this)
    let goal = Expr::arrow(a.clone(), Expr::arrow(b, a));

    let mut state = ProofState::new(env, goal);

    // Safe rules (intro) should work without backtracking
    // A → B → A is provable by intro; intro; assumption
    let result = aesop(&mut state);

    // A → B → A is provable by intro; intro; assumption — aesop must solve it
    assert!(
        result.is_ok(),
        "aesop must solve A → B → A via intro + assumption: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "aesop should close all goals for A → B → A"
    );
}

// =============================================================================
// Test Documentation
// =============================================================================

// AND-OR tree properties (Part of #15):
// - AND nodes: all children proven. OR nodes: at least one.
// - Backtracking: on failure, return to try alternatives.
// - Probability: higher-probability branches explored first.
// - Safe rules don't need backtracking; unsafe rules do.
//
// Test categories:
// - test_aesop_*_backtrack*: require backtracking (fail on linear impl)
// - test_aesop_*_and_node: test AND behavior
// - test_aesop_probability_*: test probability ordering
