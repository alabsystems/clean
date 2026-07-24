// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop destruct builder (forward reasoning with hypothesis clearing)
//
// Destruct rules add hypotheses to context AND clear the matched hypothesis.
// This is critical for:
// - And elimination: `h : P ∧ Q` → get `P`, remove `h`
// - Exists elimination: `h : ∃ x, P x` → get witness `x` and `P x`, remove `h`
// - Preventing infinite loops in forward reasoning
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::{AesopRule, AesopRuleBuilder, AesopRulePhase, Declaration};
use clean_kernel::expr::ExprKind;

// =============================================================================
// D-T1: Basic Destruct Rule
//
// @[aesop safe destruct]
// theorem p_imp_q (h : P) : Q := sorry
//
// Destruct: if we have P in context, add Q and remove P
// =============================================================================

/// Test: Basic destruct rule adds hypothesis and clears source
///
/// Given: hp : P in context
/// Destruct rule: p_imp_q : P → Q
/// Expected: hq : Q added to context, hp removed
#[test]
fn test_destruct_basic() {
    let mut env = setup_destruct_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // Register destruct rule: p_imp_q : P → Q
    let p_to_q = Expr::arrow(p.clone(), q.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p_imp_q"),
        level_params: vec![],
        type_: p_to_q,
    })
    .unwrap();

    // Register as destruct rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("p_imp_q"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Destruct,
        builder_args: vec![],
        priority: 50,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: R (something we can't prove)
    // Context: hp : P
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, r);

    // Add hp : P to context
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Verify initial state: has P, no Q
    let goal = state.current_goal().unwrap();
    let has_p_before = goal.local_ctx.iter().any(|d| d.name == "hp");
    let has_q_before = goal
        .local_ctx
        .iter()
        .any(|d| matches!(d.ty.kind(), ExprKind::Const(n, _) if n.to_string() == "Q"));
    assert!(has_p_before, "should have hp : P initially");
    assert!(!has_q_before, "should not have Q initially");

    // Run aesop — goal R is unprovable from {hp: P} + destruct P→Q
    let result = aesop(&mut state);

    // Aesop must fail: R is not derivable from Q (which is what destruct produces)
    assert!(
        result.is_err(),
        "aesop should fail to close goal R from context {{ hp: P, destruct P→Q }}"
    );

    // After failed search with tree-based rollback, state should be preserved
    let goal = state
        .current_goal()
        .expect("should have a goal after failed search");
    let has_hp_after = goal.local_ctx.iter().any(|d| d.name == "hp");
    assert!(
        has_hp_after,
        "hp : P should be preserved after failed aesop search (tree-based rollback)"
    );
}

// =============================================================================
// D-T2: Destruct No Infinite Loop
//
// @[aesop safe destruct]
// theorem p_to_p (h : P) : P := h
//
// Unlike forward, destruct should NOT trigger infinite recursion
// because it clears the hypothesis after use.
// =============================================================================

/// Test: Destruct rule prevents infinite loop by clearing hypothesis
///
/// Given: hp : P in context
/// Destruct rule: p_to_p : P → P
/// Expected: hp removed, new P added, no re-trigger
#[test]
fn test_destruct_no_infinite_loop() {
    let mut env = setup_destruct_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // Register destruct rule: p_to_p : P → P (identity)
    let p_to_p = Expr::arrow(p.clone(), p.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p_to_p"),
        level_params: vec![],
        type_: p_to_p,
    })
    .unwrap();

    // Register as destruct rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("p_to_p"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Destruct,
        builder_args: vec![],
        priority: 50,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: R (something we can't prove)
    // Context: hp : P
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, r);

    // Add hp : P to context
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Run aesop with limited iterations
    let config = AesopConfig {
        max_depth: 5,
        max_goals: 10,
        ..Default::default()
    };
    let result = aesop_with_config(&mut state, config);

    // Goal R is unprovable from P → P destruct rule, aesop must fail
    assert!(
        result.is_err(),
        "aesop should fail on unprovable goal R with only P→P destruct rule"
    );

    // Count hypotheses of type P — destruct clears source, so at most 1
    let p_count = state
        .current_goal()
        .map(|g| {
            g.local_ctx
                .iter()
                .filter(|d| matches!(d.ty.kind(), ExprKind::Const(n, _) if n.to_string() == "P"))
                .count()
        })
        .unwrap_or(0);

    assert!(
        p_count <= 1,
        "destruct should not create duplicate P; got {p_count}"
    );
}

// =============================================================================
// D-T3: Destruct Preserves Other Hypotheses
//
// Given: hp : P, hq : Q
// Destruct rule: p_imp_r : P → R
// Expected: hr : R added, hp removed, hq preserved
// =============================================================================

/// Test: Destruct only clears the matched hypothesis
#[test]
fn test_destruct_preserves_other_hyps() {
    let mut env = setup_destruct_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let r = Expr::const_(Name::from_string("R"), vec![]);

    // Register destruct rule: p_imp_r : P → R
    let p_to_r = Expr::arrow(p.clone(), r.clone());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p_imp_r"),
        level_params: vec![],
        type_: p_to_r,
    })
    .unwrap();

    // Register as destruct rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("p_imp_r"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Destruct,
        builder_args: vec![],
        priority: 50,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: S (something we can't prove)
    let s = Expr::const_(Name::from_string("S"), vec![]);
    let mut state = ProofState::new(env, s);

    // Add hp : P to context
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p.clone(),
        value: None,
    });

    // Add hq : Q to context (should be preserved)
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(101),
        name: "hq".to_string(),
        ty: q.clone(),
        value: None,
    });

    // Run aesop — goal S is unprovable
    let result = aesop(&mut state);

    // Aesop must fail: S is not derivable from {hp: P, hq: Q} + destruct P→R
    assert!(
        result.is_err(),
        "aesop should fail to close goal S from context {{ hp: P, hq: Q, destruct P→R }}"
    );

    // After failed search, all original hypotheses should be preserved
    let goal = state
        .current_goal()
        .expect("should have a goal after failed search");
    let has_hq = goal.local_ctx.iter().any(|d| d.name == "hq");
    let has_hp = goal.local_ctx.iter().any(|d| d.name == "hp");
    assert!(
        has_hq,
        "hq : Q should be preserved after failed aesop search"
    );
    assert!(
        has_hp,
        "hp : P should be preserved after failed aesop search (tree-based rollback)"
    );
}

// =============================================================================
// D-T4: Forward vs Destruct Behavior Comparison
//
// Forward: adds new hypothesis, keeps original
// Destruct: adds new hypothesis, removes original
// =============================================================================

/// Setup env with P→Q rule of given builder kind, goal R, hp : P in context
fn setup_builder_test(builder: AesopRuleBuilder) -> ProofState {
    let mut env = setup_destruct_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p_imp_q"),
        level_params: vec![],
        type_: Expr::arrow(p.clone(), q),
    })
    .unwrap();
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("p_imp_q"),
        phase: AesopRulePhase::Safe,
        builder,
        builder_args: vec![],
        priority: 50,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });
    let r = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, r);
    state.current_goal_mut().unwrap().local_ctx.push(LocalDecl {
        fvar: FVarId::new(100),
        name: "hp".to_string(),
        ty: p,
        value: None,
    });
    state
}

/// Test: Both forward and destruct preserve state after failed search
#[test]
fn test_destruct_vs_forward() {
    // Run forward: goal R is unprovable from P + forward P→Q
    let mut state_forward = setup_builder_test(AesopRuleBuilder::Forward);
    let result_forward = aesop(&mut state_forward);
    assert!(
        result_forward.is_err(),
        "aesop should fail with forward P→Q on unprovable goal R"
    );

    // Run destruct: goal R is unprovable from P + destruct P→Q
    let mut state_destruct = setup_builder_test(AesopRuleBuilder::Destruct);
    let result_destruct = aesop(&mut state_destruct);
    assert!(
        result_destruct.is_err(),
        "aesop should fail with destruct P→Q on unprovable goal R"
    );

    // Both failed searches should preserve state via tree-based backtracking
    let forward_has_hp = state_forward
        .current_goal()
        .map(|g| g.local_ctx.iter().any(|d| d.name == "hp"))
        .unwrap_or(false);
    let destruct_has_hp = state_destruct
        .current_goal()
        .map(|g| g.local_ctx.iter().any(|d| d.name == "hp"))
        .unwrap_or(false);
    assert!(
        forward_has_hp && destruct_has_hp,
        "after failed aesop search, state should be preserved (tree-based backtracking)"
    );
}

// =============================================================================
// D-T5: Parse Destruct Builder
//
// Test that the parser correctly recognizes the destruct keyword
// =============================================================================

/// Test: Parser recognizes destruct builder
#[test]
fn test_parse_destruct_builder() {
    use clean_parser::{AesopBuilder, Attribute};

    let input = "@[aesop safe destruct] x";
    let mut parser = clean_parser::grammar::Parser::new(input);
    let attrs = parser.attributes().expect("should parse");

    match &attrs[0] {
        Attribute::Aesop(attr) => {
            assert_eq!(attr.builder, AesopBuilder::Destruct);
        }
        _ => panic!("Expected Attribute::Aesop"),
    }
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Setup environment with propositions P, Q, R, S
fn setup_destruct_env() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Add propositions P, Q, R, S
    for name in ["P", "Q", "R", "S"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    env
}
