// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop constructors builder (Phase C7)
//
// Part of #15: Aesop parity for Mathlib compatibility
//
// The constructors builder allows registering an inductive type such that
// when a goal is of that type, aesop automatically tries all constructors.
// For example, `@[aesop safe constructors Bool]` means that when proving
// a goal of type `Bool`, aesop will try both `Bool.true` and `Bool.false`.

use super::*;
use clean_kernel::env::{AesopRule, AesopRuleBuilder, AesopRulePhase};

/// Test that builder_args for `constructors` are correctly registered and affect candidate generation.
///
/// When `@[aesop safe constructors Bool]` is registered and the goal is of type `Bool`,
/// the aesop search should generate candidates for `Bool.true` and `Bool.false`.
#[test]
fn test_aesop_constructors_builder_args_register() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Initially no constructors rule should be registered
    let safe_rules_before = env.get_aesop_safe_rules();
    assert!(
        safe_rules_before
            .iter()
            .all(|r| r.builder != AesopRuleBuilder::Constructors || r.builder_args.is_empty()),
        "no constructors rule with builder_args should be registered initially"
    );

    // Register `@[aesop safe constructors Bool]`
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("constructors_bool"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Constructors,
        builder_args: vec![Name::from_string("Bool")],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Verify the rule was registered
    let safe_rules_after = env.get_aesop_safe_rules();
    let ctor_bool_rule = safe_rules_after
        .iter()
        .find(|r| r.name.to_string() == "constructors_bool");
    assert!(
        ctor_bool_rule.is_some(),
        "constructors_bool rule should be registered"
    );

    let rule = ctor_bool_rule.unwrap();
    assert_eq!(rule.builder, AesopRuleBuilder::Constructors);
    assert_eq!(rule.builder_args.len(), 1);
    assert_eq!(rule.builder_args[0].to_string(), "Bool");
}

/// Test that aesop can prove a Bool goal using the constructors builder.
///
/// When `@[aesop safe constructors Bool]` is registered, aesop should be able
/// to prove a goal of type `Bool` by trying both constructors.
#[test]
fn test_aesop_constructors_prove_bool() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Register constructors rule for Bool
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("constructors_bool"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Constructors,
        builder_args: vec![Name::from_string("Bool")],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: Bool (can be proven by either Bool.true or Bool.false)
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);

    let mut state = ProofState::new(env, bool_ty);

    // Run aesop - should succeed by applying a constructor
    let result = aesop(&mut state);
    assert!(result.is_ok(), "aesop should prove Bool using constructors");
    assert!(state.is_complete(), "goal should be solved after aesop");
}

/// Test that constructor builder registration works for And type.
///
/// `And.intro` is the constructor for And. When `@[aesop safe constructors And]`
/// is registered, the rule should be stored with correct metadata.
///
/// Note: Actually proving `True ∧ True` requires the apply tactic to handle
/// implicit arguments and aesop to solve subgoals with trivial. This is
/// tested in aesop_mathlib.rs for the complete proving scenario.
#[test]
fn test_aesop_constructors_register_and() {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    // Register constructors rule for And
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("constructors_and"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Constructors,
        builder_args: vec![Name::from_string("And")],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Verify And is a valid inductive
    let and_ind = env.get_inductive(&Name::from_string("And"));
    assert!(and_ind.is_some(), "And should be registered as inductive");

    // Verify And has constructor And.intro
    let and_info = and_ind.unwrap();
    assert!(
        and_info
            .constructor_names
            .contains(&Name::from_string("And.intro")),
        "And should have And.intro constructor"
    );

    // Verify constructor rule is registered
    let safe_rules = env.get_aesop_safe_rules();
    let ctor_rule = safe_rules
        .iter()
        .find(|r| r.name.to_string() == "constructors_and");
    assert!(ctor_rule.is_some(), "constructors_and should be registered");

    let rule = ctor_rule.unwrap();
    assert_eq!(rule.builder_args.len(), 1);
    assert_eq!(rule.builder_args[0].to_string(), "And");
}

/// Test that the constructors builder only affects matching target types.
///
/// Registering `@[aesop safe constructors Bool]` is type-targeted: it adds
/// `Bool`'s constructors as candidates only when the goal's head type is
/// `Bool` (see `aesop_get_candidates`, which keys `constructors_type_priorities`
/// on the target type). A goal of a *different* type must not gain any closing
/// path from this rule.
///
/// We use `Empty` (an inductive with **no** constructors) as the foreign type.
/// `Empty` is genuinely uninhabited, so — unlike `Nat` — it has no
/// nullary-constructor path that aesop's generic `trivial`/`constructor`
/// fallback could exploit to close it. That makes the negative assertion a
/// real probe of type filtering: if the Bool constructors rule leaked to
/// non-Bool goals it would be the *only* candidate source here, and it must
/// not close the goal.
///
/// NOTE: `Nat` would be an unsound probe. `Nat`'s first constructor is the
/// nullary `Nat.zero`, and `trivial` (run during aesop normalization) applies
/// the first constructor via the `constructor` tactic. So a bare `⊢ Nat` goal
/// is closed by aesop regardless of any constructors rule — which is correct,
/// type-independent behavior and says nothing about the Bool rule's filtering.
#[test]
fn test_aesop_constructors_type_filtering() {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_empty().unwrap();

    // Register constructors rule for Bool only
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("constructors_bool"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Constructors,
        builder_args: vec![Name::from_string("Bool")],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Bool goal: the registered constructors rule supplies Bool.true / Bool.false
    // as candidates, so aesop closes it.
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let mut bool_state = ProofState::new(env.clone(), bool_ty);

    // This should work
    let result = aesop(&mut bool_state);
    assert!(
        result.is_ok(),
        "Bool goal should be solvable with constructors builder"
    );
    assert!(
        bool_state.is_complete(),
        "Bool constructors should close Bool goal"
    );

    // Empty goal: the Bool constructors rule is type-targeted to `Bool`, so it
    // contributes no candidates here, and `Empty` has no constructor of its own
    // for the generic fallback to apply. Aesop must therefore fail — proving the
    // constructors rule does not leak across target types.
    let empty_ty = Expr::const_(Name::from_string("Empty"), vec![]);
    let mut empty_state = ProofState::new(env, empty_ty);

    let empty_result = aesop(&mut empty_state);
    assert!(
        empty_result.is_err(),
        "aesop should fail on Empty goal with only Bool constructors, got {:?}",
        empty_result
    );
}

/// Test unsafe constructors rules with priority.
#[test]
fn test_aesop_constructors_unsafe_priority() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Register as unsafe with specific priority
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("constructors_bool"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Constructors,
        builder_args: vec![Name::from_string("Bool")],
        priority: 50, // Medium priority
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Verify rule is in unsafe rules
    let unsafe_rules = env.get_aesop_unsafe_rules();
    let rule = unsafe_rules
        .iter()
        .find(|r| r.name.to_string() == "constructors_bool");
    assert!(
        rule.is_some(),
        "constructors_bool should be in unsafe rules"
    );

    let r = rule.unwrap();
    assert_eq!(r.priority, 50);
    assert_eq!(r.phase, AesopRulePhase::Unsafe);

    // Goal: Bool
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let mut state = ProofState::new(env, bool_ty);

    // Should still be able to prove Bool (unsafe rules are still tried)
    let result = aesop(&mut state);
    assert!(
        result.is_ok(),
        "aesop should prove Bool with unsafe constructors rule"
    );
    assert!(
        state.is_complete(),
        "unsafe constructors should close Bool goal"
    );
}
