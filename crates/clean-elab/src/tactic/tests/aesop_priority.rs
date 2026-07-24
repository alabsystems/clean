// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop priority inheritance (D5)
//
// Priority inheritance allows rule sets to override base rule priorities:
// - effective_priority() checks for set-specific overrides
// - Default behavior uses rule's inherent priority
// - Overrides enable contextual priority adjustment
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::{
    AesopIndexMode, AesopRule, AesopRuleBuilder, AesopRulePhase, AesopRuleSet, TransparencyMode,
};

// =============================================================================
// PI-T1: Effective Priority Without Override
//
// Verify that effective_priority returns rule's inherent priority when no
// override is set
// =============================================================================

/// Test: No override returns rule's priority
#[test]
fn test_priority_no_override_uses_default() {
    let rule = AesopRule {
        name: Name::from_string("my_lemma"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::default(),
        transparency: TransparencyMode::default(),
    };

    let rule_set = AesopRuleSet::default();

    // Without override, effective_priority should return rule's priority
    assert_eq!(rule_set.effective_priority(&rule), 50);
}

// =============================================================================
// PI-T2: Effective Priority With Override
//
// Verify that effective_priority returns the override value when set
// =============================================================================

/// Test: Override changes effective priority
#[test]
fn test_priority_override_takes_precedence() {
    let rule = AesopRule {
        name: Name::from_string("my_lemma"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::default(),
        transparency: TransparencyMode::default(),
    };

    let mut rule_set = AesopRuleSet::default();
    rule_set.set_priority_override(Name::from_string("my_lemma"), 80);

    // With override, effective_priority should return override value
    assert_eq!(rule_set.effective_priority(&rule), 80);
}

// =============================================================================
// PI-T3: Set Priority Override Method
//
// Verify set_priority_override works correctly
// =============================================================================

/// Test: Set priority override returns previous value
#[test]
fn test_set_priority_override() {
    let mut rule_set = AesopRuleSet::default();

    // First override returns None
    let prev = rule_set.set_priority_override(Name::from_string("rule1"), 70);
    assert!(
        prev.is_none(),
        "first override for rule1 should return None"
    );

    // Second override returns previous value
    let prev = rule_set.set_priority_override(Name::from_string("rule1"), 90);
    assert_eq!(prev, Some(70));

    // Check it's actually set
    assert!(rule_set.has_priority_override(&Name::from_string("rule1")));
}

// =============================================================================
// PI-T4: Remove Priority Override Method
//
// Verify remove_priority_override works correctly
// =============================================================================

/// Test: Remove priority override
#[test]
fn test_remove_priority_override() {
    let mut rule_set = AesopRuleSet::default();
    rule_set.set_priority_override(Name::from_string("rule1"), 70);

    // Remove returns the old value
    let removed = rule_set.remove_priority_override(&Name::from_string("rule1"));
    assert_eq!(removed, Some(70));

    // No longer has override
    assert!(!rule_set.has_priority_override(&Name::from_string("rule1")));

    // Remove again returns None
    let removed = rule_set.remove_priority_override(&Name::from_string("rule1"));
    assert!(
        removed.is_none(),
        "second remove for rule1 should return None"
    );
}

// =============================================================================
// PI-T5: Multiple Rules Different Overrides
//
// Verify multiple rules can have different overrides in same set
// =============================================================================

/// Test: Multiple rules with different overrides
#[test]
fn test_multiple_rules_different_overrides() {
    let rule1 = AesopRule {
        name: Name::from_string("lemma1"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 30,
        index_mode: AesopIndexMode::default(),
        transparency: TransparencyMode::default(),
    };

    let rule2 = AesopRule {
        name: Name::from_string("lemma2"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 40,
        index_mode: AesopIndexMode::default(),
        transparency: TransparencyMode::default(),
    };

    let rule3 = AesopRule {
        name: Name::from_string("lemma3"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::default(),
        transparency: TransparencyMode::default(),
    };

    let mut rule_set = AesopRuleSet::default();
    rule_set.set_priority_override(Name::from_string("lemma1"), 90);
    rule_set.set_priority_override(Name::from_string("lemma2"), 10);
    // lemma3 has no override

    assert_eq!(rule_set.effective_priority(&rule1), 90); // Override
    assert_eq!(rule_set.effective_priority(&rule2), 10); // Override
    assert_eq!(rule_set.effective_priority(&rule3), 50); // Default
}

// =============================================================================
// PI-T6: Config rule_sets Field
//
// Verify AesopConfig has rule_sets field with correct default
// =============================================================================

/// Test: Config rule_sets defaults to empty
#[test]
fn test_config_rule_sets_default() {
    use super::super::search::AesopConfig;

    let config = AesopConfig::default();
    assert!(config.rule_sets.is_empty());
}

/// Test: Config rule_sets can be set
#[test]
fn test_config_rule_sets_can_be_set() {
    use super::super::search::AesopConfig;

    let config = AesopConfig {
        rule_sets: vec![
            Name::from_string("Measurable"),
            Name::from_string("Continuous"),
        ],
        ..Default::default()
    };

    assert_eq!(config.rule_sets.len(), 2);
    assert_eq!(config.rule_sets[0].to_string(), "Measurable");
    assert_eq!(config.rule_sets[1].to_string(), "Continuous");
}
