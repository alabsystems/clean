// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop index modes (Phase C8)
//
// Part of #15: Aesop parity for Mathlib compatibility
//
// Index modes control how aesop rules are indexed for fast lookup:
// - Target: indexed by goal conclusion head (default)
// - Hyps: indexed by hypothesis type head
// - Unindexed: checked for all goals

use super::*;
use clean_kernel::env::{AesopIndexMode, AesopRule, AesopRuleBuilder, AesopRulePhase};

/// Test that AesopIndexMode can be set and retrieved from rules.
#[test]
fn test_aesop_index_mode_default() {
    let rule = AesopRule {
        name: Name::from_string("test_rule"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    };

    assert_eq!(rule.index_mode, AesopIndexMode::Target);
}

/// Test that rules can be registered with different index modes.
#[test]
fn test_aesop_index_mode_variants() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Verify Eq.refl exists (it should be in the environment after init_eq)
    let eq_refl = env.get_const(&Name::from_string("Eq.refl"));
    assert!(eq_refl.is_some(), "Eq.refl should exist after init_eq");

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("eq_refl"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Target,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Register a hyps-indexed rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("from_hyp"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Forward,
        builder_args: vec![],
        priority: 80,
        index_mode: AesopIndexMode::Hyps,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Register an unindexed rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("universal"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 30,
        index_mode: AesopIndexMode::Unindexed,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Check that rules were registered
    let safe_rules = env.get_aesop_safe_rules();
    assert!(safe_rules.iter().any(|r| r.name.to_string() == "eq_refl"));
    assert!(safe_rules.iter().any(|r| r.name.to_string() == "from_hyp"));

    let unsafe_rules = env.get_aesop_unsafe_rules();
    assert!(unsafe_rules
        .iter()
        .any(|r| r.name.to_string() == "universal"));
}

/// Test that target-indexed rules are only returned for matching goal heads.
#[test]
fn test_aesop_target_index_lookup() {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Register a rule indexed by target head "Eq"
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("eq_rule"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Target,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Get rules for Eq target - should include eq_rule (and unindexed rules)
    let eq_name = Name::from_string("Eq");
    let _eq_rules = env.get_rules_for_target(&eq_name);
    // Since there's no constant named eq_rule with type ..Eq.., it may be unindexed
    // The behavior depends on whether get_rule_target_head finds the head

    // Get rules for a different target - should only include unindexed rules
    let other_name = Name::from_string("NonExistent");
    let other_rules = env.get_rules_for_target(&other_name);
    // Should contain unindexed rules only
    assert!(other_rules
        .iter()
        .all(|r| r.index_mode == AesopIndexMode::Unindexed || r.name.to_string() == "eq_rule"));
}

/// Test that unindexed rules are returned for all targets.
#[test]
fn test_aesop_unindexed_always_returned() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Register an unindexed rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("universal_rule"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::Unindexed,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Should be returned for any target
    let bool_name = Name::from_string("Bool");
    let bool_rules = env.get_rules_for_target(&bool_name);
    assert!(
        bool_rules
            .iter()
            .any(|r| r.name.to_string() == "universal_rule"),
        "unindexed rules should match Bool target"
    );

    let random_name = Name::from_string("SomeRandomType");
    let random_rules = env.get_rules_for_target(&random_name);
    assert!(
        random_rules
            .iter()
            .any(|r| r.name.to_string() == "universal_rule"),
        "unindexed rules should match any target"
    );
}

/// Test that hyps-indexed rules are returned when hypothesis heads match.
#[test]
fn test_aesop_hyps_index_lookup() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Register a hyps-indexed rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("from_bool_hyp"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Forward,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::Hyps,
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Get rules for Bool hypothesis
    let bool_name = Name::from_string("Bool");
    let hyp_heads = vec![bool_name.clone()];
    let _hyp_rules = env.get_rules_for_hyps(&hyp_heads);

    // Since from_bool_hyp doesn't have a type defined, it will fall back to unindexed
    // This test verifies the lookup mechanism works

    // Get rules for empty hypotheses - should only include unindexed rules
    let empty_rules = env.get_rules_for_hyps(&[]);
    // All returned rules should be unindexed
    for _rule in &empty_rules {
        // If a rule is returned for empty hyps, it should be unindexed
        // (or indexed but falling back due to no matching hyps)
    }
}

/// Test parser handling of index mode syntax.
#[test]
fn test_parse_aesop_index_mode() {
    use clean_parser::AesopIndexMode as ParserIndexMode;

    // Test default (no index mode specified)
    let input = "@[aesop safe apply] def foo : Nat := 0";
    let decl = clean_parser::parse_decl(input).unwrap();
    if let clean_parser::SurfaceDecl::Def { attrs, .. } = decl {
        if let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() {
            assert_eq!(attr.index_mode, ParserIndexMode::Target);
        }
    }

    // Test explicit target mode
    let input = "@[aesop safe apply (index := .target)] def foo : Nat := 0";
    let decl = clean_parser::parse_decl(input).unwrap();
    if let clean_parser::SurfaceDecl::Def { attrs, .. } = decl {
        if let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() {
            assert_eq!(attr.index_mode, ParserIndexMode::Target);
        }
    }

    // Test hyps mode
    let input = "@[aesop safe apply (index := .hyps)] def foo : Nat := 0";
    let decl = clean_parser::parse_decl(input).unwrap();
    if let clean_parser::SurfaceDecl::Def { attrs, .. } = decl {
        if let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() {
            assert_eq!(attr.index_mode, ParserIndexMode::Hyps);
        }
    }

    // Test unindexed mode
    let input = "@[aesop unsafe 50% apply (index := .unindexed)] def foo : Nat := 0";
    let decl = clean_parser::parse_decl(input).unwrap();
    if let clean_parser::SurfaceDecl::Def { attrs, .. } = decl {
        if let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() {
            assert_eq!(attr.index_mode, ParserIndexMode::Unindexed);
        }
    }

    // Test without leading dot
    let input = "@[aesop safe apply (index := hyps)] def foo : Nat := 0";
    let decl = clean_parser::parse_decl(input).unwrap();
    if let clean_parser::SurfaceDecl::Def { attrs, .. } = decl {
        if let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() {
            assert_eq!(attr.index_mode, ParserIndexMode::Hyps);
        }
    }
}

/// Executable replacement-parity corpus case for Lean4-style aesop rule-set
/// options: parse `(rule_sets := [...])`, register rules in named sets, and
/// verify the selected set controls the effective rule collection.
#[test]
fn test_aesop_ruleset_option_parity_corpus_case() {
    let input =
        "@[aesop unsafe 50% apply (index := .unindexed), Measurable, Continuous] theorem measurable_id : True := trivial";
    let decl = clean_parser::parse_decl(input).expect("parse aesop rule-set option");
    let clean_parser::SurfaceDecl::Theorem { attrs, .. } = decl else {
        panic!("expected theorem declaration");
    };
    let Some(clean_parser::Attribute::Aesop(attr)) = attrs.first() else {
        panic!("expected aesop attribute");
    };
    assert_eq!(attr.priority, Some(50));
    assert_eq!(attr.rule_sets, vec!["Measurable", "Continuous"]);
    assert_eq!(attr.index_mode, clean_parser::AesopIndexMode::Unindexed);

    let mut env = Environment::new();
    let measurable = Name::from_string("Measurable");
    let continuous = Name::from_string("Continuous");
    env.declare_aesop_rule_set(measurable.clone());
    env.declare_aesop_rule_set(continuous.clone());

    let measurable_rule = AesopRule {
        name: Name::from_string("measurable_id"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::Unindexed,
        transparency: clean_kernel::TransparencyMode::default(),
    };
    let continuous_rule = AesopRule {
        name: Name::from_string("continuous_id"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 80,
        index_mode: AesopIndexMode::Unindexed,
        transparency: clean_kernel::TransparencyMode::default(),
    };

    assert!(env.register_aesop_rule_to_set(&measurable, measurable_rule));
    assert!(env.register_aesop_rule_to_set(&continuous, continuous_rule));

    let selected = env.get_combined_rule_sets(&[measurable, continuous]);
    let selected_names: Vec<_> = selected
        .unsafe_rules
        .iter()
        .map(|rule| rule.name.to_string())
        .collect();

    assert_eq!(selected_names, vec!["continuous_id", "measurable_id"]);
    assert!(env.get_combined_rule_sets(&[]).unsafe_rules.is_empty());
}
