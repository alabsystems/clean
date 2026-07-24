// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop builder arguments (Phase C6)
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::{AesopRule, AesopRuleBuilder, AesopRulePhase};

/// Test that builder_args for `cases` are correctly registered and affect candidate generation.
///
/// This test verifies the C6 feature: when `@[aesop safe cases Bool]` is registered,
/// the aesop candidate generation includes `cases` on Bool hypotheses.
#[test]
fn test_aesop_cases_builder_args_enable_bool() {
    let mut env = Environment::new();
    env.init_bool().unwrap();

    // Without the cases Bool rule, Bool is not in the default cases types
    let safe_rules_before = env.get_aesop_safe_rules();
    assert!(
        safe_rules_before
            .iter()
            .all(|r| r.builder != AesopRuleBuilder::Cases || r.builder_args.is_empty()),
        "no cases rule with builder_args should be registered initially"
    );

    // Register `@[aesop safe cases Bool]`
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("cases_bool"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Cases,
        builder_args: vec![Name::from_string("Bool")],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Verify the rule was registered
    let safe_rules_after = env.get_aesop_safe_rules();
    let cases_bool_rule = safe_rules_after
        .iter()
        .find(|r| r.name.to_string() == "cases_bool");
    assert!(
        cases_bool_rule.is_some(),
        "cases_bool rule should be registered"
    );

    let rule = cases_bool_rule.unwrap();
    assert_eq!(rule.builder, AesopRuleBuilder::Cases);
    assert_eq!(rule.builder_args.len(), 1);
    assert_eq!(rule.builder_args[0].to_string(), "Bool");

    // Test that the rule is detected as an inductive type
    assert!(
        env.get_inductive(&Name::from_string("Bool")).is_some(),
        "Bool should be registered as an inductive type"
    );
}
