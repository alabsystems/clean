// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 1d: Proptest equivalents of Kani timeout harnesses for inductive
//! positivity checking (#982).
//!
//! Migrated from designs/2026-03-04-982-proptest-alternative.md
//!
//! Kani harnesses verify_negative_occurrence_detected, verify_positive_occurrence_accepted,
//! verify_strictly_positive_nested, verify_nested_negative_detected, and
//! verify_app_inductive_args_checked all timeout on recursive ADTs.
//! These proptests exercise real production check_positivity with varying names.

use clean_kernel::expr::Expr;
use clean_kernel::inductive::check_positivity;
use clean_kernel::name::Name;
use clean_kernel::InductiveError;
use proptest::prelude::*;

/// Strategy for generating inductive type names with varying depth.
fn ind_name_strategy() -> impl Strategy<Value = Name> {
    prop::collection::vec("[A-Z][a-z]{1,4}", 1..4).prop_map(|segments| {
        segments
            .iter()
            .fold(Name::anon(), |parent, seg| parent.str(seg))
    })
}

/// Helper: single-name positivity check for non-mutual tests.
fn check_pos(name: &Name, expr: &Expr, param_count: u32) -> Result<(), InductiveError> {
    check_positivity(name, expr, param_count, &[name])
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    // ================================================================
    // Positive occurrence accepted (Kani equivalent: verify_positive_occurrence_accepted)
    //
    // Constructor type: Nat → IndName
    // IndName appears only in return position — always valid.
    // ================================================================

    #[test]
    fn prop_positive_occurrence_accepted(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let ctor_type = Expr::arrow(nat, ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_ok(),
            "Positive occurrence (return position only) should be accepted: {:?}", name);
    }

    // ================================================================
    // Negative occurrence detected (Kani equivalent: verify_negative_occurrence_detected)
    //
    // Constructor type: (IndName → Prop) → IndName
    // IndName appears left of arrow in a constructor argument — non-positive.
    // ================================================================

    #[test]
    fn prop_negative_occurrence_detected(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        let domain = Expr::arrow(ind_ref.clone(), Expr::prop());
        let ctor_type = Expr::arrow(domain, ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_err(),
            "Negative occurrence should be rejected: {:?}", name);
        if let Err(e) = result {
            prop_assert!(matches!(e, InductiveError::NonPositive(_, _)),
                "Error should be NonPositive variant, got: {:?}", e);
        }
    }

    // ================================================================
    // Strictly positive nested (Kani equivalent: verify_strictly_positive_nested)
    //
    // Constructor type: (Nat → IndName) → IndName
    // IndName appears in positive position within a constructor argument.
    // This is strictly positive because IndName is not left of any arrow.
    // ================================================================

    #[test]
    fn prop_strictly_positive_nested(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        // Nat → IndName: IndName in positive position
        let pos_arg = Expr::arrow(nat, ind_ref.clone());
        // (Nat → IndName) → IndName
        let ctor_type = Expr::arrow(pos_arg, ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_ok(),
            "Strictly positive nested occurrence should be accepted: {:?}", name);
    }

    // ================================================================
    // Nested negative detected (Kani equivalent: verify_nested_negative_detected)
    //
    // Constructor type: ((IndName → Prop) → Prop) → IndName
    // IndName appears left of arrow even though it's nested deeper.
    // The check recurses into Pi domains.
    // ================================================================

    #[test]
    fn prop_nested_negative_detected(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        // IndName → Prop (negative occurrence of IndName)
        let inner = Expr::arrow(ind_ref.clone(), Expr::prop());
        // (IndName → Prop) → Prop
        let middle = Expr::arrow(inner, Expr::prop());
        // ((IndName → Prop) → Prop) → IndName
        let ctor_type = Expr::arrow(middle, ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_err(),
            "Nested negative occurrence should be rejected: {:?}", name);
    }

    // ================================================================
    // App inductive args checked (Kani equivalent: verify_app_inductive_args_checked)
    //
    // Constructor type: IndName(IndName → Prop) → IndName
    // When IndName is applied to args, those args must not mention any
    // mutual inductive type (check_no_negative_occurrence).
    // ================================================================

    #[test]
    fn prop_inductive_app_args_checked(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        // IndName → Prop (mentions IndName)
        let bad_arg = Expr::arrow(ind_ref.clone(), Expr::prop());
        // IndName(IndName → Prop) — applied to arg mentioning itself
        let app = Expr::app(ind_ref.clone(), bad_arg);
        // IndName(IndName → Prop) → IndName
        let ctor_type = Expr::arrow(app, ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_err(),
            "Inductive applied to self-referencing arg should be rejected: {:?}", name);
    }

    // ================================================================
    // Additional: direct self-reference is positive
    //
    // Constructor type: IndName → IndName (like List.cons : A → List A → List A)
    // Direct occurrence in domain is positive (it's a Const, not under a Pi domain).
    // ================================================================

    #[test]
    fn prop_direct_self_reference_positive(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        // IndName → IndName (like cons : A → List A → List A)
        let ctor_type = Expr::arrow(ind_ref.clone(), ind_ref);
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_ok(),
            "Direct self-reference (not under arrow in domain) should be positive: {:?}", name);
    }

    // ================================================================
    // Additional: multiple Pi domains, negative in one
    //
    // Constructor type: Nat → (IndName → Prop) → IndName
    // ================================================================

    #[test]
    fn prop_negative_in_later_arg(name in ind_name_strategy()) {
        let ind_ref = Expr::const_(name.clone(), vec![]);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let neg_domain = Expr::arrow(ind_ref.clone(), Expr::prop());
        // Nat → (IndName → Prop) → IndName
        let ctor_type = Expr::arrow(nat, Expr::arrow(neg_domain, ind_ref));
        let result = check_pos(&name, &ctor_type, 0);
        prop_assert!(result.is_err(),
            "Negative in later arg should still be rejected: {:?}", name);
    }
}
