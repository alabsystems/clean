// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended coercion elaboration module.

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use crate::coercion::{CoercionEntry, CoercionKind, CoercionRegistry};
use crate::coercion_ext::{CoercionExtConfig, CoercionExtSearch, CoercionTrace, SortCoercion};

fn mk_direct(fn_name: &str, source: &str, target: &str) -> CoercionEntry {
    CoercionEntry {
        fn_name: Name::from_string(fn_name),
        source: Name::from_string(source),
        target: Name::from_string(target),
        kind: CoercionKind::Direct,
    }
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

// ============================================================================
// Configuration
// ============================================================================

#[test]
fn test_config_default_values() {
    let cfg = CoercionExtConfig::default();
    assert_eq!(cfg.max_depth, 8);
    assert!(cfg.sort_coercions);
    assert!(cfg.function_coercions);
    assert!(cfg.numeric_coercions);
    assert!(cfg.detect_ambiguity);
    assert!(!cfg.trace_enabled);
}

#[test]
fn test_config_custom_depth() {
    let cfg = CoercionExtConfig {
        max_depth: 3,
        ..Default::default()
    };
    assert_eq!(cfg.max_depth, 3);
}

// ============================================================================
// Chain composition (2-step and 3-step)
// ============================================================================

#[test]
fn test_chain_two_step_via_search() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bc", "B", "C")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let (path, _trace) = search.search(&reg, &name("A"), &name("C"));
    let path = path.expect("should find 2-step path");
    assert_eq!(path.len(), 2);
    assert_eq!(path.steps[0].fn_name, name("f_ab"));
    assert_eq!(path.steps[1].fn_name, name("f_bc"));
}

#[test]
fn test_chain_three_step_via_search() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bc", "B", "C")).unwrap();
    reg.register(mk_direct("f_cd", "C", "D")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let (path, _trace) = search.search(&reg, &name("A"), &name("D"));
    let path = path.expect("should find 3-step path");
    assert_eq!(path.len(), 3);
    assert_eq!(path.steps[0].fn_name, name("f_ab"));
    assert_eq!(path.steps[1].fn_name, name("f_bc"));
    assert_eq!(path.steps[2].fn_name, name("f_cd"));
}

// ============================================================================
// Depth limit enforcement
// ============================================================================

#[test]
fn test_depth_limit_enforced() {
    let mut reg = CoercionRegistry::new();
    // Build chain of length 4: T0->T1->T2->T3->T4
    for i in 0..4 {
        let src = format!("T{i}");
        let tgt = format!("T{}", i + 1);
        let fn_name = format!("coe_{i}_{}", i + 1);
        reg.register(mk_direct(&fn_name, &src, &tgt)).unwrap();
    }

    // With depth limit 3, should not find T0->T4 (needs 4 steps).
    let config = CoercionExtConfig {
        max_depth: 3,
        detect_ambiguity: true,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let (path, _) = search.search(&reg, &name("T0"), &name("T4"));
    assert!(path.is_none(), "chain of 4 should exceed depth limit of 3");
}

#[test]
fn test_depth_limit_allows_shorter() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bc", "B", "C")).unwrap();

    let config = CoercionExtConfig {
        max_depth: 3,
        detect_ambiguity: true,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let (path, _) = search.search(&reg, &name("A"), &name("C"));
    assert!(path.is_some(), "chain of 2 should be within depth limit 3");
}

// ============================================================================
// Sort coercions
// ============================================================================

#[test]
fn test_sort_coercion_prop_to_type() {
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_sort_coercion(&name("Prop"), &name("Type"));
    assert!(result.is_some());
    let (kind, fn_name) = result.unwrap();
    assert_eq!(kind, SortCoercion::PropToType);
    assert_eq!(fn_name, name("propToType"));
}

#[test]
fn test_sort_coercion_type_to_sort() {
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_sort_coercion(&name("Type"), &name("Sort"));
    assert!(result.is_some());
    let (kind, fn_name) = result.unwrap();
    assert_eq!(kind, SortCoercion::TypeToSort);
    assert_eq!(fn_name, name("typeToSort"));
}

#[test]
fn test_sort_coercion_disabled() {
    let config = CoercionExtConfig {
        sort_coercions: false,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let result = search.find_sort_coercion(&name("Prop"), &name("Type"));
    assert!(result.is_none(), "sort coercion should be disabled");
}

#[test]
fn test_sort_coercion_no_match() {
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_sort_coercion(&name("Nat"), &name("Int"));
    assert!(result.is_none(), "Nat->Int is not a sort coercion");
}

#[test]
fn test_sort_coercion_via_search() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("Prop"), &name("Type"));
    let path = path.expect("should find Prop->Type sort coercion");
    assert_eq!(path.len(), 1);
    assert_eq!(path.steps[0].fn_name, name("propToType"));
}

// ============================================================================
// Function coercions
// ============================================================================

#[test]
fn test_function_coercion_registered() {
    let mut search = CoercionExtSearch::with_defaults();
    search.register_coe_fun(name("Equiv"));
    assert!(search.has_coe_fun(&name("Equiv")));
    assert!(!search.has_coe_fun(&name("Nat")));
}

#[test]
fn test_function_coercion_apply() {
    let mut search = CoercionExtSearch::with_defaults();
    search.register_coe_fun(name("Equiv"));
    let expr = Expr::const_str("my_equiv");
    let result = search.try_function_coercion(&name("Equiv"), expr);
    assert!(result.is_some(), "should apply coeFun");
    let coerced = result.unwrap();
    assert!(coerced.is_app());
}

#[test]
fn test_function_coercion_not_registered() {
    let search = CoercionExtSearch::with_defaults();
    let expr = Expr::const_str("x");
    let result = search.try_function_coercion(&name("Nat"), expr);
    assert!(result.is_none(), "Nat has no coeFun");
}

#[test]
fn test_function_coercion_disabled() {
    let config = CoercionExtConfig {
        function_coercions: false,
        ..Default::default()
    };
    let mut search = CoercionExtSearch::new(config);
    search.register_coe_fun(name("Equiv"));
    let expr = Expr::const_str("e");
    let result = search.try_function_coercion(&name("Equiv"), expr);
    assert!(result.is_none(), "function coercions disabled");
}

// ============================================================================
// Numeric literal coercions
// ============================================================================

#[test]
fn test_nat_literal_coercion_to_int() {
    let search = CoercionExtSearch::with_defaults();
    let entry = search
        .find_nat_literal_coercion(&name("Int"))
        .expect("Nat->Int via OfNat should exist");
    assert_eq!(entry.fn_name, name("Int.ofNat"));
    assert_eq!(entry.source, name("Nat"));
    assert_eq!(entry.target, name("Int"));
}

#[test]
fn test_nat_literal_coercion_to_float() {
    let search = CoercionExtSearch::with_defaults();
    let entry = search
        .find_nat_literal_coercion(&name("Float"))
        .expect("Nat->Float via OfNat should exist");
    assert_eq!(entry.fn_name, name("Float.ofNat"));
}

#[test]
fn test_nat_literal_coercion_to_rat() {
    let search = CoercionExtSearch::with_defaults();
    let entry = search
        .find_nat_literal_coercion(&name("Rat"))
        .expect("Nat->Rat via OfNat should exist");
    assert_eq!(entry.fn_name, name("Rat.ofNat"));
}

#[test]
fn test_nat_literal_coercion_unknown_target() {
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_nat_literal_coercion(&name("String"));
    assert!(result.is_none(), "no OfNat for String");
}

#[test]
fn test_scientific_literal_coercion_to_float() {
    let search = CoercionExtSearch::with_defaults();
    let entry = search
        .find_scientific_literal_coercion(&name("Float"))
        .expect("Float.ofScientific should exist");
    assert_eq!(entry.fn_name, name("Float.ofScientific"));
}

#[test]
fn test_scientific_literal_coercion_unknown_target() {
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_scientific_literal_coercion(&name("Nat"));
    assert!(result.is_none(), "no OfScientific for Nat");
}

#[test]
fn test_numeric_coercions_disabled() {
    let config = CoercionExtConfig {
        numeric_coercions: false,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    assert!(search.find_nat_literal_coercion(&name("Int")).is_none());
    assert!(search
        .find_scientific_literal_coercion(&name("Float"))
        .is_none());
}

#[test]
fn test_register_custom_of_nat_target() {
    let mut search = CoercionExtSearch::with_defaults();
    assert!(!search.has_of_nat(&name("MyNum")));
    search.register_of_nat_target(name("MyNum"));
    assert!(search.has_of_nat(&name("MyNum")));
    let entry = search
        .find_nat_literal_coercion(&name("MyNum"))
        .expect("should find custom OfNat");
    assert_eq!(entry.fn_name, name("MyNum.ofNat"));
}

// ============================================================================
// User-defined coercion registration (via CoercionRegistry)
// ============================================================================

#[test]
fn test_user_defined_coercion_registration() {
    let mut reg = CoercionRegistry::new();
    let entry = CoercionEntry {
        fn_name: name("Subtype.val"),
        source: name("Subtype"),
        target: name("Nat"),
        kind: CoercionKind::Direct,
    };
    reg.register(entry).expect("user coercion should register");
    assert!(reg.is_coercion(&name("Subtype.val")));
    let found = reg
        .find_direct(&name("Subtype"), &name("Nat"))
        .expect("should be found");
    assert_eq!(found.fn_name, name("Subtype.val"));
}

#[test]
fn test_user_defined_coercion_in_chain() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("Subtype.val", "Subtype", "Nat"))
        .unwrap();
    reg.register(mk_direct("Int.ofNat", "Nat", "Int")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("Subtype"), &name("Int"));
    let path = path.expect("should find Subtype->Nat->Int chain");
    assert_eq!(path.len(), 2);
}

// ============================================================================
// Ambiguity detection
// ============================================================================

#[test]
fn test_ambiguity_no_paths() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let result = search.find_all_paths(&reg, &name("A"), &name("B"));
    assert!(!result.is_ambiguous);
    assert!(result.paths.is_empty());
}

#[test]
fn test_ambiguity_single_path() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let result = search.find_all_paths(&reg, &name("A"), &name("B"));
    assert!(!result.is_ambiguous);
    assert_eq!(result.paths.len(), 1);
}

#[test]
fn test_ambiguity_diamond_two_paths() {
    let mut reg = CoercionRegistry::new();
    // Path 1: A -> B -> D
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bd", "B", "D")).unwrap();
    // Path 2: A -> C -> D
    reg.register(mk_direct("f_ac", "A", "C")).unwrap();
    reg.register(mk_direct("f_cd", "C", "D")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let result = search.find_all_paths(&reg, &name("A"), &name("D"));
    assert!(result.is_ambiguous, "diamond should be ambiguous");
    assert_eq!(result.paths.len(), 2);
}

#[test]
fn test_ambiguity_diamond_direct_plus_chain() {
    let mut reg = CoercionRegistry::new();
    // Direct path: A -> C
    reg.register(mk_direct("f_ac", "A", "C")).unwrap();
    // Chain path: A -> B -> C
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bc", "B", "C")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let result = search.find_all_paths(&reg, &name("A"), &name("C"));
    assert!(result.is_ambiguous, "direct+chain should be ambiguous");
    assert_eq!(result.paths.len(), 2);
}

// ============================================================================
// Trace generation
// ============================================================================

#[test]
fn test_trace_empty_by_default() {
    let trace = CoercionTrace::new();
    assert!(trace.is_empty());
    assert_eq!(trace.len(), 0);
}

#[test]
fn test_trace_generated_when_enabled() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).unwrap();

    let config = CoercionExtConfig {
        trace_enabled: true,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let (path, trace) = search.search(&reg, &name("A"), &name("B"));
    assert!(path.is_some());
    assert!(!trace.is_empty(), "trace should have entries when enabled");
    assert!(trace.entries.iter().any(|e| e.success));
}

#[test]
fn test_trace_not_generated_when_disabled() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).unwrap();

    let config = CoercionExtConfig {
        trace_enabled: false,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let (path, trace) = search.search(&reg, &name("A"), &name("B"));
    assert!(path.is_some());
    assert!(trace.is_empty(), "trace should be empty when disabled");
}

#[test]
fn test_trace_records_failure() {
    let reg = CoercionRegistry::new();
    let config = CoercionExtConfig {
        trace_enabled: true,
        sort_coercions: false,
        numeric_coercions: false,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let (path, trace) = search.search(&reg, &name("X"), &name("Y"));
    assert!(path.is_none());
    assert!(!trace.is_empty());
    assert!(
        trace.entries.iter().all(|e| !e.success),
        "all trace entries should be failures"
    );
}

// ============================================================================
// Diamond resolution (prefer shorter chains)
// ============================================================================

#[test]
fn test_diamond_resolution_prefers_shorter() {
    let mut reg = CoercionRegistry::new();
    // Short path: A -> D (1 step)
    reg.register(mk_direct("f_ad", "A", "D")).unwrap();
    // Long path: A -> B -> C -> D (3 steps)
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bc", "B", "C")).unwrap();
    reg.register(mk_direct("f_cd", "C", "D")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let path = search
        .resolve_diamond(&reg, &name("A"), &name("D"))
        .expect("should resolve diamond");
    assert_eq!(path.len(), 1, "should prefer shorter path");
    assert_eq!(path.steps[0].fn_name, name("f_ad"));
}

#[test]
fn test_diamond_resolution_two_equal_length() {
    let mut reg = CoercionRegistry::new();
    // Path 1: A -> B -> D (2 steps)
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_bd", "B", "D")).unwrap();
    // Path 2: A -> C -> D (2 steps)
    reg.register(mk_direct("f_ac", "A", "C")).unwrap();
    reg.register(mk_direct("f_cd", "C", "D")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let path = search
        .resolve_diamond(&reg, &name("A"), &name("D"))
        .expect("should resolve diamond");
    // Both paths are length 2; either is acceptable.
    assert_eq!(path.len(), 2);
}

#[test]
fn test_diamond_resolution_no_path() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let result = search.resolve_diamond(&reg, &name("X"), &name("Y"));
    assert!(result.is_none());
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_self_coercion_not_found() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("Nat"), &name("Nat"));
    // No self-coercion registered in default config.
    assert!(path.is_none());
}

#[test]
fn test_empty_registry_search() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("A"), &name("B"));
    assert!(path.is_none());
}

#[test]
fn test_cycle_detection_in_search() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B")).unwrap();
    reg.register(mk_direct("f_ba", "B", "A")).unwrap();
    // No path from A to C despite cycle A<->B.
    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("A"), &name("C"));
    assert!(path.is_none());
}

// ============================================================================
// Extended try_coerce_ext integration
// ============================================================================

#[test]
fn test_try_coerce_ext_direct() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("Int.ofNat", "Nat", "Int")).unwrap();

    let search = CoercionExtSearch::with_defaults();
    let expr = Expr::const_str("n");
    let actual = Expr::const_str("Nat");
    let expected = Expr::const_str("Int");
    let (coerced, _trace) = search
        .try_coerce_ext(&reg, expr, &actual, &expected)
        .expect("should coerce");
    assert!(coerced.is_app());
}

#[test]
fn test_try_coerce_ext_sort_coercion() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let expr = Expr::const_str("p");
    let actual = Expr::const_str("Prop");
    let expected = Expr::const_str("Type");
    let (coerced, _trace) = search
        .try_coerce_ext(&reg, expr, &actual, &expected)
        .expect("should use sort coercion");
    assert!(coerced.is_app());
}

#[test]
fn test_try_coerce_ext_no_coercion() {
    let reg = CoercionRegistry::new();
    let config = CoercionExtConfig {
        sort_coercions: false,
        numeric_coercions: false,
        ..Default::default()
    };
    let search = CoercionExtSearch::new(config);
    let expr = Expr::const_str("x");
    let actual = Expr::const_str("String");
    let expected = Expr::const_str("Nat");
    let result = search.try_coerce_ext(&reg, expr, &actual, &expected);
    assert!(result.is_err());
}

#[test]
fn test_try_coerce_ext_non_const_head_error() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let expr = Expr::const_str("x");
    let actual = Expr::bvar(0); // not a const head
    let expected = Expr::const_str("Nat");
    let result = search.try_coerce_ext(&reg, expr, &actual, &expected);
    assert!(result.is_err());
}

#[test]
fn test_search_prefers_registry_over_sort() {
    // If a direct coercion exists in the registry from Prop to Type,
    // it should be found before the sort coercion fallback.
    let mut reg = CoercionRegistry::new();
    reg.register(CoercionEntry {
        fn_name: name("myPropToType"),
        source: name("Prop"),
        target: name("Type"),
        kind: CoercionKind::Direct,
    })
    .unwrap();

    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("Prop"), &name("Type"));
    let path = path.expect("should find coercion");
    assert_eq!(path.steps[0].fn_name, name("myPropToType"));
}

#[test]
fn test_nat_numeric_coercion_via_search() {
    let reg = CoercionRegistry::new();
    let search = CoercionExtSearch::with_defaults();
    let (path, _) = search.search(&reg, &name("Nat"), &name("Int"));
    let path = path.expect("should find Nat->Int via numeric coercion");
    assert_eq!(path.len(), 1);
    assert_eq!(path.steps[0].fn_name, name("Int.ofNat"));
}

#[test]
fn test_register_of_scientific_target() {
    let mut search = CoercionExtSearch::with_defaults();
    assert!(!search.has_of_scientific(&name("MyReal")));
    search.register_of_scientific_target(name("MyReal"));
    assert!(search.has_of_scientific(&name("MyReal")));
}
