// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended section variable handling with dependency tracking.

use clean_kernel::Expr;

use crate::section_scope::SectionVariable;
use crate::section_variable_ext::{SectionDiagnosticKind, SectionVariableExt};

// ---------------------------------------------------------------------------
// Scope management
// ---------------------------------------------------------------------------

#[test]
fn test_new_has_no_scopes() {
    let ext = SectionVariableExt::new();
    assert_eq!(ext.depth(), 0);
    assert!(!ext.is_in_section());
    assert!(ext.current_section_name().is_none());
}

#[test]
fn test_enter_section_increases_depth() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Foo");
    assert_eq!(ext.depth(), 1);
    assert!(ext.is_in_section());
    assert_eq!(ext.current_section_name(), Some("Foo"));
}

#[test]
fn test_leave_section_decreases_depth() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Foo");
    let scope = ext.leave_section();
    assert!(scope.is_some());
    assert_eq!(ext.depth(), 0);
    assert!(!ext.is_in_section());
}

#[test]
fn test_leave_empty_returns_none() {
    let mut ext = SectionVariableExt::new();
    assert!(ext.leave_section().is_none());
}

#[test]
fn test_nested_sections_depth() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.enter_section("Inner");
    assert_eq!(ext.depth(), 2);
    assert_eq!(ext.current_section_name(), Some("Inner"));

    let _ = ext.leave_section();
    assert_eq!(ext.depth(), 1);
    assert_eq!(ext.current_section_name(), Some("Outer"));
}

#[test]
fn test_anonymous_section() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("");
    assert_eq!(ext.depth(), 1);
    assert_eq!(ext.current_section_name(), Some(""));
}

// ---------------------------------------------------------------------------
// Variable management
// ---------------------------------------------------------------------------

#[test]
fn test_add_variable_to_innermost_scope() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    assert!(ext.find_variable("n").is_some());
    assert_eq!(ext.all_visible_variables().len(), 1);
}

#[test]
fn test_find_variable_searches_all_scopes() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::implicit(
        "y".to_owned(),
        Expr::const_str("Type"),
    ));

    // Should find variables from both scopes
    assert!(ext.find_variable("x").is_some());
    assert!(ext.find_variable("y").is_some());
    assert!(ext.find_variable("z").is_none());
}

#[test]
fn test_all_visible_variables_outermost_first() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("Bool"),
    ));

    let all = ext.all_visible_variables();
    assert_eq!(all.len(), 2);
    assert_eq!(all[0].name, "a"); // outermost first
    assert_eq!(all[1].name, "b");
}

#[test]
fn test_leave_section_removes_inner_variables() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Bool"),
    ));

    let _ = ext.leave_section();

    assert!(ext.find_variable("x").is_some());
    assert!(ext.find_variable("y").is_none());
}

// ---------------------------------------------------------------------------
// Universe parameters
// ---------------------------------------------------------------------------

#[test]
fn test_add_universe_param() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_universe_param("u");
    ext.add_universe_param("v");

    let univs = ext.all_universe_params();
    assert_eq!(univs, vec!["u".to_owned(), "v".to_owned()]);
}

#[test]
fn test_universe_params_across_scopes() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_universe_param("u");
    ext.enter_section("Inner");
    ext.add_universe_param("v");

    let univs = ext.all_universe_params();
    assert_eq!(univs, vec!["u".to_owned(), "v".to_owned()]);
}

#[test]
fn test_universe_params_deduplicated() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_universe_param("u");
    ext.enter_section("Inner");
    ext.add_universe_param("u"); // duplicate

    let univs = ext.all_universe_params();
    assert_eq!(univs.len(), 1);
    assert_eq!(univs[0], "u");
}

// ---------------------------------------------------------------------------
// Include / omit
// ---------------------------------------------------------------------------

#[test]
fn test_omit_variable() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.omit_variable("n");

    assert!(!ext.is_included("n"));
    let included = ext.all_included_variables();
    assert!(included.is_empty());
}

#[test]
fn test_include_after_omit() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.omit_variable("n");
    ext.include_variable("n");

    assert!(ext.is_included("n"));
    assert_eq!(ext.all_included_variables().len(), 1);
}

#[test]
fn test_omit_unknown_variable_produces_diagnostic() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.omit_variable("nonexistent");

    let diags = ext.take_diagnostics();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, SectionDiagnosticKind::UnknownVariable);
}

#[test]
fn test_include_unknown_variable_produces_diagnostic() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.include_variable("nonexistent");

    let diags = ext.take_diagnostics();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, SectionDiagnosticKind::UnknownVariable);
}

// ---------------------------------------------------------------------------
// Shadowing detection
// ---------------------------------------------------------------------------

#[test]
fn test_shadow_detected() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    assert!(ext.check_shadow("x"));
    let diags = ext.take_diagnostics();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, SectionDiagnosticKind::ShadowWarning);
}

#[test]
fn test_no_shadow_for_unknown_name() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    assert!(!ext.check_shadow("y"));
    assert!(ext.take_diagnostics().is_empty());
}

// ---------------------------------------------------------------------------
// Dependency tracking
// ---------------------------------------------------------------------------

#[test]
fn test_record_and_get_dependencies() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Expression references only "n"
    let expr = Expr::const_str("n");
    ext.record_dependencies("myDef", &expr);

    let dep = ext.get_dependency("myDef").expect("should have dependency");
    assert_eq!(dep.variables, vec!["n".to_owned()]);
    assert!(dep.universes.is_empty());
}

#[test]
fn test_record_dependencies_respects_omit() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.omit_variable("n");

    // Expression references both "n" and "m"
    let expr = Expr::app(Expr::const_str("n"), Expr::const_str("m"));
    ext.record_dependencies("myDef", &expr);

    let dep = ext.get_dependency("myDef").expect("should have dependency");
    // "n" is omitted, so only "m" should appear
    assert_eq!(dep.variables, vec!["m".to_owned()]);
}

#[test]
fn test_record_dependencies_no_match() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    let expr = Expr::const_str("Bool");
    ext.record_dependencies("myDef", &expr);

    let dep = ext.get_dependency("myDef").expect("should have dependency");
    assert!(dep.variables.is_empty());
}

#[test]
fn test_get_dependency_unknown_decl_returns_none() {
    let ext = SectionVariableExt::new();
    assert!(ext.get_dependency("unknown").is_none());
}

// ---------------------------------------------------------------------------
// Section end generalization
// ---------------------------------------------------------------------------

#[test]
fn test_generalize_type_adds_pi_binders() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ));
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Record dependency on both
    let body = Expr::app(Expr::const_str("alpha"), Expr::const_str("n"));
    ext.record_dependencies("foo", &body);

    let generalized = ext.generalize_type("foo", &body);

    // Should be Pi(alpha, Pi(n, body))
    match generalized.kind() {
        clean_kernel::expr::ExprKind::Pi(_, _, inner) => match inner.kind() {
            clean_kernel::expr::ExprKind::Pi(_, _, _) => {}
            other => panic!("expected inner Pi, got {other:?}"),
        },
        other => panic!("expected outer Pi, got {other:?}"),
    }
}

#[test]
fn test_generalize_value_adds_lambda_binders() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    let body = Expr::const_str("n");
    ext.record_dependencies("foo", &body);

    let generalized = ext.generalize_value("foo", &body);

    match generalized.kind() {
        clean_kernel::expr::ExprKind::Lam(_, _, _) => {}
        other => panic!("expected Lam, got {other:?}"),
    }
}

#[test]
fn test_generalize_no_deps_returns_unchanged() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    let body = Expr::const_str("Bool");
    ext.record_dependencies("foo", &body);

    let generalized = ext.generalize_type("foo", &body);
    // No section variables used, should be identical
    assert_eq!(format!("{generalized:?}"), format!("{body:?}"));
}

#[test]
fn test_generalize_unknown_decl_returns_unchanged() {
    let ext = SectionVariableExt::new();
    let body = Expr::const_str("Bool");
    let generalized = ext.generalize_type("unknown", &body);
    assert_eq!(format!("{generalized:?}"), format!("{body:?}"));
}

// ---------------------------------------------------------------------------
// Universe dependency tracking
// ---------------------------------------------------------------------------

#[test]
fn test_used_universes_for() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_universe_param("u");

    // Record a dependency that references "u" as a constant name
    let expr = Expr::const_str("u");
    ext.record_dependencies("myDef", &expr);

    let univs = ext.used_universes_for("myDef");
    assert_eq!(univs, vec!["u".to_owned()]);
}

#[test]
fn test_used_universes_unknown_decl() {
    let ext = SectionVariableExt::new();
    let univs = ext.used_universes_for("unknown");
    assert!(univs.is_empty());
}

// ---------------------------------------------------------------------------
// Duplicate variable / universe diagnostics
// ---------------------------------------------------------------------------

#[test]
fn test_duplicate_variable_diagnostic() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Bool"),
    ));

    let diags = ext.take_diagnostics();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, SectionDiagnosticKind::DuplicateVariable);
}

#[test]
fn test_duplicate_universe_diagnostic() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_universe_param("u");
    ext.enter_section("Inner");
    ext.add_universe_param("u");

    let diags = ext.take_diagnostics();
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, SectionDiagnosticKind::DuplicateUniverse);
}

// ---------------------------------------------------------------------------
// Default trait
// ---------------------------------------------------------------------------

#[test]
fn test_default_impl() {
    let ext = SectionVariableExt::default();
    assert_eq!(ext.depth(), 0);
    assert!(ext.diagnostics().is_empty());
}

// ---------------------------------------------------------------------------
// Complex scenarios
// ---------------------------------------------------------------------------

#[test]
fn test_nested_section_variable_isolation() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::implicit(
        "y".to_owned(),
        Expr::const_str("Type"),
    ));

    // Both visible inside inner section
    assert_eq!(ext.all_visible_variables().len(), 2);

    // Record dependency using both
    let expr = Expr::app(Expr::const_str("x"), Expr::const_str("y"));
    ext.record_dependencies("bar", &expr);

    let dep = ext.get_dependency("bar").expect("should exist");
    assert_eq!(dep.variables.len(), 2);

    // Leave inner — y goes away
    let _ = ext.leave_section();
    assert_eq!(ext.all_visible_variables().len(), 1);
    assert!(ext.find_variable("y").is_none());
}

#[test]
fn test_omit_in_inner_does_not_affect_outer() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    ext.enter_section("Inner");
    ext.omit_variable("x");
    assert!(!ext.is_included("x"));

    // Leave inner — omit should be gone, x included again
    let _ = ext.leave_section();
    assert!(ext.is_included("x"));
}

#[test]
fn test_diagnostics_drain() {
    let mut ext = SectionVariableExt::new();
    ext.enter_section("S");
    ext.omit_variable("nonexistent");
    assert_eq!(ext.diagnostics().len(), 1);

    let drained = ext.take_diagnostics();
    assert_eq!(drained.len(), 1);
    assert!(ext.diagnostics().is_empty());
}
