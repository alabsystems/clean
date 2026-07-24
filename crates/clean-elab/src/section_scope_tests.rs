// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for section variable scoping with include/omit control.

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_kernel::Expr;

// ---------------------------------------------------------------------------
// SectionVariable construction
// ---------------------------------------------------------------------------

#[test]
fn test_section_variable_explicit() {
    let var = SectionVariable::explicit("n".to_owned(), Expr::const_str("Nat"));
    assert_eq!(var.name, "n");
    assert_eq!(var.binder_info, BinderInfo::Default);
    assert!(!var.is_implicit);
}

#[test]
fn test_section_variable_implicit() {
    let var = SectionVariable::implicit("alpha".to_owned(), Expr::const_str("Type"));
    assert_eq!(var.name, "alpha");
    assert_eq!(var.binder_info, BinderInfo::Implicit);
    assert!(var.is_implicit);
}

#[test]
fn test_section_variable_inst_implicit() {
    let var = SectionVariable::inst_implicit("inst".to_owned(), Expr::const_str("Add"));
    assert_eq!(var.name, "inst");
    assert_eq!(var.binder_info, BinderInfo::InstImplicit);
    assert!(!var.is_implicit);
}

#[test]
fn test_section_variable_strict_implicit() {
    let var = SectionVariable::new(
        "x".to_owned(),
        Expr::const_str("Nat"),
        BinderInfo::StrictImplicit,
    );
    assert_eq!(var.name, "x");
    assert_eq!(var.binder_info, BinderInfo::StrictImplicit);
    assert!(var.is_implicit);
}

// ---------------------------------------------------------------------------
// SectionScope creation and variable management
// ---------------------------------------------------------------------------

#[test]
fn test_section_scope_creation() {
    let scope = SectionScope::new();
    assert_eq!(scope.variable_count(), 0);
    assert!(scope.all_variables().is_empty());
    assert!(scope.universe_params().is_empty());
    assert!(scope.omitted_names().is_empty());
}

#[test]
fn test_add_variable() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    assert_eq!(scope.variable_count(), 1);
    assert_eq!(scope.all_variables()[0].name, "n");
}

#[test]
fn test_add_multiple_variables_preserves_order() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::implicit(
        "b".to_owned(),
        Expr::const_str("Type"),
    ));
    scope.add_variable(SectionVariable::inst_implicit(
        "c".to_owned(),
        Expr::const_str("Add"),
    ));

    assert_eq!(scope.variable_count(), 3);
    assert_eq!(scope.all_variables()[0].name, "a");
    assert_eq!(scope.all_variables()[1].name, "b");
    assert_eq!(scope.all_variables()[2].name, "c");
}

#[test]
fn test_add_universe_param() {
    let mut scope = SectionScope::new();
    scope.add_universe_param("u".to_owned());
    scope.add_universe_param("v".to_owned());
    assert_eq!(scope.universe_params(), &["u".to_owned(), "v".to_owned()]);
}

// ---------------------------------------------------------------------------
// Include/omit control
// ---------------------------------------------------------------------------

#[test]
fn test_variable_included_by_default() {
    let scope = SectionScope::new();
    // Any name is included if not omitted
    assert!(scope.is_included("n"));
    assert!(scope.is_included("anything"));
}

#[test]
fn test_omit_variable() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ));

    scope.omit_variable("n");

    assert!(!scope.is_included("n"));
    assert!(scope.is_included("m"));
    assert!(scope.omitted_names().contains("n"));
}

#[test]
fn test_include_after_omit() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    scope.omit_variable("n");
    assert!(!scope.is_included("n"));

    scope.include_variable("n");
    assert!(scope.is_included("n"));
    assert!(!scope.omitted_names().contains("n"));
}

#[test]
fn test_include_omit_toggling() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Default: included
    assert!(scope.is_included("x"));

    // Omit
    scope.omit_variable("x");
    assert!(!scope.is_included("x"));

    // Re-include
    scope.include_variable("x");
    assert!(scope.is_included("x"));

    // Omit again
    scope.omit_variable("x");
    assert!(!scope.is_included("x"));
}

#[test]
fn test_included_variables_filters_omitted() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "c".to_owned(),
        Expr::const_str("Nat"),
    ));

    scope.omit_variable("b");

    let included = scope.included_variables();
    assert_eq!(included.len(), 2);
    assert_eq!(included[0].name, "a");
    assert_eq!(included[1].name, "c");
}

// ---------------------------------------------------------------------------
// resolve_section_variables
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_used_variables_basic() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Expression that references "n" but not "m"
    let expr = Expr::const_str("n");
    let resolved = resolve_section_variables(&expr, &scope);

    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "n");
}

#[test]
fn test_resolve_no_variables_used() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Expression that doesn't reference any section variable
    let expr = Expr::const_str("Bool");
    let resolved = resolve_section_variables(&expr, &scope);

    assert!(resolved.is_empty());
}

#[test]
fn test_resolve_respects_omit() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ));

    scope.omit_variable("n");

    // Expression that references both "n" and "m"
    let expr = Expr::app(Expr::const_str("n"), Expr::const_str("m"));
    let resolved = resolve_section_variables(&expr, &scope);

    // Only "m" should be resolved since "n" is omitted
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "m");
}

#[test]
fn test_resolve_preserves_declaration_order() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ));
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.add_variable(SectionVariable::inst_implicit(
        "inst".to_owned(),
        Expr::const_str("Add"),
    ));

    // Expression that references all three in different order
    let expr = Expr::app(
        Expr::app(Expr::const_str("inst"), Expr::const_str("n")),
        Expr::const_str("alpha"),
    );
    let resolved = resolve_section_variables(&expr, &scope);

    assert_eq!(resolved.len(), 3);
    assert_eq!(resolved[0].name, "alpha");
    assert_eq!(resolved[1].name, "n");
    assert_eq!(resolved[2].name, "inst");
}

// ---------------------------------------------------------------------------
// abstract_section_variables
// ---------------------------------------------------------------------------

#[test]
fn test_abstract_variables_empty() {
    let expr = Expr::const_str("Nat");
    let result = abstract_section_variables(&expr, &[]);
    // Should return expression unchanged
    assert_eq!(format!("{result:?}"), format!("{expr:?}"));
}

#[test]
fn test_abstract_variables_single_explicit() {
    let var = SectionVariable::explicit("n".to_owned(), Expr::const_str("Nat"));
    let expr = Expr::const_str("Bool");

    let result = abstract_section_variables(&expr, &[&var]);

    // Result should be: (n : Nat) -> Bool  (a Pi with Default binder)
    // Check it is a Pi
    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(_, _, _) => {}
        other => panic!("Expected Pi, got {other:?}"),
    }
}

#[test]
fn test_abstract_variables_multiple() {
    let alpha = SectionVariable::implicit("alpha".to_owned(), Expr::const_str("Type"));
    let n = SectionVariable::explicit("n".to_owned(), Expr::const_str("Nat"));
    let expr = Expr::const_str("Bool");

    let result = abstract_section_variables(&expr, &[&alpha, &n]);

    // Result should be: {alpha : Type} -> (n : Nat) -> Bool
    // Outermost should be Pi (for alpha)
    match result.kind() {
        clean_kernel::expr::ExprKind::Pi(_, _, body) => {
            // Inner should also be Pi (for n)
            match body.kind() {
                clean_kernel::expr::ExprKind::Pi(_, _, _) => {}
                other => panic!("Expected inner Pi, got {other:?}"),
            }
        }
        other => panic!("Expected outer Pi, got {other:?}"),
    }
}

#[test]
fn test_abstract_variables_lam_empty() {
    let expr = Expr::const_str("Nat");
    let result = abstract_section_variables_lam(&expr, &[]);
    assert_eq!(format!("{result:?}"), format!("{expr:?}"));
}

#[test]
fn test_abstract_variables_lam_single() {
    let var = SectionVariable::explicit("n".to_owned(), Expr::const_str("Nat"));
    let expr = Expr::const_str("Bool");

    let result = abstract_section_variables_lam(&expr, &[&var]);

    // Result should be a Lambda, not a Pi
    match result.kind() {
        clean_kernel::expr::ExprKind::Lam(_, _, _) => {}
        other => panic!("Expected Lam, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Nested sections
// ---------------------------------------------------------------------------

#[test]
fn test_nested_sections_independent_scopes() {
    // Simulate nested sections by creating separate scopes
    let mut outer = SectionScope::new();
    outer.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    let mut inner = SectionScope::new();
    inner.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Bool"),
    ));

    // Inner scope only has y
    assert_eq!(inner.variable_count(), 1);
    assert_eq!(inner.all_variables()[0].name, "y");

    // Outer scope only has x
    assert_eq!(outer.variable_count(), 1);
    assert_eq!(outer.all_variables()[0].name, "x");
}

#[test]
fn test_nested_section_omit_isolation() {
    // Omitting in inner scope should not affect outer scope
    let mut outer = SectionScope::new();
    outer.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));

    let mut inner = SectionScope::new();
    inner.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ));
    inner.omit_variable("x");

    // Inner has omitted x
    assert!(!inner.is_included("x"));
    // Outer still has x included
    assert!(outer.is_included("x"));
}

// ---------------------------------------------------------------------------
// Universe parameters
// ---------------------------------------------------------------------------

#[test]
fn test_universe_params_accumulate() {
    let mut scope = SectionScope::new();
    assert!(scope.universe_params().is_empty());

    scope.add_universe_param("u".to_owned());
    assert_eq!(scope.universe_params().len(), 1);

    scope.add_universe_param("v".to_owned());
    assert_eq!(scope.universe_params().len(), 2);
    assert_eq!(scope.universe_params()[0], "u");
    assert_eq!(scope.universe_params()[1], "v");
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_omit_nonexistent_variable() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    // Omitting a variable that doesn't exist should not panic
    scope.omit_variable("nonexistent");
    assert!(!scope.is_included("nonexistent"));
    // Existing variable is unaffected
    assert!(scope.is_included("n"));
}

#[test]
fn test_include_nonexistent_variable() {
    let mut scope = SectionScope::new();
    // Including a variable that was never omitted should not panic
    scope.include_variable("nonexistent");
    assert!(scope.is_included("nonexistent"));
}

#[test]
fn test_default_impl() {
    let scope = SectionScope::default();
    assert_eq!(scope.variable_count(), 0);
    assert!(scope.universe_params().is_empty());
}

#[test]
fn test_clone_independence() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));

    let mut cloned = scope.clone();
    cloned.omit_variable("n");

    // Original should be unaffected
    assert!(scope.is_included("n"));
    assert!(!cloned.is_included("n"));
}

#[test]
fn test_resolve_with_empty_scope() {
    let scope = SectionScope::new();
    let expr = Expr::const_str("Nat");
    let resolved = resolve_section_variables(&expr, &scope);
    assert!(resolved.is_empty());
}

#[test]
fn test_resolve_with_all_omitted() {
    let mut scope = SectionScope::new();
    scope.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    scope.omit_variable("n");

    let expr = Expr::const_str("n");
    let resolved = resolve_section_variables(&expr, &scope);
    assert!(resolved.is_empty());
}
