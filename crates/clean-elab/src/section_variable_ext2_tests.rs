// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended section variable handling (ext2).

use clean_kernel::Expr;

use crate::section_scope::SectionVariable;
use crate::section_variable_ext2::{ScopedNotation, SectionVarExt2Error, SectionVariableExt2};

// ---------------------------------------------------------------------------
// Scope management
// ---------------------------------------------------------------------------

#[test]
fn test_new_no_scopes() {
    let ext = SectionVariableExt2::new();
    assert_eq!(ext.depth(), 0);
    assert!(!ext.is_in_section());
    assert!(ext.current_section_name().is_none());
}

#[test]
fn test_default_impl() {
    let ext = SectionVariableExt2::default();
    assert_eq!(ext.depth(), 0);
}

#[test]
fn test_enter_section() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Foo");
    assert_eq!(ext.depth(), 1);
    assert!(ext.is_in_section());
    assert_eq!(ext.current_section_name(), Some("Foo"));
}

#[test]
fn test_enter_anonymous_section() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("");
    assert_eq!(ext.depth(), 1);
    assert_eq!(ext.current_section_name(), Some(""));
}

#[test]
fn test_nested_sections_depth() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.enter_section("Inner");
    assert_eq!(ext.depth(), 2);
    assert_eq!(ext.current_section_name(), Some("Inner"));
}

#[test]
fn test_end_section_decreases_depth() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    let result = ext.end_section("S");
    assert!(result.is_ok());
    assert_eq!(ext.depth(), 0);
}

#[test]
fn test_end_section_no_open_error() {
    let mut ext = SectionVariableExt2::new();
    let result = ext.end_section("S");
    assert!(matches!(result, Err(SectionVarExt2Error::NoOpenSection)));
}

#[test]
fn test_end_section_name_mismatch() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Foo");
    let result = ext.end_section("Bar");
    assert!(matches!(
        result,
        Err(SectionVarExt2Error::NameMismatch { .. })
    ));
}

#[test]
fn test_end_anonymous_section_any_name() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("");
    // Empty expected name should match any anonymous section.
    let result = ext.end_section("");
    assert!(result.is_ok());
}

// ---------------------------------------------------------------------------
// Variable management
// ---------------------------------------------------------------------------

#[test]
fn test_add_variable() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    let r = ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ));
    assert!(r.is_ok());
    assert!(ext.find_variable("n").is_some());
}

#[test]
fn test_add_duplicate_variable_error() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    let r = ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Bool"),
    ));
    assert!(matches!(r, Err(SectionVarExt2Error::DuplicateVariable(_))));
}

#[test]
fn test_find_variable_across_scopes() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::implicit(
        "b".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();

    assert!(ext.find_variable("a").is_some());
    assert!(ext.find_variable("b").is_some());
    assert!(ext.find_variable("c").is_none());
}

#[test]
fn test_all_visible_variables_outermost_first() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("Bool"),
    ))
    .unwrap();

    let all = ext.all_visible_variables();
    assert_eq!(all.len(), 2);
    assert_eq!(all[0].name, "a");
    assert_eq!(all[1].name, "b");
}

#[test]
fn test_leave_section_removes_inner_variables() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::explicit(
        "y".to_owned(),
        Expr::const_str("Bool"),
    ))
    .unwrap();

    ext.end_section("Inner").unwrap();

    assert!(ext.find_variable("x").is_some());
    assert!(ext.find_variable("y").is_none());
}

// ---------------------------------------------------------------------------
// Universe parameters
// ---------------------------------------------------------------------------

#[test]
fn test_add_universe_param() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_universe_param("u");
    ext.add_universe_param("v");

    let univs = ext.all_universe_params();
    assert_eq!(univs, vec!["u".to_owned(), "v".to_owned()]);
}

#[test]
fn test_universe_params_across_scopes() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_universe_param("u");
    ext.enter_section("Inner");
    ext.add_universe_param("v");

    let univs = ext.all_universe_params();
    assert_eq!(univs, vec!["u".to_owned(), "v".to_owned()]);
}

#[test]
fn test_universe_params_deduplicated() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_universe_param("u");
    ext.enter_section("Inner");
    ext.add_universe_param("u");

    let univs = ext.all_universe_params();
    assert_eq!(univs.len(), 1);
}

// ---------------------------------------------------------------------------
// Include / omit
// ---------------------------------------------------------------------------

#[test]
fn test_omit_variable() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.omit_variable("n").unwrap();

    assert!(!ext.is_included("n"));
}

#[test]
fn test_include_after_omit() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.omit_variable("n").unwrap();
    ext.include_variable("n").unwrap();

    assert!(ext.is_included("n"));
}

#[test]
fn test_omit_unknown_variable_error() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    let r = ext.omit_variable("nonexistent");
    assert!(matches!(r, Err(SectionVarExt2Error::UnknownVariable(_))));
}

#[test]
fn test_include_unknown_variable_error() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    let r = ext.include_variable("nonexistent");
    assert!(matches!(r, Err(SectionVarExt2Error::UnknownVariable(_))));
}

#[test]
fn test_omit_in_inner_does_not_affect_outer() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.enter_section("Inner");
    ext.omit_variable("x").unwrap();
    assert!(!ext.is_included("x"));

    ext.end_section("Inner").unwrap();
    // After leaving inner, omit should be gone.
    assert!(ext.is_included("x"));
}

// ---------------------------------------------------------------------------
// Notation scoping
// ---------------------------------------------------------------------------

#[test]
fn test_add_and_retrieve_notation() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_notation(ScopedNotation {
        pattern: "_ ++ _".to_owned(),
        expansion: "HAppend.hAppend _ _".to_owned(),
        referenced_vars: vec!["α".to_owned()],
    });

    let notations = ext.all_notations();
    assert_eq!(notations.len(), 1);
    assert_eq!(notations[0].pattern, "_ ++ _");
}

#[test]
fn test_notation_expires_on_section_close() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_notation(ScopedNotation {
        pattern: "_ ++ _".to_owned(),
        expansion: "HAppend.hAppend _ _".to_owned(),
        referenced_vars: vec![],
    });

    let result = ext.end_section("S").unwrap();
    assert_eq!(result.expired_notations.len(), 1);
    assert!(ext.all_notations().is_empty());
}

// ---------------------------------------------------------------------------
// Auto-inclusion and dependency recording
// ---------------------------------------------------------------------------

#[test]
fn test_record_auto_inclusion_basic() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    // Expression references only "n".
    let expr = Expr::const_str("n");
    ext.record_auto_inclusion("myDef", &expr);

    let deps = ext.get_variable_deps("myDef").unwrap();
    assert!(deps.contains("n"));
    assert!(!deps.contains("m"));
}

#[test]
fn test_record_auto_inclusion_respects_omit() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.add_variable(SectionVariable::explicit(
        "m".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.omit_variable("n").unwrap();

    let expr = Expr::app(Expr::const_str("n"), Expr::const_str("m"));
    ext.record_auto_inclusion("myDef", &expr);

    let deps = ext.get_variable_deps("myDef").unwrap();
    assert!(!deps.contains("n")); // omitted
    assert!(deps.contains("m"));
}

#[test]
fn test_record_auto_inclusion_unknown_decl() {
    let ext = SectionVariableExt2::new();
    assert!(ext.get_variable_deps("unknown").is_none());
}

#[test]
fn test_universe_deps_tracking() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_universe_param("u");

    let expr = Expr::const_str("u");
    ext.record_auto_inclusion("myDef", &expr);

    let univs = ext.get_universe_deps("myDef").unwrap();
    assert!(univs.contains("u"));
}

// ---------------------------------------------------------------------------
// Dependent variable analysis
// ---------------------------------------------------------------------------

#[test]
fn test_dependency_closure_basic() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    // α : Type
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();
    // x : alpha (depends on alpha)
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("alpha"),
    ))
    .unwrap();

    let mut initial = std::collections::HashSet::new();
    initial.insert("x".to_owned());

    let closed = ext.dependency_closure(&initial);
    // x depends on alpha, so closure should include both.
    assert!(closed.contains("x"));
    assert!(closed.contains("alpha"));
}

#[test]
fn test_dependency_closure_no_deps() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let mut initial = std::collections::HashSet::new();
    initial.insert("n".to_owned());

    let closed = ext.dependency_closure(&initial);
    assert_eq!(closed.len(), 1);
    assert!(closed.contains("n"));
}

#[test]
fn test_auto_inclusion_expands_deps() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    // α : Type
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();
    // x : alpha (type references section var alpha)
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("alpha"),
    ))
    .unwrap();

    // Expression only references x directly, but x depends on alpha.
    let expr = Expr::const_str("x");
    ext.record_auto_inclusion("foo", &expr);

    let deps = ext.get_variable_deps("foo").unwrap();
    assert!(deps.contains("x"));
    assert!(deps.contains("alpha"));
}

// ---------------------------------------------------------------------------
// End-section generalization
// ---------------------------------------------------------------------------

#[test]
fn test_generalize_type_adds_pi() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::app(Expr::const_str("alpha"), Expr::const_str("n"));
    ext.record_auto_inclusion("foo", &body);

    let generalized = ext.generalize_type("foo", &body);

    match generalized.kind() {
        clean_kernel::expr::ExprKind::Pi(_, _, inner) => match inner.kind() {
            clean_kernel::expr::ExprKind::Pi(_, _, _) => {}
            other => panic!("expected inner Pi, got {other:?}"),
        },
        other => panic!("expected outer Pi, got {other:?}"),
    }
}

#[test]
fn test_generalize_value_adds_lambda() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::const_str("n");
    ext.record_auto_inclusion("foo", &body);

    let generalized = ext.generalize_value("foo", &body);

    match generalized.kind() {
        clean_kernel::expr::ExprKind::Lam(_, _, _) => {}
        other => panic!("expected Lam, got {other:?}"),
    }
}

#[test]
fn test_generalize_no_deps_returns_unchanged() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::const_str("Bool");
    ext.record_auto_inclusion("foo", &body);

    let generalized = ext.generalize_type("foo", &body);
    assert_eq!(format!("{generalized:?}"), format!("{body:?}"));
}

#[test]
fn test_generalize_unknown_decl() {
    let ext = SectionVariableExt2::new();
    let body = Expr::const_str("Bool");
    let generalized = ext.generalize_type("unknown", &body);
    assert_eq!(format!("{generalized:?}"), format!("{body:?}"));
}

// ---------------------------------------------------------------------------
// Fvar substitution
// ---------------------------------------------------------------------------

#[test]
fn test_substitute_fvars_basic() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::const_str("n");
    ext.record_auto_inclusion("foo", &body);

    let substituted = ext.substitute_fvars("foo", &body);
    match substituted.kind() {
        clean_kernel::expr::ExprKind::BVar(0) => {}
        other => panic!("expected BVar(0), got {other:?}"),
    }
}

#[test]
fn test_substitute_fvars_two_vars() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::app(Expr::const_str("a"), Expr::const_str("b"));
    ext.record_auto_inclusion("foo", &body);

    let substituted = ext.substitute_fvars("foo", &body);
    // a is outermost (idx=1), b is innermost (idx=0)
    match substituted.kind() {
        clean_kernel::expr::ExprKind::App(f, arg) => {
            match f.kind() {
                clean_kernel::expr::ExprKind::BVar(1) => {}
                other => panic!("expected BVar(1) for a, got {other:?}"),
            }
            match arg.kind() {
                clean_kernel::expr::ExprKind::BVar(0) => {}
                other => panic!("expected BVar(0) for b, got {other:?}"),
            }
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_substitute_fvars_no_deps() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let body = Expr::const_str("Bool");
    ext.record_auto_inclusion("foo", &body);

    let substituted = ext.substitute_fvars("foo", &body);
    // No deps, should be unchanged.
    assert_eq!(format!("{substituted:?}"), format!("{body:?}"));
}

#[test]
fn test_substitute_fvars_unknown_decl() {
    let ext = SectionVariableExt2::new();
    let body = Expr::const_str("Bool");
    let substituted = ext.substitute_fvars("unknown", &body);
    assert_eq!(format!("{substituted:?}"), format!("{body:?}"));
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

#[test]
fn test_stats_initial() {
    let ext = SectionVariableExt2::new();
    let stats = ext.stats();
    assert_eq!(stats.vars_included, 0);
    assert_eq!(stats.vars_generalized, 0);
    assert_eq!(stats.vars_omitted, 0);
    assert_eq!(stats.max_depth, 0);
}

#[test]
fn test_stats_max_depth() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("A");
    ext.enter_section("B");
    ext.enter_section("C");
    assert_eq!(ext.stats().max_depth, 3);

    ext.end_section("C").unwrap();
    // Max depth is a high-water mark, doesn't decrease.
    assert_eq!(ext.stats().max_depth, 3);
}

#[test]
fn test_stats_vars_omitted() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "a".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.add_variable(SectionVariable::explicit(
        "b".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.omit_variable("a").unwrap();
    ext.omit_variable("b").unwrap();

    assert_eq!(ext.stats().vars_omitted, 2);
}

#[test]
fn test_stats_vars_included() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "n".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();

    let expr = Expr::const_str("n");
    ext.record_auto_inclusion("foo", &expr);

    assert_eq!(ext.stats().vars_included, 1);
}

// ---------------------------------------------------------------------------
// End-section result
// ---------------------------------------------------------------------------

#[test]
fn test_end_section_result_contains_variables() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("Nat"),
    ))
    .unwrap();
    ext.add_universe_param("u");

    let result = ext.end_section("S").unwrap();
    assert_eq!(result.name, "S");
    assert_eq!(result.closed_variables.len(), 1);
    assert_eq!(result.closed_variables[0].name, "x");
    assert_eq!(result.closed_universes, vec!["u".to_owned()]);
}

// ---------------------------------------------------------------------------
// Complex scenarios
// ---------------------------------------------------------------------------

#[test]
fn test_nested_section_full_lifecycle() {
    let mut ext = SectionVariableExt2::new();

    // Outer section
    ext.enter_section("Outer");
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();
    ext.add_universe_param("u");

    // Inner section
    ext.enter_section("Inner");
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("alpha"),
    ))
    .unwrap();

    // Both visible
    assert_eq!(ext.all_visible_variables().len(), 2);
    assert_eq!(ext.depth(), 2);

    // Record dependency using both
    let expr = Expr::app(Expr::const_str("alpha"), Expr::const_str("x"));
    ext.record_auto_inclusion("bar", &expr);

    let deps = ext.get_variable_deps("bar").unwrap();
    assert!(deps.contains("alpha"));
    assert!(deps.contains("x"));

    // Close inner
    let inner_result = ext.end_section("Inner").unwrap();
    assert_eq!(inner_result.closed_variables.len(), 1);
    assert_eq!(ext.depth(), 1);
    assert!(ext.find_variable("x").is_none());
    assert!(ext.find_variable("alpha").is_some());

    // Close outer
    let outer_result = ext.end_section("Outer").unwrap();
    assert_eq!(outer_result.closed_variables.len(), 1);
    assert_eq!(outer_result.closed_universes.len(), 1);
    assert_eq!(ext.depth(), 0);
}

#[test]
fn test_transitive_dependency_chain() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("S");

    // α : Type
    ext.add_variable(SectionVariable::implicit(
        "alpha".to_owned(),
        Expr::const_str("Type"),
    ))
    .unwrap();

    // x : alpha (depends on alpha)
    ext.add_variable(SectionVariable::explicit(
        "x".to_owned(),
        Expr::const_str("alpha"),
    ))
    .unwrap();

    // f : x (depends on x, which depends on alpha)
    ext.add_variable(SectionVariable::explicit(
        "f".to_owned(),
        Expr::const_str("x"),
    ))
    .unwrap();

    // Expression references only f.
    let expr = Expr::const_str("f");
    ext.record_auto_inclusion("myDef", &expr);

    let deps = ext.get_variable_deps("myDef").unwrap();
    // Transitive closure should pull in f -> x -> alpha.
    assert!(deps.contains("f"));
    assert!(deps.contains("x"));
    assert!(deps.contains("alpha"));
}

#[test]
fn test_notation_scoping_nested() {
    let mut ext = SectionVariableExt2::new();
    ext.enter_section("Outer");
    ext.add_notation(ScopedNotation {
        pattern: "_ <> _".to_owned(),
        expansion: "Append _ _".to_owned(),
        referenced_vars: vec![],
    });

    ext.enter_section("Inner");
    ext.add_notation(ScopedNotation {
        pattern: "_ ** _".to_owned(),
        expansion: "Pow _ _".to_owned(),
        referenced_vars: vec![],
    });

    assert_eq!(ext.all_notations().len(), 2);

    ext.end_section("Inner").unwrap();
    // Inner notation expired.
    assert_eq!(ext.all_notations().len(), 1);
    assert_eq!(ext.all_notations()[0].pattern, "_ <> _");

    ext.end_section("Outer").unwrap();
    assert!(ext.all_notations().is_empty());
}
