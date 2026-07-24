// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended where-clause elaboration.

use std::collections::HashSet;

use clean_parser::{Span, SurfaceBinder, SurfaceExpr, SurfacePattern};

use super::*;
use crate::where_desugar::WhereClause;

fn span() -> Span {
    Span::dummy()
}

fn mk_ident(name: &str) -> SurfaceExpr {
    SurfaceExpr::ident(name)
}

fn mk_clause(name: &str, params: Vec<SurfaceBinder>, body: SurfaceExpr) -> WhereClause {
    WhereClause {
        name: name.to_string(),
        params,
        return_type: None,
        body,
        span: span(),
    }
}

fn mk_typed_clause(name: &str, body: SurfaceExpr) -> WhereClause {
    mk_clause(name, vec![], body)
}

fn mk_clause_with_ret(
    name: &str,
    params: Vec<SurfaceBinder>,
    ret: SurfaceExpr,
    body: SurfaceExpr,
) -> WhereClause {
    WhereClause {
        name: name.to_string(),
        params,
        return_type: Some(ret),
        body,
        span: span(),
    }
}

fn default_config() -> WhereClauseExtConfig {
    WhereClauseExtConfig::default()
}

// =============================================================================
// Classification
// =============================================================================

#[test]
fn test_classify_binding_simple() {
    let all_names: HashSet<String> = ["a", "b"].iter().map(|s| s.to_string()).collect();
    let clause = mk_typed_clause("a", mk_ident("x"));
    let kind = classify_binding(&clause, &all_names);
    assert!(matches!(kind, WhereBindingKind::Simple));
}

#[test]
fn test_classify_binding_recursive() {
    let all_names: HashSet<String> = ["a", "b"].iter().map(|s| s.to_string()).collect();
    let clause = mk_typed_clause("a", mk_ident("b"));
    let kind = classify_binding(&clause, &all_names);
    match kind {
        WhereBindingKind::Recursive { deps } => {
            assert!(deps.contains(&"b".to_string()));
        }
        other => panic!("expected Recursive, got {:?}", other),
    }
}

#[test]
fn test_classify_binding_self_ref_is_simple() {
    let all_names: HashSet<String> = ["a"].iter().map(|s| s.to_string()).collect();
    let clause = mk_typed_clause("a", mk_ident("a"));
    let kind = classify_binding(&clause, &all_names);
    // Self-reference is excluded from deps, so it's Simple.
    assert!(matches!(kind, WhereBindingKind::Simple));
}

#[test]
fn test_classify_bindings_mixed() {
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("c", mk_ident("y")),
    ];
    let classified = classify_bindings(&clauses);
    assert_eq!(classified.len(), 3);
    assert!(matches!(classified[0].1, WhereBindingKind::Simple));
    assert!(matches!(
        classified[1].1,
        WhereBindingKind::Recursive { .. }
    ));
    assert!(matches!(classified[2].1, WhereBindingKind::Simple));
}

// =============================================================================
// Type inference
// =============================================================================

#[test]
fn test_infer_omitted_type_returns_hole() {
    let binding = ExtWhereBinding {
        name: "f".to_string(),
        kind: WhereBindingKind::Simple,
        params: vec![],
        return_type: None,
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    };
    let inferred = infer_omitted_type(&binding);
    assert!(inferred.is_some());
    assert!(matches!(inferred.unwrap(), SurfaceExpr::Hole(_)));
}

#[test]
fn test_infer_omitted_type_with_annotation_returns_none() {
    let binding = ExtWhereBinding {
        name: "f".to_string(),
        kind: WhereBindingKind::Simple,
        params: vec![],
        return_type: Some(mk_ident("Nat")),
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    };
    assert!(infer_omitted_type(&binding).is_none());
}

// =============================================================================
// Validation
// =============================================================================

#[test]
fn test_validate_empty_bindings() {
    let result = validate_bindings(&[], &default_config());
    assert!(result.is_ok());
}

#[test]
fn test_validate_duplicate_binding_error() {
    let bindings = vec![
        ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("x"),
            inferred_type: None,
            span: span(),
        },
        ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("y"),
            inferred_type: None,
            span: span(),
        },
    ];
    let err = validate_bindings(&bindings, &default_config()).unwrap_err();
    assert!(matches!(err, WhereClauseExtError::DuplicateBinding { ref name, .. } if name == "a"));
}

#[test]
fn test_validate_exceeded_max_bindings() {
    let mut config = default_config();
    config.max_bindings = 1;
    let bindings = vec![
        ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("x"),
            inferred_type: None,
            span: span(),
        },
        ExtWhereBinding {
            name: "b".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("y"),
            inferred_type: None,
            span: span(),
        },
    ];
    let err = validate_bindings(&bindings, &config).unwrap_err();
    assert!(matches!(
        err,
        WhereClauseExtError::ExceededMaxBindings {
            count: 2,
            max: 1,
            ..
        }
    ));
}

#[test]
fn test_validate_recursive_not_allowed() {
    let mut config = default_config();
    config.allow_recursive_bindings = false;
    let bindings = vec![ExtWhereBinding {
        name: "a".to_string(),
        kind: WhereBindingKind::Recursive {
            deps: vec!["b".to_string()],
        },
        params: vec![],
        return_type: Some(mk_ident("Nat")),
        body: mk_ident("b"),
        inferred_type: None,
        span: span(),
    }];
    let err = validate_bindings(&bindings, &config).unwrap_err();
    assert!(matches!(
        err,
        WhereClauseExtError::RecursiveBindingNotAllowed { .. }
    ));
}

#[test]
fn test_validate_pattern_not_allowed() {
    let mut config = default_config();
    config.allow_pattern_bindings = false;
    let bindings = vec![ExtWhereBinding {
        name: "a".to_string(),
        kind: WhereBindingKind::Pattern {
            pattern: SurfacePattern::Var("x".to_string()),
            scrutinee: mk_ident("pair"),
        },
        params: vec![],
        return_type: Some(mk_ident("Nat")),
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    }];
    let err = validate_bindings(&bindings, &config).unwrap_err();
    assert!(matches!(
        err,
        WhereClauseExtError::PatternBindingNotAllowed { .. }
    ));
}

#[test]
fn test_validate_guard_not_allowed() {
    let mut config = default_config();
    config.allow_guards = false;
    let bindings = vec![ExtWhereBinding {
        name: "a".to_string(),
        kind: WhereBindingKind::Guarded {
            condition: mk_ident("cond"),
        },
        params: vec![],
        return_type: Some(mk_ident("Nat")),
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    }];
    let err = validate_bindings(&bindings, &config).unwrap_err();
    assert!(matches!(err, WhereClauseExtError::GuardNotAllowed { .. }));
}

#[test]
fn test_validate_type_inference_not_allowed() {
    let mut config = default_config();
    config.allow_type_inference = false;
    let bindings = vec![ExtWhereBinding {
        name: "a".to_string(),
        kind: WhereBindingKind::Simple,
        params: vec![],
        return_type: None,
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    }];
    let err = validate_bindings(&bindings, &config).unwrap_err();
    assert!(matches!(
        err,
        WhereClauseExtError::TypeInferenceNotAllowed { .. }
    ));
}

// =============================================================================
// Dependency ordering
// =============================================================================

#[test]
fn test_order_bindings_empty() {
    let result = order_bindings(&[]).expect("should succeed");
    assert!(result.is_empty());
}

#[test]
fn test_order_bindings_single() {
    let bindings = vec![ExtWhereBinding {
        name: "a".to_string(),
        kind: WhereBindingKind::Simple,
        params: vec![],
        return_type: None,
        body: mk_ident("x"),
        inferred_type: None,
        span: span(),
    }];
    let order = order_bindings(&bindings).expect("should succeed");
    assert_eq!(order, vec![0]);
}

#[test]
fn test_order_bindings_dependency_chain() {
    let bindings = vec![
        ExtWhereBinding {
            name: "b".to_string(),
            kind: WhereBindingKind::Recursive {
                deps: vec!["a".to_string()],
            },
            params: vec![],
            return_type: None,
            body: mk_ident("a"),
            inferred_type: None,
            span: span(),
        },
        ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: None,
            body: mk_ident("x"),
            inferred_type: None,
            span: span(),
        },
    ];
    let order = order_bindings(&bindings).expect("should succeed");
    // a (index 1) should come before b (index 0)
    let pos_a = order.iter().position(|&i| i == 1).unwrap();
    let pos_b = order.iter().position(|&i| i == 0).unwrap();
    assert!(pos_a < pos_b, "a should precede b");
}

// =============================================================================
// build_ext_where_bindings
// =============================================================================

#[test]
fn test_build_ext_where_bindings_empty() {
    let result = build_ext_where_bindings(&[], &default_config()).expect("should succeed");
    assert!(result.bindings.is_empty());
    assert!(result.recursive_groups.is_empty());
    assert!(result.inferred_types.is_empty());
}

#[test]
fn test_build_ext_where_bindings_simple() {
    let clauses = vec![mk_typed_clause("a", mk_ident("x"))];
    let result = build_ext_where_bindings(&clauses, &default_config()).expect("should succeed");
    assert_eq!(result.bindings.len(), 1);
    assert_eq!(result.bindings[0].name, "a");
}

#[test]
fn test_build_ext_where_bindings_infers_types() {
    // No return type annotation => should get an inferred type.
    let clauses = vec![mk_typed_clause("a", mk_ident("x"))];
    let result = build_ext_where_bindings(&clauses, &default_config()).expect("should succeed");
    assert!(result.inferred_types.contains_key("a"));
    assert!(matches!(
        result.inferred_types.get("a"),
        Some(SurfaceExpr::Hole(_))
    ));
}

#[test]
fn test_build_ext_where_bindings_no_infer_with_annotation() {
    let clauses = vec![mk_clause_with_ret(
        "a",
        vec![],
        mk_ident("Nat"),
        mk_ident("x"),
    )];
    let result = build_ext_where_bindings(&clauses, &default_config()).expect("should succeed");
    assert!(!result.inferred_types.contains_key("a"));
}

#[test]
fn test_build_ext_where_bindings_orders_deps() {
    // b depends on a, but b comes first in input
    let clauses = vec![
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", mk_ident("x")),
    ];
    let result = build_ext_where_bindings(&clauses, &default_config()).expect("should succeed");
    assert_eq!(result.bindings[0].name, "a");
    assert_eq!(result.bindings[1].name, "b");
}

#[test]
fn test_build_ext_where_bindings_detects_mutual_recursion() {
    let clauses = vec![
        mk_typed_clause("a", mk_ident("b")),
        mk_typed_clause("b", mk_ident("a")),
    ];
    let result = build_ext_where_bindings(&clauses, &default_config()).expect("should succeed");
    assert_eq!(result.recursive_groups.len(), 1);
    let group = &result.recursive_groups[0];
    assert_eq!(group.len(), 2);
}

#[test]
fn test_build_ext_where_bindings_duplicate_error() {
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("a", mk_ident("y")),
    ];
    let err = build_ext_where_bindings(&clauses, &default_config()).unwrap_err();
    assert!(matches!(err, WhereClauseExtError::DuplicateBinding { .. }));
}

// =============================================================================
// Desugaring
// =============================================================================

#[test]
fn test_desugar_ext_where_empty() {
    let body = mk_ident("x");
    let result = WhereClauseExtResult {
        bindings: vec![],
        recursive_groups: vec![],
        inferred_types: HashMap::new(),
    };
    let desugared = desugar_ext_where(body, &result);
    assert!(matches!(desugared, SurfaceExpr::Ident(_, ref n) if n == "x"));
}

#[test]
fn test_desugar_ext_where_simple_binding() {
    let body = mk_ident("body");
    let result = WhereClauseExtResult {
        bindings: vec![ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("42"),
            inferred_type: None,
            span: span(),
        }],
        recursive_groups: vec![],
        inferred_types: HashMap::new(),
    };
    let desugared = desugar_ext_where(body, &result);
    match desugared {
        SurfaceExpr::LetRec(_, binder, _, _) => {
            assert_eq!(binder.name, "a");
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

#[test]
fn test_desugar_ext_where_guarded_binding() {
    let body = mk_ident("body");
    let result = WhereClauseExtResult {
        bindings: vec![ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Guarded {
                condition: mk_ident("cond"),
            },
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("42"),
            inferred_type: None,
            span: span(),
        }],
        recursive_groups: vec![],
        inferred_types: HashMap::new(),
    };
    let desugared = desugar_ext_where(body, &result);
    match desugared {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "a");
            // Value should be an If expression.
            assert!(matches!(*val, SurfaceExpr::If(..)));
        }
        other => panic!("expected LetRec with If value, got {:?}", other),
    }
}

#[test]
fn test_desugar_ext_where_pattern_binding() {
    let body = mk_ident("body");
    let result = WhereClauseExtResult {
        bindings: vec![ExtWhereBinding {
            name: "a".to_string(),
            kind: WhereBindingKind::Pattern {
                pattern: SurfacePattern::Var("x".to_string()),
                scrutinee: mk_ident("pair"),
            },
            params: vec![],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("x"),
            inferred_type: None,
            span: span(),
        }],
        recursive_groups: vec![],
        inferred_types: HashMap::new(),
    };
    let desugared = desugar_ext_where(body, &result);
    match desugared {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "a");
            // Value should be a Match expression.
            assert!(matches!(*val, SurfaceExpr::Match(..)));
        }
        other => panic!("expected LetRec with Match value, got {:?}", other),
    }
}

#[test]
fn test_desugar_ext_where_with_params() {
    let body = mk_ident("body");
    let result = WhereClauseExtResult {
        bindings: vec![ExtWhereBinding {
            name: "f".to_string(),
            kind: WhereBindingKind::Simple,
            params: vec![SurfaceBinder::explicit("n", mk_ident("Nat"))],
            return_type: Some(mk_ident("Nat")),
            body: mk_ident("n"),
            inferred_type: None,
            span: span(),
        }],
        recursive_groups: vec![],
        inferred_types: HashMap::new(),
    };
    let desugared = desugar_ext_where(body, &result);
    match desugared {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "f");
            assert!(matches!(*val, SurfaceExpr::Lambda(..)));
            // Type should be Pi.
            assert!(matches!(binder.ty.as_deref(), Some(SurfaceExpr::Pi(..))));
        }
        other => panic!("expected LetRec with Lambda, got {:?}", other),
    }
}

// =============================================================================
// process_where_clause_ext (end-to-end)
// =============================================================================

#[test]
fn test_process_where_clause_ext_empty() {
    let body = mk_ident("x");
    let result = process_where_clause_ext(body, &[], &default_config()).expect("should succeed");
    assert!(matches!(result, SurfaceExpr::Ident(_, ref n) if n == "x"));
}

#[test]
fn test_process_where_clause_ext_single() {
    let body = mk_ident("a");
    let clauses = vec![mk_typed_clause("a", mk_ident("42"))];
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");
    assert!(matches!(result, SurfaceExpr::LetRec(..)));
}

#[test]
fn test_process_where_clause_ext_reorders_deps() {
    let body = mk_ident("body");
    let clauses = vec![
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", mk_ident("x")),
    ];
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");

    // a should be outermost
    match result {
        SurfaceExpr::LetRec(_, outer, _, inner_expr) => {
            assert_eq!(outer.name, "a");
            match *inner_expr {
                SurfaceExpr::LetRec(_, inner, _, _) => {
                    assert_eq!(inner.name, "b");
                }
                other => panic!("expected inner LetRec, got {:?}", other),
            }
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

#[test]
fn test_process_where_clause_ext_complex_chain() {
    // d := c, c := b, b := a, a := 1
    let body = mk_ident("d");
    let clauses = vec![
        mk_typed_clause("d", mk_ident("c")),
        mk_typed_clause("c", mk_ident("b")),
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", SurfaceExpr::nat(1)),
    ];
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");

    let mut names = Vec::new();
    let mut current = &result;
    loop {
        match current {
            SurfaceExpr::LetRec(_, b, _, inner) => {
                names.push(b.name.clone());
                current = inner;
            }
            _ => break,
        }
    }
    assert_eq!(names, vec!["a", "b", "c", "d"]);
}

#[test]
fn test_process_where_clause_ext_duplicate_error() {
    let body = mk_ident("body");
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("a", mk_ident("y")),
    ];
    let err = process_where_clause_ext(body, &clauses, &default_config()).unwrap_err();
    assert!(matches!(err, WhereClauseExtError::DuplicateBinding { .. }));
}

#[test]
fn test_process_where_clause_ext_with_params_and_ret() {
    let body = mk_ident("body");
    let clauses = vec![mk_clause_with_ret(
        "f",
        vec![SurfaceBinder::explicit("n", mk_ident("Nat"))],
        mk_ident("Nat"),
        mk_ident("n"),
    )];
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");
    match result {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "f");
            assert!(matches!(*val, SurfaceExpr::Lambda(..)));
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_config_default_values() {
    let config = WhereClauseExtConfig::default();
    assert!(config.allow_recursive_bindings);
    assert!(config.allow_type_inference);
    assert!(config.allow_pattern_bindings);
    assert!(config.allow_guards);
    assert_eq!(config.max_binding_depth, 64);
    assert_eq!(config.max_bindings, 256);
}

#[test]
fn test_error_display_dependency_cycle() {
    let err = WhereClauseExtError::DependencyCycle {
        names: vec!["a".into(), "b".into(), "a".into()],
        span: span(),
    };
    let msg = err.to_string();
    assert!(msg.contains("a -> b -> a"));
}

#[test]
fn test_error_display_exceeded_max_bindings() {
    let err = WhereClauseExtError::ExceededMaxBindings {
        count: 300,
        max: 256,
        span: span(),
    };
    let msg = err.to_string();
    assert!(msg.contains("300"));
    assert!(msg.contains("256"));
}

#[test]
fn test_error_display_duplicate_binding() {
    let err = WhereClauseExtError::DuplicateBinding {
        name: "foo".to_string(),
        span: span(),
    };
    let msg = err.to_string();
    assert!(msg.contains("duplicate"));
    assert!(msg.contains("foo"));
}

#[test]
fn test_deeply_nested_independent_bindings() {
    // 10 independent bindings should all appear in output
    let clauses: Vec<WhereClause> = (0..10)
        .map(|i| mk_typed_clause(&format!("v{i}"), SurfaceExpr::nat(i as u64)))
        .collect();
    let body = mk_ident("body");
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");

    let mut count = 0;
    let mut current = &result;
    loop {
        match current {
            SurfaceExpr::LetRec(_, _, _, inner) => {
                count += 1;
                current = inner;
            }
            _ => break,
        }
    }
    assert_eq!(count, 10);
}

#[test]
fn test_binding_with_inferred_type_uses_hole() {
    // When return_type is None, the desugared type should be a Hole.
    let body = mk_ident("body");
    let clauses = vec![mk_typed_clause("a", mk_ident("x"))];
    let result =
        process_where_clause_ext(body, &clauses, &default_config()).expect("should succeed");
    match result {
        SurfaceExpr::LetRec(_, binder, _, _) => {
            // Type should be Hole since no annotation provided.
            match binder.ty.as_deref() {
                Some(SurfaceExpr::Hole(_)) => {}
                other => panic!("expected Hole type, got {:?}", other),
            }
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}
