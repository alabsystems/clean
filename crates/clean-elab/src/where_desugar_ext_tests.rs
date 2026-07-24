// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended where-clause desugaring with dependency ordering
//! and cycle detection.

use std::collections::HashSet;

use clean_parser::{Span, SurfaceBinder, SurfaceExpr};

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

fn mk_typed_clause(name: &str, body: SurfaceExpr) -> WhereClause {
    mk_clause(name, vec![], body)
}

// ═══════════════════════════════════════════════════════════════════════════════
// Free identifier collection
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_free_idents_simple_ident() {
    let expr = mk_ident("foo");
    let free = collect_free_idents(&expr);
    assert_eq!(free, HashSet::from(["foo".to_string()]));
}

#[test]
fn test_collect_free_idents_hole_has_none() {
    let expr = SurfaceExpr::Hole(span());
    let free = collect_free_idents(&expr);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_idents_literal_has_none() {
    let expr = SurfaceExpr::nat(42);
    let free = collect_free_idents(&expr);
    assert!(free.is_empty());
}

#[test]
fn test_collect_free_idents_lambda_binds_param() {
    // fun (x : Nat) => x — x is bound, Nat is free
    let expr = SurfaceExpr::Lambda(
        span(),
        vec![SurfaceBinder::explicit("x", mk_ident("Nat"))],
        Box::new(mk_ident("x")),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("Nat"), "Nat should be free");
    assert!(!free.contains("x"), "x should be bound by lambda");
}

#[test]
fn test_collect_free_idents_lambda_body_free_var() {
    // fun (x : Nat) => y — y is free
    let expr = SurfaceExpr::Lambda(
        span(),
        vec![SurfaceBinder::explicit("x", mk_ident("Nat"))],
        Box::new(mk_ident("y")),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("y"), "y should be free in lambda body");
    assert!(free.contains("Nat"), "Nat should be free in binder type");
}

#[test]
fn test_collect_free_idents_let_binds_name() {
    // let z : Nat := x in z — x is free, z is bound in body
    let expr = SurfaceExpr::Let(
        span(),
        SurfaceBinder::explicit("z", mk_ident("Nat")),
        Box::new(mk_ident("x")),
        Box::new(mk_ident("z")),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("x"), "x should be free in let value");
    assert!(free.contains("Nat"), "Nat should be free in let type");
    assert!(!free.contains("z"), "z should be bound in let body");
}

#[test]
fn test_collect_free_idents_let_rec_binds_in_val() {
    // let rec f : Nat := f in f — f is bound in both val and body
    let expr = SurfaceExpr::LetRec(
        span(),
        SurfaceBinder::explicit("f", mk_ident("Nat")),
        Box::new(mk_ident("f")),
        Box::new(mk_ident("f")),
    );
    let free = collect_free_idents(&expr);
    assert!(!free.contains("f"), "f should be bound in let rec");
    assert!(free.contains("Nat"), "Nat should be free in let rec type");
}

#[test]
fn test_collect_free_idents_app_collects_all() {
    // f x y — all three are free
    let expr = SurfaceExpr::app(mk_ident("f"), vec![mk_ident("x"), mk_ident("y")]);
    let free = collect_free_idents(&expr);
    assert!(free.contains("f"));
    assert!(free.contains("x"));
    assert!(free.contains("y"));
}

#[test]
fn test_collect_free_idents_arrow_both_sides() {
    // A -> B — both free
    let expr = SurfaceExpr::Arrow(span(), Box::new(mk_ident("A")), Box::new(mk_ident("B")));
    let free = collect_free_idents(&expr);
    assert!(free.contains("A"));
    assert!(free.contains("B"));
}

#[test]
fn test_collect_free_idents_pi_binds_in_body() {
    // (x : A) -> B x — A is free, x is bound in B x
    let expr = SurfaceExpr::Pi(
        span(),
        vec![SurfaceBinder::explicit("x", mk_ident("A"))],
        Box::new(SurfaceExpr::app(mk_ident("B"), vec![mk_ident("x")])),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("A"), "A should be free");
    assert!(free.contains("B"), "B should be free");
    assert!(!free.contains("x"), "x should be bound by pi");
}

#[test]
fn test_collect_free_idents_nested_scopes() {
    // fun (x : T) => let y := x in f y
    let inner_let = SurfaceExpr::Let(
        span(),
        SurfaceBinder::explicit("y", mk_ident("T")),
        Box::new(mk_ident("x")),
        Box::new(SurfaceExpr::app(mk_ident("f"), vec![mk_ident("y")])),
    );
    let expr = SurfaceExpr::Lambda(
        span(),
        vec![SurfaceBinder::explicit("x", mk_ident("T"))],
        Box::new(inner_let),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("f"), "f should be free");
    assert!(free.contains("T"), "T should be free");
    assert!(!free.contains("x"), "x should be bound by lambda");
    assert!(!free.contains("y"), "y should be bound by let");
}

#[test]
fn test_collect_free_idents_anonymous_binder_not_bound() {
    // fun (_ : Nat) => x — x is free, _ doesn't bind
    let expr = SurfaceExpr::Lambda(
        span(),
        vec![SurfaceBinder::explicit("_", mk_ident("Nat"))],
        Box::new(mk_ident("x")),
    );
    let free = collect_free_idents(&expr);
    assert!(free.contains("x"));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Dependency analysis
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_analyze_where_deps_empty() {
    let result = analyze_where_deps(&[]).expect("should succeed");
    assert!(result.sorted_indices.is_empty());
    assert!(result.mutual_groups.is_empty());
}

#[test]
fn test_analyze_where_deps_single_clause() {
    let clauses = vec![mk_typed_clause("a", mk_ident("x"))];
    let result = analyze_where_deps(&clauses).expect("should succeed");
    assert_eq!(result.sorted_indices, vec![0]);
    assert!(result.mutual_groups.is_empty());
}

#[test]
fn test_analyze_where_deps_independent_clauses() {
    // a := x, b := y — no dependencies between them
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("b", mk_ident("y")),
    ];
    let result = analyze_where_deps(&clauses).expect("should succeed");
    assert_eq!(result.sorted_indices.len(), 2);
    assert!(result.mutual_groups.is_empty());
}

#[test]
fn test_analyze_where_deps_linear_chain() {
    // c depends on b, b depends on a
    // a := x, b := a, c := b
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("c", mk_ident("b")),
    ];
    let result = analyze_where_deps(&clauses).expect("should succeed");

    // a must come before b, b must come before c
    let pos_a = result.sorted_indices.iter().position(|&i| i == 0).unwrap();
    let pos_b = result.sorted_indices.iter().position(|&i| i == 1).unwrap();
    let pos_c = result.sorted_indices.iter().position(|&i| i == 2).unwrap();
    assert!(pos_a < pos_b, "a must precede b");
    assert!(pos_b < pos_c, "b must precede c");
}

#[test]
fn test_analyze_where_deps_reorders_out_of_order() {
    // Written: b := a, a := x — b depends on a, but a is listed second
    let clauses = vec![
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", mk_ident("x")),
    ];
    let result = analyze_where_deps(&clauses).expect("should succeed");

    // a (index 1) should come before b (index 0)
    let pos_a = result.sorted_indices.iter().position(|&i| i == 1).unwrap();
    let pos_b = result.sorted_indices.iter().position(|&i| i == 0).unwrap();
    assert!(pos_a < pos_b, "a should be reordered before b");
}

#[test]
fn test_analyze_where_deps_diamond_dependency() {
    // a := x, b := a, c := a, d := b + c
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("c", mk_ident("a")),
        mk_typed_clause("d", SurfaceExpr::app(mk_ident("b"), vec![mk_ident("c")])),
    ];
    let result = analyze_where_deps(&clauses).expect("should succeed");

    let pos = |idx: usize| {
        result
            .sorted_indices
            .iter()
            .position(|&i| i == idx)
            .unwrap()
    };
    assert!(pos(0) < pos(1), "a before b");
    assert!(pos(0) < pos(2), "a before c");
    assert!(pos(1) < pos(3), "b before d");
    assert!(pos(2) < pos(3), "c before d");
}

#[test]
fn test_analyze_where_deps_mutual_recursion_detected() {
    // a := b, b := a — mutual recursion
    let clauses = vec![
        mk_typed_clause("a", mk_ident("b")),
        mk_typed_clause("b", mk_ident("a")),
    ];
    let result = analyze_where_deps(&clauses).expect("should succeed with mutual group");
    assert_eq!(
        result.mutual_groups.len(),
        1,
        "should detect one mutual group"
    );
    let group = &result.mutual_groups[0];
    assert_eq!(group.len(), 2);
    assert!(group.contains(&0));
    assert!(group.contains(&1));
}

#[test]
fn test_analyze_where_deps_self_reference_no_edge() {
    // a := a — self-reference; should not create a dependency edge to self
    let clauses = vec![mk_typed_clause("a", mk_ident("a"))];
    let result = analyze_where_deps(&clauses).expect("should succeed");
    assert_eq!(result.sorted_indices, vec![0]);
    assert!(
        result.mutual_groups.is_empty(),
        "self-ref is not mutual recursion"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// Error cases
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_analyze_where_deps_duplicate_name_error() {
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("a", mk_ident("y")),
    ];
    let err = analyze_where_deps(&clauses).expect_err("should fail on duplicate");
    match err {
        WhereDesugarError::DuplicateName { name, .. } => {
            assert_eq!(name, "a");
        }
        other => panic!("expected DuplicateName, got {:?}", other),
    }
}

#[test]
fn test_where_desugar_error_display_duplicate() {
    let err = WhereDesugarError::DuplicateName {
        name: "foo".to_string(),
        span: span(),
    };
    let msg = err.to_string();
    assert!(
        msg.contains("duplicate"),
        "error message should mention duplicate"
    );
    assert!(msg.contains("foo"), "error message should mention the name");
}

#[test]
fn test_where_desugar_error_display_cycle() {
    let err = WhereDesugarError::CyclicDependency {
        names: vec!["a".into(), "b".into(), "a".into()],
        span: span(),
    };
    let msg = err.to_string();
    assert!(msg.contains("a -> b -> a"), "should show cycle path");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Ordered desugaring (integration)
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_desugar_where_ordered_empty() {
    let body = mk_ident("x");
    let result = desugar_where_ordered(body, &[]).expect("should succeed");
    assert!(matches!(result, SurfaceExpr::Ident(_, ref n) if n == "x"));
}

#[test]
fn test_desugar_where_ordered_single() {
    let body = mk_ident("a");
    let clauses = vec![mk_typed_clause("a", mk_ident("42"))];
    let result = desugar_where_ordered(body, &clauses).expect("should succeed");

    match result {
        SurfaceExpr::LetRec(_, binder, _, _) => {
            assert_eq!(binder.name, "a");
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

#[test]
fn test_desugar_where_ordered_reorders_deps() {
    // Written order: b depends on a, but b is first
    let body = mk_ident("body");
    let clauses = vec![
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", mk_ident("42")),
    ];
    let result = desugar_where_ordered(body, &clauses).expect("should succeed");

    // After reordering, a should be outermost (first in nesting)
    match result {
        SurfaceExpr::LetRec(_, outer, _, inner_expr) => {
            assert_eq!(outer.name, "a", "a should be outermost (it has no deps)");
            match *inner_expr {
                SurfaceExpr::LetRec(_, inner, _, _) => {
                    assert_eq!(inner.name, "b", "b should be inner (depends on a)");
                }
                other => panic!("expected inner LetRec, got {:?}", other),
            }
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

#[test]
fn test_desugar_where_ordered_preserves_order_when_no_deps() {
    // a := x, b := y — no deps, preserve original order
    let body = mk_ident("body");
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("b", mk_ident("y")),
    ];
    let result = desugar_where_ordered(body, &clauses).expect("should succeed");

    let mut names = Vec::new();
    let mut current = &result;
    while let SurfaceExpr::LetRec(_, b, _, inner) = current {
        names.push(b.name.clone());
        current = inner;
    }
    assert_eq!(names, vec!["a", "b"]);
}

#[test]
fn test_desugar_where_ordered_duplicate_name_fails() {
    let body = mk_ident("body");
    let clauses = vec![
        mk_typed_clause("a", mk_ident("x")),
        mk_typed_clause("a", mk_ident("y")),
    ];
    let err = desugar_where_ordered(body, &clauses).expect_err("should fail");
    assert!(matches!(err, WhereDesugarError::DuplicateName { .. }));
}

#[test]
fn test_desugar_where_ordered_with_type_annotation() {
    let body = mk_ident("body");
    let clauses = vec![mk_clause_with_ret(
        "f",
        vec![SurfaceBinder::explicit("n", mk_ident("Nat"))],
        mk_ident("Nat"),
        mk_ident("n"),
    )];
    let result = desugar_where_ordered(body, &clauses).expect("should succeed");

    match result {
        SurfaceExpr::LetRec(_, binder, val, _) => {
            assert_eq!(binder.name, "f");
            // Value should be Lambda
            assert!(matches!(*val, SurfaceExpr::Lambda(..)));
            // Type should be Pi with Nat codomain
            match binder.ty.as_deref() {
                Some(SurfaceExpr::Pi(_, _, codomain)) => {
                    assert!(matches!(**codomain, SurfaceExpr::Ident(_, ref n) if n == "Nat"));
                }
                other => panic!("expected Pi type, got {:?}", other),
            }
        }
        other => panic!("expected LetRec, got {:?}", other),
    }
}

#[test]
fn test_desugar_where_ordered_complex_chain() {
    // d := c, c := b, b := a, a := 1
    // Should reorder to: a, b, c, d
    let body = mk_ident("d");
    let clauses = vec![
        mk_typed_clause("d", mk_ident("c")),
        mk_typed_clause("c", mk_ident("b")),
        mk_typed_clause("b", mk_ident("a")),
        mk_typed_clause("a", SurfaceExpr::nat(1)),
    ];
    let result = desugar_where_ordered(body, &clauses).expect("should succeed");

    let mut names = Vec::new();
    let mut current = &result;
    while let SurfaceExpr::LetRec(_, b, _, inner) = current {
        names.push(b.name.clone());
        current = inner;
    }
    assert_eq!(names, vec!["a", "b", "c", "d"]);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Clause free ident collection (via analyze_where_deps edge structure)
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_clause_free_idents_excludes_own_params() {
    // f (x : Nat) := x + y — x is param (excluded), y and Nat are free
    let clause = mk_clause(
        "f",
        vec![SurfaceBinder::explicit("x", mk_ident("Nat"))],
        SurfaceExpr::app(mk_ident("add"), vec![mk_ident("x"), mk_ident("y")]),
    );
    let free = clause_free_idents(&clause);
    assert!(!free.contains("x"), "parameter x should be excluded");
    assert!(free.contains("y"), "y should be free");
    assert!(free.contains("add"), "add should be free");
    assert!(free.contains("Nat"), "Nat (in param type) should be free");
}

#[test]
fn test_clause_free_idents_return_type_references() {
    // f (x : Nat) : Vec Nat := x — Vec and Nat in return type are free
    let clause = mk_clause_with_ret(
        "f",
        vec![SurfaceBinder::explicit("x", mk_ident("Nat"))],
        SurfaceExpr::app(mk_ident("Vec"), vec![mk_ident("Nat")]),
        mk_ident("x"),
    );
    let free = clause_free_idents(&clause);
    assert!(free.contains("Vec"), "Vec in return type should be free");
}

// ═══════════════════════════════════════════════════════════════════════════════
// From-parsed ordered desugaring
// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn test_desugar_where_from_parsed_ordered_empty() {
    let body = mk_ident("x");
    let result = desugar_where_from_parsed_ordered(&body, &[]).expect("should succeed");
    assert!(matches!(result, SurfaceExpr::Ident(_, ref n) if n == "x"));
}

#[test]
fn test_desugar_where_from_parsed_ordered_reorders() {
    use clean_parser::WhereLocalDef;

    let body = mk_ident("body");
    let defs = vec![
        WhereLocalDef {
            span: span(),
            name: "b".to_string(),
            binders: vec![],
            ret_ty: None,
            body: mk_ident("a"),
        },
        WhereLocalDef {
            span: span(),
            name: "a".to_string(),
            binders: vec![],
            ret_ty: None,
            body: SurfaceExpr::nat(1),
        },
    ];

    let result = desugar_where_from_parsed_ordered(&body, &defs).expect("should succeed");

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
