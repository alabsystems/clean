// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended preprocessing pipeline.

use std::collections::HashSet;

use clean_parser::{OpenPath, Span, SurfaceArg, SurfaceDecl, SurfaceExpr, SurfaceLit};

use crate::preprocess_ext::*;

fn span() -> Span {
    Span { start: 0, end: 0 }
}

fn mk_def(name: &str, refs: Vec<&str>) -> SurfaceDecl {
    // Build a body that references the given names via nested Ident nodes.
    let body = if refs.is_empty() {
        SurfaceExpr::Lit(span(), SurfaceLit::Nat(0))
    } else {
        // Chain idents as a nested App: f(a)(b)(c)...
        let mut expr = SurfaceExpr::Ident(span(), refs[0].to_string());
        for r in &refs[1..] {
            expr = SurfaceExpr::App(
                span(),
                Box::new(expr),
                vec![SurfaceArg {
                    span: span(),
                    expr: SurfaceExpr::Ident(span(), r.to_string()),
                    name: None,
                }],
            );
        }
        expr
    };

    SurfaceDecl::Def {
        span: span(),
        name: name.to_string(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: None,
        val: Box::new(body),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: Default::default(),
        where_decls: Vec::new(),
    }
}

fn mk_def_with_universes(name: &str, univs: Vec<&str>) -> SurfaceDecl {
    SurfaceDecl::Def {
        span: span(),
        name: name.to_string(),
        universe_params: univs.into_iter().map(String::from).collect(),
        binders: Vec::new(),
        ty: None,
        val: Box::new(SurfaceExpr::Lit(span(), SurfaceLit::Nat(0))),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: Default::default(),
        where_decls: Vec::new(),
    }
}

fn mk_theorem(name: &str, ty_ref: &str, proof_ref: &str) -> SurfaceDecl {
    SurfaceDecl::Theorem {
        span: span(),
        name: name.to_string(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: Box::new(SurfaceExpr::Ident(span(), ty_ref.to_string())),
        proof: Box::new(SurfaceExpr::Ident(span(), proof_ref.to_string())),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: Default::default(),
        where_decls: Vec::new(),
    }
}

fn mk_axiom(name: &str, ty_ref: &str) -> SurfaceDecl {
    SurfaceDecl::Axiom {
        span: span(),
        name: name.to_string(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: Box::new(SurfaceExpr::Ident(span(), ty_ref.to_string())),
        attrs: Vec::new(),
        modifiers: Default::default(),
    }
}

fn mk_example(body_ref: &str) -> SurfaceDecl {
    SurfaceDecl::Example {
        span: span(),
        binders: Vec::new(),
        ty: None,
        val: Box::new(SurfaceExpr::Ident(span(), body_ref.to_string())),
    }
}

fn mk_open(ns_parts: Vec<&str>) -> SurfaceDecl {
    SurfaceDecl::Open {
        span: span(),
        paths: vec![OpenPath {
            path: ns_parts.into_iter().map(String::from).collect(),
            names: Vec::new(),
            hiding: Vec::new(),
            renaming: Vec::new(),
        }],
        body: None,
        scoped: false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 1: Docstring extraction
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_extract_docstrings_block_comment() {
    let decls = vec![mk_def("foo", vec![])];
    let comments = vec!["/-- A foo function -/"];
    let docs = extract_docstrings(&comments, &decls);
    assert_eq!(docs.len(), 1);
    assert_eq!(docs[0].text, "A foo function");
    assert_eq!(docs[0].decl_name, "foo");
}

#[test]
fn test_extract_docstrings_line_comment() {
    let decls = vec![mk_def("bar", vec![])];
    let comments = vec!["-- A bar function"];
    let docs = extract_docstrings(&comments, &decls);
    assert_eq!(docs.len(), 1);
    assert_eq!(docs[0].text, "A bar function");
    assert_eq!(docs[0].decl_name, "bar");
}

#[test]
fn test_extract_docstrings_empty_comments() {
    let decls = vec![mk_def("x", vec![])];
    let comments: Vec<&str> = vec![];
    let docs = extract_docstrings(&comments, &decls);
    assert!(docs.is_empty());
}

#[test]
fn test_extract_docstrings_non_doc_comment() {
    let decls = vec![mk_def("x", vec![])];
    let comments = vec!["just a string, not a comment"];
    let docs = extract_docstrings(&comments, &decls);
    assert!(docs.is_empty());
}

#[test]
fn test_extract_docstrings_multiple() {
    let decls = vec![mk_def("a", vec![]), mk_def("b", vec![])];
    let comments = vec!["/-- first -/", "-- second"];
    let docs = extract_docstrings(&comments, &decls);
    assert_eq!(docs.len(), 2);
    assert_eq!(docs[0].decl_name, "a");
    assert_eq!(docs[1].decl_name, "b");
}

#[test]
fn test_extract_docstrings_more_comments_than_decls() {
    let decls = vec![mk_def("a", vec![])];
    let comments = vec!["/-- first -/", "/-- orphan -/"];
    let docs = extract_docstrings(&comments, &decls);
    assert_eq!(docs.len(), 1);
}

#[test]
fn test_extract_docstrings_overlapping_delimiter_no_panic() {
    // "/--/" satisfies both starts_with("/--") and ends_with("-/") but has
    // len()==4, so the naive slice trimmed[3..len-2] == trimmed[3..2] would
    // panic ("byte range starts at 3 but ends at 2"). The length precondition
    // (len >= 5) must exclude this degenerate overlapping-delimiter case.
    let decls = vec![mk_def("a", vec![])];
    let comments = vec!["/--/"];
    let docs = extract_docstrings(&comments, &decls);
    // Not a valid non-empty doc comment: yields no docstring, and must not panic.
    assert!(docs.is_empty());
}

#[test]
fn test_extract_docstrings_minimal_valid_doc_comment_unchanged() {
    // Boundary above the fix: len==5 "/---/" is a valid (empty-body) doc
    // comment shape; its inner slice trimmed[3..3] is "" so it is skipped just
    // as before. Confirms the fix does not alter correct-path behavior.
    let decls = vec![mk_def("a", vec![])];
    let comments = vec!["/---/"];
    let docs = extract_docstrings(&comments, &decls);
    assert!(docs.is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 2: Mutual block detection
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_detect_mutual_groups_no_cycles() {
    let decls = vec![mk_def("a", vec![]), mk_def("b", vec!["a"])];
    let groups = detect_mutual_groups(&decls);
    assert!(groups.is_empty());
}

#[test]
fn test_detect_mutual_groups_simple_cycle() {
    let decls = vec![mk_def("a", vec!["b"]), mk_def("b", vec!["a"])];
    let groups = detect_mutual_groups(&decls);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].names.len(), 2);
    assert!(groups[0].names.contains(&"a".to_string()));
    assert!(groups[0].names.contains(&"b".to_string()));
}

#[test]
fn test_detect_mutual_groups_three_way_cycle() {
    let decls = vec![
        mk_def("a", vec!["b"]),
        mk_def("b", vec!["c"]),
        mk_def("c", vec!["a"]),
    ];
    let groups = detect_mutual_groups(&decls);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].names.len(), 3);
}

#[test]
fn test_detect_mutual_groups_self_reference_not_mutual() {
    // Self-reference is a single recursive def, not a mutual group.
    let decls = vec![mk_def("f", vec!["f"])];
    let groups = detect_mutual_groups(&decls);
    // SCC of size 1 with self-loop is filtered out (only size > 1 counts).
    assert!(groups.is_empty());
}

#[test]
fn test_detect_mutual_groups_disconnected() {
    let decls = vec![
        mk_def("a", vec!["b"]),
        mk_def("b", vec!["a"]),
        mk_def("c", vec!["d"]),
        mk_def("d", vec!["c"]),
    ];
    let groups = detect_mutual_groups(&decls);
    assert_eq!(groups.len(), 2);
}

#[test]
fn test_detect_mutual_groups_empty() {
    let groups = detect_mutual_groups(&[]);
    assert!(groups.is_empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 3: Universe parameter collection
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_collect_universe_params_none() {
    let decls = vec![mk_def("a", vec![])];
    let params = collect_universe_params(&decls);
    assert!(params.is_empty());
}

#[test]
fn test_collect_universe_params_single() {
    let decls = vec![mk_def_with_universes("foo", vec!["u"])];
    let params = collect_universe_params(&decls);
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].name, "u");
    assert_eq!(params[0].decl_name, "foo");
}

#[test]
fn test_collect_universe_params_multiple() {
    let decls = vec![
        mk_def_with_universes("foo", vec!["u", "v"]),
        mk_def_with_universes("bar", vec!["w"]),
    ];
    let params = collect_universe_params(&decls);
    assert_eq!(params.len(), 3);
}

#[test]
fn test_collect_universe_params_theorem() {
    let decl = SurfaceDecl::Theorem {
        span: span(),
        name: "thm".to_string(),
        universe_params: vec!["u".to_string()],
        binders: Vec::new(),
        ty: Box::new(SurfaceExpr::Ident(span(), "Prop".to_string())),
        proof: Box::new(SurfaceExpr::Ident(span(), "sorry".to_string())),
        attrs: Vec::new(),
        termination: Default::default(),
        modifiers: Default::default(),
        where_decls: Vec::new(),
    };
    let params = collect_universe_params(&[decl]);
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].name, "u");
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 4: Attribute validation
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_validate_attributes_no_attrs() {
    let decls = vec![mk_def("x", vec![])];
    let count = validate_attributes(&decls).expect("should succeed");
    assert_eq!(count, 0);
}

#[test]
fn test_validate_attributes_with_attrs() {
    use clean_parser::Attribute;
    let decl = SurfaceDecl::Def {
        span: span(),
        name: "x".to_string(),
        universe_params: Vec::new(),
        binders: Vec::new(),
        ty: None,
        val: Box::new(SurfaceExpr::Lit(span(), SurfaceLit::Nat(0))),
        attrs: vec![Attribute::Inline, Attribute::Simp { priority: None }],
        termination: Default::default(),
        modifiers: Default::default(),
        where_decls: Vec::new(),
    };
    let count = validate_attributes(&[decl]).expect("should succeed");
    assert_eq!(count, 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 5: Namespace resolution
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_resolve_namespaces_simple() {
    let decls = vec![mk_def("foo", vec!["add"])];
    let opened = vec!["Nat".to_string()];
    let mut known = HashSet::new();
    known.insert("Nat.add".to_string());

    let (resolved, count) = resolve_namespaces(&decls, &opened, &known);
    assert_eq!(count, 1);
    assert_eq!(resolved.len(), 1);
}

#[test]
fn test_resolve_namespaces_no_match() {
    let decls = vec![mk_def("foo", vec!["unknown_fn"])];
    let opened = vec!["Nat".to_string()];
    let known: HashSet<String> = HashSet::new();

    let (_, count) = resolve_namespaces(&decls, &opened, &known);
    assert_eq!(count, 0);
}

#[test]
fn test_resolve_namespaces_already_qualified() {
    let decls = vec![mk_def("foo", vec!["Nat.add"])];
    let opened = vec!["Nat".to_string()];
    let mut known = HashSet::new();
    known.insert("Nat.add".to_string());

    let (_, count) = resolve_namespaces(&decls, &opened, &known);
    // Already qualified, should not be re-resolved.
    assert_eq!(count, 0);
}

#[test]
fn test_resolve_namespaces_theorem() {
    let decls = vec![mk_theorem("thm", "Prop", "rfl")];
    let opened = vec!["Eq".to_string()];
    let mut known = HashSet::new();
    known.insert("Eq.rfl".to_string());

    let (_, count) = resolve_namespaces(&decls, &opened, &known);
    assert_eq!(count, 1); // "rfl" → "Eq.rfl"
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 6: Import expansion
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_expand_imports_none() {
    let decls = vec![mk_def("x", vec![])];
    let opened = expand_imports(&decls);
    assert!(opened.is_empty());
}

#[test]
fn test_expand_imports_single() {
    let decls = vec![mk_open(vec!["Nat"])];
    let opened = expand_imports(&decls);
    assert_eq!(opened, vec!["Nat"]);
}

#[test]
fn test_expand_imports_nested() {
    let decls = vec![mk_open(vec!["Lean", "Data", "List"])];
    let opened = expand_imports(&decls);
    assert_eq!(opened, vec!["Lean.Data.List"]);
}

#[test]
fn test_expand_imports_multiple() {
    let decls = vec![mk_open(vec!["Nat"]), mk_open(vec!["Int"])];
    let opened = expand_imports(&decls);
    assert_eq!(opened, vec!["Nat", "Int"]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 7: Syntax desugaring
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_desugar_example() {
    let decls = vec![mk_example("sorry")];
    let (desugared, count) = desugar_decls(&decls);
    assert_eq!(count, 1);
    assert_eq!(desugared.len(), 1);
    assert!(
        matches!(&desugared[0], SurfaceDecl::Def { name, .. } if name.starts_with("_example_"))
    );
}

#[test]
fn test_desugar_passthrough() {
    let decls = vec![mk_def("x", vec![])];
    let (desugared, count) = desugar_decls(&decls);
    assert_eq!(count, 0);
    assert_eq!(desugared.len(), 1);
    assert!(matches!(&desugared[0], SurfaceDecl::Def { name, .. } if name == "x"));
}

#[test]
fn test_desugar_mixed() {
    let decls = vec![mk_def("a", vec![]), mk_example("b"), mk_def("c", vec![])];
    let (desugared, count) = desugar_decls(&decls);
    assert_eq!(count, 1);
    assert_eq!(desugared.len(), 3);
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 8: Dependency ordering
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_order_by_deps_no_deps() {
    let decls = vec![mk_def("a", vec![]), mk_def("b", vec![])];
    let (ordered, reordered) = order_by_deps(&decls).expect("should succeed");
    assert_eq!(ordered.len(), 2);
    // No reordering needed
    assert_eq!(reordered, 0);
}

#[test]
fn test_order_by_deps_simple_chain() {
    // b depends on a. Original order: b, a. Should become: a, b.
    let decls = vec![mk_def("b", vec!["a"]), mk_def("a", vec![])];
    let (ordered, reordered) = order_by_deps(&decls).expect("should succeed");
    assert_eq!(ordered.len(), 2);
    // "a" should come before "b"
    let names: Vec<_> = ordered.iter().filter_map(|d| decl_name(d)).collect();
    assert_eq!(names[0], "a");
    assert_eq!(names[1], "b");
    assert!(reordered > 0);
}

#[test]
fn test_order_by_deps_cycle_graceful() {
    // a → b → a: cycle. Should not error, cycle nodes appended in order.
    let decls = vec![mk_def("a", vec!["b"]), mk_def("b", vec!["a"])];
    let result = order_by_deps(&decls);
    assert!(result.is_ok());
    let (ordered, _) = result.expect("should succeed");
    assert_eq!(ordered.len(), 2);
}

#[test]
fn test_order_by_deps_single() {
    let decls = vec![mk_def("a", vec![])];
    let (ordered, reordered) = order_by_deps(&decls).expect("should succeed");
    assert_eq!(ordered.len(), 1);
    assert_eq!(reordered, 0);
}

#[test]
fn test_order_by_deps_empty() {
    let (ordered, reordered) = order_by_deps(&[]).expect("should succeed");
    assert!(ordered.is_empty());
    assert_eq!(reordered, 0);
}

#[test]
fn test_order_by_deps_diamond() {
    // d depends on b and c; b and c depend on a.
    let decls = vec![
        mk_def("d", vec!["b", "c"]),
        mk_def("b", vec!["a"]),
        mk_def("c", vec!["a"]),
        mk_def("a", vec![]),
    ];
    let (ordered, _) = order_by_deps(&decls).expect("should succeed");
    let names: Vec<_> = ordered.iter().filter_map(|d| decl_name(d)).collect();
    // "a" must come before "b" and "c"; "b" and "c" before "d"
    let pos_a = names.iter().position(|n| *n == "a").expect("a must exist");
    let pos_b = names.iter().position(|n| *n == "b").expect("b must exist");
    let pos_c = names.iter().position(|n| *n == "c").expect("c must exist");
    let pos_d = names.iter().position(|n| *n == "d").expect("d must exist");
    assert!(pos_a < pos_b);
    assert!(pos_a < pos_c);
    assert!(pos_b < pos_d);
    assert!(pos_c < pos_d);
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 9: Full pipeline
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_pipeline_empty() {
    let known = HashSet::new();
    let result = preprocess_pipeline(&[], &[], &known).expect("should succeed");
    assert!(result.decls.is_empty());
    assert!(result.docstrings.is_empty());
    assert!(result.mutual_groups.is_empty());
    assert!(result.universe_params.is_empty());
    assert_eq!(result.stats.decls_preprocessed, 0);
}

#[test]
fn test_pipeline_basic() {
    let decls = vec![mk_def("foo", vec![])];
    let comments = vec!["/-- doc -/"];
    let known = HashSet::new();
    let result = preprocess_pipeline(&decls, &comments, &known).expect("should succeed");
    assert_eq!(result.decls.len(), 1);
    assert_eq!(result.docstrings.len(), 1);
    assert_eq!(result.stats.decls_preprocessed, 1);
    assert_eq!(result.stats.docstrings_extracted, 1);
}

#[test]
fn test_pipeline_with_mutual() {
    let decls = vec![mk_def("a", vec!["b"]), mk_def("b", vec!["a"])];
    let known = HashSet::new();
    let result = preprocess_pipeline(&decls, &[], &known).expect("should succeed");
    assert_eq!(result.mutual_groups.len(), 1);
    assert_eq!(result.stats.mutual_blocks_found, 1);
}

#[test]
fn test_pipeline_with_universes() {
    let decls = vec![mk_def_with_universes("f", vec!["u", "v"])];
    let known = HashSet::new();
    let result = preprocess_pipeline(&decls, &[], &known).expect("should succeed");
    assert_eq!(result.universe_params.len(), 2);
    assert_eq!(result.stats.universe_params_collected, 2);
}

#[test]
fn test_pipeline_with_desugaring() {
    let decls = vec![mk_example("sorry"), mk_def("a", vec![])];
    let known = HashSet::new();
    let result = preprocess_pipeline(&decls, &[], &known).expect("should succeed");
    assert_eq!(result.stats.desugared, 1);
    assert_eq!(result.decls.len(), 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Step 10: Statistics
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_stats_default() {
    let stats = PreprocessStats::default();
    assert_eq!(stats.decls_preprocessed, 0);
    assert_eq!(stats.mutual_blocks_found, 0);
    assert_eq!(stats.desugared, 0);
    assert_eq!(stats.reordered, 0);
}

#[test]
fn test_stats_populated_by_pipeline() {
    let decls = vec![
        mk_def("b", vec!["a"]),
        mk_def("a", vec![]),
        mk_example("sorry"),
    ];
    let comments = vec!["/-- doc -/"];
    let known = HashSet::new();
    let result = preprocess_pipeline(&decls, &comments, &known).expect("should succeed");
    assert_eq!(result.stats.decls_preprocessed, 3);
    assert_eq!(result.stats.desugared, 1);
    assert_eq!(result.stats.docstrings_extracted, 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper function tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_decl_name_def() {
    let d = mk_def("foo", vec![]);
    assert_eq!(decl_name(&d), Some("foo"));
}

#[test]
fn test_decl_name_theorem() {
    let d = mk_theorem("thm", "Prop", "sorry");
    assert_eq!(decl_name(&d), Some("thm"));
}

#[test]
fn test_decl_name_axiom() {
    let d = mk_axiom("ax", "Nat");
    assert_eq!(decl_name(&d), Some("ax"));
}

#[test]
fn test_decl_name_import() {
    let d = SurfaceDecl::Import {
        span: span(),
        paths: vec![],
    };
    assert_eq!(decl_name(&d), None);
}

#[test]
fn test_decl_name_example() {
    let d = mk_example("sorry");
    assert_eq!(decl_name(&d), None);
}

#[test]
fn test_collect_idents_nested_app() {
    let expr = SurfaceExpr::App(
        span(),
        Box::new(SurfaceExpr::Ident(span(), "f".to_string())),
        vec![SurfaceArg {
            span: span(),
            expr: SurfaceExpr::Ident(span(), "x".to_string()),
            name: None,
        }],
    );
    let mut idents = HashSet::new();
    collect_idents(&expr, &mut idents);
    assert!(idents.contains("f"));
    assert!(idents.contains("x"));
}

#[test]
fn test_collect_idents_arrow() {
    let expr = SurfaceExpr::Arrow(
        span(),
        Box::new(SurfaceExpr::Ident(span(), "A".to_string())),
        Box::new(SurfaceExpr::Ident(span(), "B".to_string())),
    );
    let mut idents = HashSet::new();
    collect_idents(&expr, &mut idents);
    assert!(idents.contains("A"));
    assert!(idents.contains("B"));
}

#[test]
fn test_collect_idents_lambda() {
    let expr = SurfaceExpr::Lambda(
        span(),
        Vec::new(),
        Box::new(SurfaceExpr::Ident(span(), "body".to_string())),
    );
    let mut idents = HashSet::new();
    collect_idents(&expr, &mut idents);
    assert!(idents.contains("body"));
}
