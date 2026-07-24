// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for mutual declaration blocks and dependency graph analysis.

use super::*;
use crate::dep_graph::DependencyGraph;
use clean_kernel::{Expr, Level};

fn mk_entry(name: &str, is_noncomputable: bool) -> MutualEntry {
    MutualEntry {
        name: name.to_string(),
        ty: None,
        body: Expr::sort(Level::zero()),
        is_noncomputable,
    }
}

fn mk_entry_with_body(name: &str, body: Expr) -> MutualEntry {
    MutualEntry {
        name: name.to_string(),
        ty: None,
        body,
        is_noncomputable: false,
    }
}

// ── MutualBlock basic ────────────────────────────────────────────────────────

#[test]
fn test_mutual_block_new_is_empty() {
    let block = MutualBlock::new();
    assert!(block.is_empty());
    assert_eq!(block.len(), 0);
    assert!(block.names().is_empty());
}

#[test]
fn test_mutual_block_add_entry() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("foo", false));
    block.add_entry(mk_entry("bar", false));
    assert_eq!(block.len(), 2);
    assert!(!block.is_empty());
    assert_eq!(block.names(), vec!["foo", "bar"]);
}

#[test]
fn test_mutual_block_well_founded_empty_fails() {
    let block = MutualBlock::new();
    let result = block.check_well_founded();
    assert!(result.is_err());
}

#[test]
fn test_mutual_block_well_founded_single_entry_ok() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("foo", false));
    block.build_dep_graph();
    block
        .check_well_founded()
        .expect("single entry should be well-founded");
}

// ── DependencyGraph ──────────────────────────────────────────────────────────

#[test]
fn test_dep_graph_empty_no_cycle() {
    let graph = DependencyGraph::new();
    assert!(graph.find_cycle(3).is_none());
}

#[test]
fn test_dep_graph_linear_no_cycle() {
    let mut graph = DependencyGraph::new();
    // A -> B -> C (linear chain)
    graph.add_edge(0, 1);
    graph.add_edge(1, 2);
    assert!(graph.find_cycle(3).is_none());
}

#[test]
fn test_dep_graph_simple_cycle() {
    let mut graph = DependencyGraph::new();
    // A -> B -> A (simple cycle)
    graph.add_edge(0, 1);
    graph.add_edge(1, 0);
    let cycle = graph.find_cycle(2);
    assert!(cycle.is_some(), "should detect A <-> B cycle");
    let cycle = cycle.unwrap();
    assert!(cycle.contains(&0) && cycle.contains(&1));
}

#[test]
fn test_dep_graph_self_loop() {
    let mut graph = DependencyGraph::new();
    // A -> A (self-loop)
    graph.add_edge(0, 0);
    let cycle = graph.find_cycle(1);
    assert!(cycle.is_some(), "should detect self-loop");
}

#[test]
fn test_dep_graph_successors() {
    let mut graph = DependencyGraph::new();
    graph.add_edge(0, 1);
    graph.add_edge(0, 2);
    graph.add_edge(1, 2);
    assert_eq!(graph.successors(0).len(), 2);
    assert_eq!(graph.successors(1), vec![2]);
    assert!(graph.successors(2).is_empty());
}

#[test]
fn test_dep_graph_topological_sort_linear() {
    let mut graph = DependencyGraph::new();
    graph.add_edge(0, 1);
    graph.add_edge(1, 2);
    let order = graph.topological_sort(3).expect("should succeed");
    // Node 0 must come before 1, and 1 before 2
    let pos_of = |n: usize| order.iter().position(|&x| x == n).unwrap();
    assert!(pos_of(0) < pos_of(1));
    assert!(pos_of(1) < pos_of(2));
}

#[test]
fn test_dep_graph_topological_sort_cycle_fails() {
    let mut graph = DependencyGraph::new();
    graph.add_edge(0, 1);
    graph.add_edge(1, 0);
    let result = graph.topological_sort(2);
    assert!(result.is_err(), "cycle should produce Err");
}

#[test]
fn test_dep_graph_nontrivial_sccs_none() {
    let mut graph = DependencyGraph::new();
    graph.add_edge(0, 1);
    graph.add_edge(1, 2);
    assert_eq!(graph.num_nontrivial_sccs(3), 0);
}

#[test]
fn test_dep_graph_nontrivial_sccs_one() {
    let mut graph = DependencyGraph::new();
    graph.add_edge(0, 1);
    graph.add_edge(1, 0);
    graph.add_edge(2, 0); // non-cyclic edge from 2
    assert_eq!(graph.num_nontrivial_sccs(3), 1);
}

#[test]
fn test_dep_graph_nontrivial_sccs_two() {
    let mut graph = DependencyGraph::new();
    // SCC 1: {0, 1}
    graph.add_edge(0, 1);
    graph.add_edge(1, 0);
    // SCC 2: {2, 3}
    graph.add_edge(2, 3);
    graph.add_edge(3, 2);
    assert_eq!(graph.num_nontrivial_sccs(4), 2);
}

// ── Well-founded check ───────────────────────────────────────────────────────

#[test]
fn test_well_founded_mutual_recursion_computable_ok() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("even", false));
    block.add_entry(mk_entry("odd", false));
    // even -> odd -> even (mutual recursion, both computable)
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    block
        .check_well_founded()
        .expect("mutual recursion between computable decls is allowed");
}

#[test]
fn test_well_founded_mixed_computable_noncomputable_fails() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f", false)); // computable
    block.add_entry(mk_entry("g", true)); // noncomputable
                                          // f -> g -> f (mixed cycle)
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let result = block.check_well_founded();
    assert!(
        result.is_err(),
        "mixed computable/noncomputable cycle should fail"
    );
}

// ── build_dep_graph via const refs ───────────────────────────────────────────

#[test]
fn test_build_dep_graph_detects_const_refs() {
    let mut block = MutualBlock::new();
    // f references g via a Const expression
    let body_f = Expr::app(Expr::const_str("g"), Expr::nat_lit(42));
    block.add_entry(mk_entry_with_body("f", body_f));
    block.add_entry(mk_entry("g", false));
    block.build_dep_graph();
    assert_eq!(block.dep_graph.successors(0), vec![1]);
    assert!(block.dep_graph.successors(1).is_empty());
}

#[test]
fn test_build_dep_graph_no_self_edge() {
    let mut block = MutualBlock::new();
    // f references itself — build_dep_graph should skip self-edges
    let body_f = Expr::app(Expr::const_str("f"), Expr::nat_lit(0));
    block.add_entry(mk_entry_with_body("f", body_f));
    block.build_dep_graph();
    assert!(
        block.dep_graph.successors(0).is_empty(),
        "self-references should not appear in dep graph"
    );
}

// ── collect_surface_refs ─────────────────────────────────────────────────────

#[test]
fn test_collect_surface_refs_ident() {
    let names = vec!["foo", "bar", "baz"];
    let expr = SurfaceExpr::Ident(clean_parser::Span::dummy(), "bar".to_string());
    let mut refs = HashSet::new();
    collect_surface_refs(&expr, &names, &mut refs);
    assert!(refs.contains(&1));
    assert_eq!(refs.len(), 1);
}

#[test]
fn test_collect_surface_refs_nested_app() {
    let names = vec!["f", "g"];
    let span = clean_parser::Span::dummy();
    let inner = SurfaceExpr::Ident(span, "g".to_string());
    let expr = SurfaceExpr::App(
        span,
        Box::new(SurfaceExpr::Ident(span, "f".to_string())),
        vec![clean_parser::SurfaceArg {
            span,
            expr: inner,
            name: None,
        }],
    );
    let mut refs = HashSet::new();
    collect_surface_refs(&expr, &names, &mut refs);
    assert!(refs.contains(&0)); // f
    assert!(refs.contains(&1)); // g
}

#[test]
fn test_collect_surface_refs_no_match() {
    let names = vec!["foo"];
    let expr = SurfaceExpr::Ident(clean_parser::Span::dummy(), "other".to_string());
    let mut refs = HashSet::new();
    collect_surface_refs(&expr, &names, &mut refs);
    assert!(refs.is_empty());
}
