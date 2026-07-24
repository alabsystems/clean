// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for dep_graph_ext2: transitive closure, critical path, parallelism,
//! graph metrics, subgraph extraction, layered scheduling, and impact analysis.

use clean_kernel::Name;

use crate::dep_graph_ext::{DepNode, ExtDepGraph};
use crate::dep_graph_ext2::{DepGraphExt2Error, Ext2Config};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn node(module: &str, decl: &str) -> DepNode {
    DepNode::new(Name::from_string(module), Name::from_string(decl))
}

fn cfg() -> Ext2Config {
    Ext2Config::default()
}

/// Build a linear chain: n0 -> n1 -> n2 -> ... -> n(len-1).
fn linear_chain(len: usize) -> (ExtDepGraph, Vec<DepNode>) {
    let mut g = ExtDepGraph::new();
    let nodes: Vec<DepNode> = (0..len).map(|i| node("M", &format!("n{i}"))).collect();
    for i in 0..(len - 1) {
        g.add_dep(nodes[i].clone(), nodes[i + 1].clone());
    }
    (g, nodes)
}

/// Build a diamond: a -> b, a -> c, b -> d, c -> d.
fn diamond() -> (ExtDepGraph, DepNode, DepNode, DepNode, DepNode) {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(a.clone(), c.clone());
    g.add_dep(b.clone(), d.clone());
    g.add_dep(c.clone(), d.clone());
    (g, a, b, c, d)
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitive closure tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_transitive_closure_empty_graph_node_not_found() {
    let g = ExtDepGraph::new();
    let n = node("M", "x");
    let result = g.transitive_closure(&n, &cfg());
    assert!(matches!(result, Err(DepGraphExt2Error::NodeNotFound(_))));
}

#[test]
fn test_transitive_closure_single_node_no_deps() {
    let mut g = ExtDepGraph::new();
    let n = node("M", "x");
    g.ensure_node(n.clone());
    let result = g.transitive_closure(&n, &cfg()).unwrap();
    assert!(result.is_empty());
}

#[test]
fn test_transitive_closure_linear_chain() {
    let (g, nodes) = linear_chain(4);
    // n0 -> n1 -> n2 -> n3
    let tc = g.transitive_closure(&nodes[0], &cfg()).unwrap();
    assert_eq!(tc.len(), 3);
    assert!(tc.contains(&nodes[1]));
    assert!(tc.contains(&nodes[2]));
    assert!(tc.contains(&nodes[3]));
}

#[test]
fn test_transitive_closure_middle_node() {
    let (g, nodes) = linear_chain(4);
    let tc = g.transitive_closure(&nodes[1], &cfg()).unwrap();
    assert_eq!(tc.len(), 2);
    assert!(tc.contains(&nodes[2]));
    assert!(tc.contains(&nodes[3]));
    assert!(!tc.contains(&nodes[0]));
}

#[test]
fn test_transitive_closure_leaf_node() {
    let (g, nodes) = linear_chain(3);
    let tc = g.transitive_closure(&nodes[2], &cfg()).unwrap();
    assert!(tc.is_empty());
}

#[test]
fn test_transitive_closure_diamond() {
    let (g, a, b, c, d) = diamond();
    let tc = g.transitive_closure(&a, &cfg()).unwrap();
    assert_eq!(tc.len(), 3);
    assert!(tc.contains(&b));
    assert!(tc.contains(&c));
    assert!(tc.contains(&d));
}

#[test]
fn test_transitive_closure_depth_limit() {
    let (g, nodes) = linear_chain(5);
    let short_cfg = Ext2Config { max_depth: 2 };
    let result = g.transitive_closure(&nodes[0], &short_cfg);
    assert!(matches!(
        result,
        Err(DepGraphExt2Error::DepthLimitExceeded(2))
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitive dependents tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_transitive_dependents_leaf_has_ancestors() {
    let (g, nodes) = linear_chain(4);
    // reverse: who depends on n3?
    let td = g.transitive_dependents(&nodes[3], &cfg()).unwrap();
    assert_eq!(td.len(), 3);
    assert!(td.contains(&nodes[0]));
    assert!(td.contains(&nodes[1]));
    assert!(td.contains(&nodes[2]));
}

#[test]
fn test_transitive_dependents_root_has_none() {
    let (g, nodes) = linear_chain(3);
    let td = g.transitive_dependents(&nodes[0], &cfg()).unwrap();
    assert!(td.is_empty());
}

#[test]
fn test_transitive_dependents_diamond() {
    let (g, a, b, _c, d) = diamond();
    let td = g.transitive_dependents(&d, &cfg()).unwrap();
    assert_eq!(td.len(), 3); // a, b, c
    assert!(td.contains(&a));
    assert!(td.contains(&b));
}

// ─────────────────────────────────────────────────────────────────────────────
// Critical path tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_critical_path_empty_graph() {
    let g = ExtDepGraph::new();
    let cp = g.critical_path().unwrap();
    assert!(cp.path.is_empty());
    assert_eq!(cp.length, 0);
}

#[test]
fn test_critical_path_single_node() {
    let mut g = ExtDepGraph::new();
    g.ensure_node(node("M", "x"));
    let cp = g.critical_path().unwrap();
    assert_eq!(cp.path.len(), 1);
    assert_eq!(cp.length, 0);
}

#[test]
fn test_critical_path_linear_chain() {
    let (g, nodes) = linear_chain(4);
    let cp = g.critical_path().unwrap();
    assert_eq!(cp.length, 3);
    assert_eq!(cp.path.len(), 4);
    // The path should traverse the chain
    assert_eq!(cp.path[0], nodes[0]);
    assert_eq!(cp.path[3], nodes[3]);
}

#[test]
fn test_critical_path_diamond_length_is_two() {
    let (g, _a, _b, _c, _d) = diamond();
    let cp = g.critical_path().unwrap();
    // diamond has paths of length 2 (a->b->d or a->c->d)
    assert_eq!(cp.length, 2);
    assert_eq!(cp.path.len(), 3);
}

#[test]
fn test_critical_path_cycle_returns_error() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b, a);
    let result = g.critical_path();
    assert!(matches!(result, Err(DepGraphExt2Error::CycleDetected(_))));
}

// ─────────────────────────────────────────────────────────────────────────────
// Parallelism estimation tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_max_parallelism_empty() {
    let g = ExtDepGraph::new();
    assert_eq!(g.max_parallelism().unwrap(), 0);
}

#[test]
fn test_max_parallelism_independent_nodes() {
    let mut g = ExtDepGraph::new();
    for i in 0..5 {
        g.ensure_node(node("M", &format!("n{i}")));
    }
    assert_eq!(g.max_parallelism().unwrap(), 5);
}

#[test]
fn test_max_parallelism_linear_chain() {
    let (g, _) = linear_chain(4);
    assert_eq!(g.max_parallelism().unwrap(), 1);
}

#[test]
fn test_max_parallelism_diamond() {
    let (g, _, _, _, _) = diamond();
    // diamond: layer 0={d}, layer 1={b,c}, layer 2={a} => max=2
    assert_eq!(g.max_parallelism().unwrap(), 2);
}

#[test]
fn test_serialization_ratio_linear_chain() {
    let (g, _) = linear_chain(4);
    let ratio = g.serialization_ratio().unwrap();
    // chain of 4: critical path covers all 4 nodes => ratio = 1.0
    assert!((ratio - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_serialization_ratio_independent_nodes() {
    let mut g = ExtDepGraph::new();
    for i in 0..4 {
        g.ensure_node(node("M", &format!("n{i}")));
    }
    let ratio = g.serialization_ratio().unwrap();
    // 1 node in critical path / 4 total = 0.25
    assert!((ratio - 0.25).abs() < f64::EPSILON);
}

// ─────────────────────────────────────────────────────────────────────────────
// Graph metrics tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_metrics_empty_graph() {
    let g = ExtDepGraph::new();
    let m = g.graph_metrics();
    assert_eq!(m.node_count, 0);
    assert_eq!(m.edge_count, 0);
    assert_eq!(m.density, 0.0);
}

#[test]
fn test_metrics_single_node() {
    let mut g = ExtDepGraph::new();
    g.ensure_node(node("M", "x"));
    let m = g.graph_metrics();
    assert_eq!(m.node_count, 1);
    assert_eq!(m.edge_count, 0);
    assert_eq!(m.density, 0.0);
    assert_eq!(m.max_out_degree, 0);
}

#[test]
fn test_metrics_linear_chain() {
    let (g, _) = linear_chain(3);
    let m = g.graph_metrics();
    assert_eq!(m.node_count, 3);
    assert_eq!(m.edge_count, 2);
    assert!((m.avg_out_degree - 2.0 / 3.0).abs() < 1e-10);
    assert_eq!(m.max_out_degree, 1);
}

#[test]
fn test_metrics_diamond_density() {
    let (g, _, _, _, _) = diamond();
    let m = g.graph_metrics();
    assert_eq!(m.node_count, 4);
    assert_eq!(m.edge_count, 4);
    // density = 4 / (4*3) = 1/3
    assert!((m.density - 1.0 / 3.0).abs() < 1e-10);
}

#[test]
fn test_metrics_diamond_clustering() {
    let (g, _, _, _, _) = diamond();
    let m = g.graph_metrics();
    // clustering should be > 0 because b and c share neighbors a and d
    assert!(m.avg_clustering_coefficient >= 0.0);
}

#[test]
fn test_metrics_complete_graph_high_density() {
    // 3-node complete DAG: a->b, a->c, b->c
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(a, c.clone());
    g.add_dep(b, c);
    let m = g.graph_metrics();
    assert_eq!(m.edge_count, 3);
    // density = 3 / (3*2) = 0.5
    assert!((m.density - 0.5).abs() < 1e-10);
}

// ─────────────────────────────────────────────────────────────────────────────
// Subgraph extraction tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_subgraph_from_empty_roots() {
    let (g, _) = linear_chain(3);
    let sub = g.subgraph_from_roots(&[]);
    assert!(sub.all_nodes().is_empty());
}

#[test]
fn test_subgraph_from_single_leaf() {
    let (g, nodes) = linear_chain(3);
    let sub = g.subgraph_from_roots(&[nodes[2].clone()]);
    assert_eq!(sub.all_nodes().len(), 1);
}

#[test]
fn test_subgraph_from_root_includes_all() {
    let (g, nodes) = linear_chain(3);
    let sub = g.subgraph_from_roots(&[nodes[0].clone()]);
    assert_eq!(sub.all_nodes().len(), 3);
}

#[test]
fn test_subgraph_from_middle_includes_downstream() {
    let (g, nodes) = linear_chain(4);
    let sub = g.subgraph_from_roots(&[nodes[1].clone()]);
    assert_eq!(sub.all_nodes().len(), 3); // n1, n2, n3
    assert!(!sub.all_nodes().contains(&nodes[0]));
}

#[test]
fn test_subgraph_preserves_edges() {
    let (g, a, b, c, d) = diamond();
    let sub = g.subgraph_from_roots(std::slice::from_ref(&a));
    assert_eq!(sub.all_nodes().len(), 4);
    assert!(sub.deps_of(&a).contains(&b));
    assert!(sub.deps_of(&a).contains(&c));
    assert!(sub.deps_of(&b).contains(&d));
    assert!(sub.deps_of(&c).contains(&d));
}

#[test]
fn test_subgraph_reverse_from_leaf() {
    let (g, nodes) = linear_chain(4);
    // reverse from n3 should include all nodes (everyone depends transitively)
    let sub = g.subgraph_from_roots_reverse(&[nodes[3].clone()]);
    assert_eq!(sub.all_nodes().len(), 4);
}

#[test]
fn test_subgraph_reverse_from_root_only_self() {
    let (g, nodes) = linear_chain(4);
    let sub = g.subgraph_from_roots_reverse(&[nodes[0].clone()]);
    assert_eq!(sub.all_nodes().len(), 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Layered scheduling tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_layered_schedule_empty() {
    let g = ExtDepGraph::new();
    let layers = g.layered_schedule().unwrap();
    assert!(layers.is_empty());
}

#[test]
fn test_layered_schedule_single_node() {
    let mut g = ExtDepGraph::new();
    g.ensure_node(node("M", "x"));
    let layers = g.layered_schedule().unwrap();
    assert_eq!(layers.len(), 1);
    assert_eq!(layers[0].depth, 0);
}

#[test]
fn test_layered_schedule_linear_chain() {
    let (g, nodes) = linear_chain(3);
    let layers = g.layered_schedule().unwrap();
    assert_eq!(layers.len(), 3);
    // Layer 0 should be the leaf (n2), layer 2 the root (n0)
    assert!(layers[0].nodes.contains(&nodes[2]));
    assert!(layers[2].nodes.contains(&nodes[0]));
}

#[test]
fn test_layered_schedule_diamond() {
    let (g, a, b, c, d) = diamond();
    let layers = g.layered_schedule().unwrap();
    assert_eq!(layers.len(), 3);
    // Layer 0: d (no deps)
    assert!(layers[0].nodes.contains(&d));
    // Layer 1: b and c (both depend only on d)
    assert_eq!(layers[1].nodes.len(), 2);
    assert!(layers[1].nodes.contains(&b));
    assert!(layers[1].nodes.contains(&c));
    // Layer 2: a (depends on b and c)
    assert!(layers[2].nodes.contains(&a));
}

#[test]
fn test_layered_schedule_cycle_returns_error() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b, a);
    let result = g.layered_schedule();
    assert!(matches!(result, Err(DepGraphExt2Error::CycleDetected(_))));
}

#[test]
fn test_node_layer_map_diamond() {
    let (g, a, b, c, d) = diamond();
    let map = g.node_layer_map().unwrap();
    assert_eq!(map[&d], 0);
    assert_eq!(map[&b], 1);
    assert_eq!(map[&c], 1);
    assert_eq!(map[&a], 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Impact analysis tests
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_impact_set_empty_changed() {
    let (g, _) = linear_chain(3);
    let impact = g.impact_set(&[], &cfg()).unwrap();
    assert!(impact.is_empty());
}

#[test]
fn test_impact_set_leaf_change_no_downstream() {
    let (g, nodes) = linear_chain(3);
    let impact = g.impact_set(&[nodes[0].clone()], &cfg()).unwrap();
    // n0 is the root: nothing depends on it
    assert!(impact.is_empty());
}

#[test]
fn test_impact_set_root_dep_change_affects_all_upstream() {
    let (g, nodes) = linear_chain(3);
    // n2 is the leaf: n0 and n1 depend on it
    let impact = g.impact_set(&[nodes[2].clone()], &cfg()).unwrap();
    assert_eq!(impact.len(), 2);
    assert!(impact.contains(&nodes[0]));
    assert!(impact.contains(&nodes[1]));
}

#[test]
fn test_impact_set_diamond_change_d_affects_all() {
    let (g, a, b, c, d) = diamond();
    let impact = g.impact_set(&[d], &cfg()).unwrap();
    assert_eq!(impact.len(), 3);
    assert!(impact.contains(&a));
    assert!(impact.contains(&b));
    assert!(impact.contains(&c));
}

#[test]
fn test_impact_set_unknown_node_skipped() {
    let (g, _) = linear_chain(3);
    let unknown = node("X", "unknown");
    let impact = g.impact_set(&[unknown], &cfg()).unwrap();
    assert!(impact.is_empty());
}

#[test]
fn test_impact_score_leaf_node() {
    let (g, nodes) = linear_chain(3);
    // n2 is depended on by n0 and n1
    let score = g.impact_score(&nodes[2], &cfg()).unwrap();
    assert_eq!(score, 2);
}

#[test]
fn test_impact_score_root_node() {
    let (g, nodes) = linear_chain(3);
    let score = g.impact_score(&nodes[0], &cfg()).unwrap();
    assert_eq!(score, 0);
}

#[test]
fn test_impact_ranking_order() {
    let (g, nodes) = linear_chain(3);
    let ranking = g.impact_ranking(&cfg()).unwrap();
    // n2 has highest impact (2), n1 has 1, n0 has 0
    assert_eq!(ranking[0].0, nodes[2]);
    assert_eq!(ranking[0].1, 2);
    assert_eq!(ranking[1].0, nodes[1]);
    assert_eq!(ranking[1].1, 1);
    assert_eq!(ranking[2].0, nodes[0]);
    assert_eq!(ranking[2].1, 0);
}

#[test]
fn test_impact_ranking_diamond() {
    let (g, _a, _b, _c, d) = diamond();
    let ranking = g.impact_ranking(&cfg()).unwrap();
    // d has the highest impact (a, b, c all depend on it)
    assert_eq!(ranking[0].0, d);
    assert_eq!(ranking[0].1, 3);
}

// ─────────────────────────────────────────────────────────────────────────────
// Integration: combined operations
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_subgraph_then_critical_path() {
    // Build a wider graph, extract subgraph, then find critical path
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    let e = node("M", "e"); // disconnected branch
    let f = node("M", "f");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), c.clone());
    g.add_dep(d.clone(), e.clone());
    g.add_dep(e.clone(), f.clone());

    let sub = g.subgraph_from_roots(std::slice::from_ref(&a));
    assert_eq!(sub.all_nodes().len(), 3); // a, b, c only
    let cp = sub.critical_path().unwrap();
    assert_eq!(cp.length, 2);
}

#[test]
fn test_layered_schedule_wide_graph() {
    // a -> d, b -> d, c -> d, e (independent)
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    let e = node("M", "e");
    g.add_dep(a, d.clone());
    g.add_dep(b, d.clone());
    g.add_dep(c, d);
    g.ensure_node(e);

    let layers = g.layered_schedule().unwrap();
    // Layer 0: d and e (no deps), Layer 1: a, b, c
    assert_eq!(layers.len(), 2);
    assert!(layers[0].nodes.len() >= 2); // d and e
    assert_eq!(layers[1].nodes.len(), 3); // a, b, c
}
