// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended dependency graph analysis.

use clean_kernel::Name;

use crate::dep_graph_ext::{DepGraphExtConfig, DepNode, ExtDepGraph};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn node(module: &str, decl: &str) -> DepNode {
    DepNode::new(Name::from_string(module), Name::from_string(decl))
}

fn default_config() -> DepGraphExtConfig {
    DepGraphExtConfig::default()
}

// ─────────────────────────────────────────────────────────────────────────────
// Empty / single-node graphs
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_empty_graph_all_nodes_is_empty() {
    let g = ExtDepGraph::new();
    assert!(g.all_nodes().is_empty());
}

#[test]
fn test_empty_graph_schedule_waves_returns_empty() {
    let g = ExtDepGraph::new();
    let waves = g.schedule_waves().expect("empty graph has no cycles");
    assert!(waves.is_empty());
}

#[test]
fn test_empty_graph_no_cycles() {
    let g = ExtDepGraph::new();
    assert!(g.find_cycles().is_empty());
}

#[test]
fn test_single_node_no_edges() {
    let mut g = ExtDepGraph::new();
    g.ensure_node(node("M", "x"));
    assert_eq!(g.all_nodes().len(), 1);
    let waves = g.schedule_waves().expect("single node has no cycles");
    assert_eq!(waves.len(), 1);
    assert_eq!(waves[0].nodes.len(), 1);
}

#[test]
fn test_single_node_self_loop_detected_as_cycle() {
    let mut g = ExtDepGraph::new();
    let n = node("M", "x");
    g.add_dep(n.clone(), n.clone());
    let cycles = g.find_cycles();
    assert_eq!(cycles.len(), 1);
    assert!(cycles[0].message.contains("cycle"));
}

// ─────────────────────────────────────────────────────────────────────────────
// Cross-module dependency tracking
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_cross_module_dep_forward_and_reverse() {
    let mut g = ExtDepGraph::new();
    let a = node("Init", "Nat.add");
    let b = node("Mathlib", "ring_add");
    g.add_dep(b.clone(), a.clone());

    assert!(g.deps_of(&b).contains(&a));
    assert!(g.dependents_of(&a).contains(&b));
}

#[test]
fn test_cross_module_multiple_deps() {
    let mut g = ExtDepGraph::new();
    let a = node("Init", "Nat");
    let b = node("Init", "List");
    let c = node("Mathlib", "theorem1");
    g.add_dep(c.clone(), a.clone());
    g.add_dep(c.clone(), b.clone());

    let deps = g.deps_of(&c);
    assert_eq!(deps.len(), 2);
    assert!(deps.contains(&a));
    assert!(deps.contains(&b));
}

#[test]
fn test_module_import_tracking() {
    let mut g = ExtDepGraph::new();
    let m1 = Name::from_string("Init");
    let m2 = Name::from_string("Mathlib");
    g.add_module_import(m2.clone(), m1.clone());

    let imports = g.module_imports.get(&m2).expect("should have imports");
    assert!(imports.contains(&m1));
}

// ─────────────────────────────────────────────────────────────────────────────
// Incremental recheck
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_recheck_includes_changed_nodes() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    g.ensure_node(a.clone());
    let recheck = g.recheck_set(std::slice::from_ref(&a));
    assert!(recheck.contains(&a));
}

#[test]
fn test_recheck_propagates_to_dependents() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(b.clone(), a.clone()); // b depends on a
    g.add_dep(c.clone(), b.clone()); // c depends on b

    let recheck = g.recheck_set(std::slice::from_ref(&a));
    assert!(recheck.contains(&a));
    assert!(recheck.contains(&b));
    assert!(recheck.contains(&c));
}

#[test]
fn test_recheck_does_not_include_unrelated() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(b.clone(), a.clone());
    g.ensure_node(c.clone());

    let recheck = g.recheck_set(std::slice::from_ref(&a));
    assert!(!recheck.contains(&c));
}

#[test]
fn test_recheck_handles_diamond() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(c.clone(), a.clone());
    g.add_dep(d.clone(), b.clone());
    g.add_dep(d.clone(), c.clone());

    let recheck = g.recheck_set(std::slice::from_ref(&a));
    assert_eq!(recheck.len(), 4);
}

// ─────────────────────────────────────────────────────────────────────────────
// Parallel scheduling
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_schedule_linear_chain() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(c.clone(), b.clone());

    let waves = g.schedule_waves().expect("linear chain is acyclic");
    assert_eq!(waves.len(), 3);
    assert!(waves[0].nodes.contains(&a));
    assert!(waves[1].nodes.contains(&b));
    assert!(waves[2].nodes.contains(&c));
}

#[test]
fn test_schedule_independent_nodes_in_same_wave() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.ensure_node(a.clone());
    g.ensure_node(b.clone());
    g.ensure_node(c.clone());

    let waves = g.schedule_waves().expect("independent nodes are acyclic");
    assert_eq!(waves.len(), 1);
    assert_eq!(waves[0].nodes.len(), 3);
}

#[test]
fn test_schedule_diamond_two_waves() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(c.clone(), a.clone());
    g.add_dep(d.clone(), b.clone());
    g.add_dep(d.clone(), c.clone());

    let waves = g.schedule_waves().expect("diamond is acyclic");
    assert_eq!(waves.len(), 3);
    assert!(waves[0].nodes.contains(&a));
    // b and c should be in the same wave
    assert!(waves[1].nodes.contains(&b));
    assert!(waves[1].nodes.contains(&c));
    assert!(waves[2].nodes.contains(&d));
}

#[test]
fn test_schedule_rejects_cycle() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), a.clone());

    let result = g.schedule_waves();
    assert!(result.is_err());
    let report = result.unwrap_err();
    assert!(report.message.contains("cycle"));
}

// ─────────────────────────────────────────────────────────────────────────────
// Cycle detection and reporting
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_find_cycles_simple_two_node() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), a.clone());

    let cycles = g.find_cycles();
    assert!(!cycles.is_empty());
    assert!(cycles[0].message.contains("cycle"));
}

#[test]
fn test_find_cycles_three_node_ring() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), c.clone());
    g.add_dep(c.clone(), a.clone());

    let cycles = g.find_cycles();
    assert!(!cycles.is_empty());
    let total_nodes: usize = cycles.iter().map(|c| c.cycle.len()).sum();
    assert!(total_nodes >= 3, "cycle should involve all 3 nodes");
}

#[test]
fn test_no_cycles_in_dag() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(c.clone(), b.clone());

    assert!(g.find_cycles().is_empty());
}

#[test]
fn test_cycle_message_readable() {
    let mut g = ExtDepGraph::new();
    let a = node("Init", "Nat.rec");
    let b = node("Init", "Nat.below");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), a.clone());

    let cycles = g.find_cycles();
    assert!(!cycles.is_empty());
    let msg = &cycles[0].message;
    // Message should mention both declarations
    assert!(msg.contains("Nat.rec") || msg.contains("Nat.below"));
}

// ─────────────────────────────────────────────────────────────────────────────
// Transitive closure
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_transitive_deps_linear() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), c.clone());

    let tc = g.transitive_deps(&a, &default_config());
    assert!(tc.contains(&b));
    assert!(tc.contains(&c));
}

#[test]
fn test_transitive_deps_respects_max_depth() {
    let mut g = ExtDepGraph::new();
    // Build a long chain: n0 -> n1 -> ... -> n20
    let nodes: Vec<DepNode> = (0..21).map(|i| node("M", &format!("n{i}"))).collect();
    for i in 0..20 {
        g.add_dep(nodes[i].clone(), nodes[i + 1].clone());
    }

    let config = DepGraphExtConfig {
        max_transitive_depth: 5,
    };
    let tc = g.transitive_deps(&nodes[0], &config);
    // Should reach at most depth 5
    assert!(tc.contains(&nodes[1]));
    assert!(tc.contains(&nodes[5]));
    assert!(!tc.contains(&nodes[10]));
}

#[test]
fn test_transitive_deps_empty_for_leaf() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    g.ensure_node(a.clone());

    let tc = g.transitive_deps(&a, &default_config());
    assert!(tc.is_empty());
}

#[test]
fn test_transitive_deps_diamond() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    let d = node("M", "d");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(a.clone(), c.clone());
    g.add_dep(b.clone(), d.clone());
    g.add_dep(c.clone(), d.clone());

    let tc = g.transitive_deps(&a, &default_config());
    assert_eq!(tc.len(), 3); // b, c, d
}

// ─────────────────────────────────────────────────────────────────────────────
// SCC detection (Tarjan's)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_scc_dag_all_singletons() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(b.clone(), a.clone());

    let sccs = g.compute_sccs();
    assert!(sccs.iter().all(|scc| scc.nodes.len() == 1));
}

#[test]
fn test_scc_cycle_detected() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), a.clone());

    let sccs = g.compute_sccs();
    let nontrivial: Vec<_> = sccs.iter().filter(|s| s.nodes.len() > 1).collect();
    assert_eq!(nontrivial.len(), 1);
    assert_eq!(nontrivial[0].nodes.len(), 2);
}

#[test]
fn test_scc_multiple_components() {
    let mut g = ExtDepGraph::new();
    // Component 1: a <-> b
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(a.clone(), b.clone());
    g.add_dep(b.clone(), a.clone());
    // Component 2: c <-> d
    let c = node("M", "c");
    let d = node("M", "d");
    g.add_dep(c.clone(), d.clone());
    g.add_dep(d.clone(), c.clone());
    // Acyclic link between components
    g.add_dep(a.clone(), c.clone());

    let sccs = g.compute_sccs();
    let nontrivial: Vec<_> = sccs.iter().filter(|s| s.nodes.len() > 1).collect();
    assert_eq!(nontrivial.len(), 2);
}

#[test]
fn test_scc_self_loop_is_singleton_scc() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    g.add_dep(a.clone(), a.clone());

    let sccs = g.compute_sccs();
    assert_eq!(sccs.len(), 1);
    assert_eq!(sccs[0].nodes.len(), 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Serialization round-trip
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_serialize_empty_roundtrip() {
    let g = ExtDepGraph::new();
    let data = g.to_json().expect("serialize empty graph");
    let g2 = ExtDepGraph::from_json(&data).expect("deserialize empty graph");
    assert!(g2.all_nodes().is_empty());
}

#[test]
fn test_serialize_roundtrip_preserves_edges() {
    let mut g = ExtDepGraph::new();
    let a = node("Init", "Nat");
    let b = node("Mathlib", "ring");
    g.add_dep(b.clone(), a.clone());
    g.set_stamp(a.clone(), 100);
    g.set_stamp(b.clone(), 200);
    g.add_module_import(Name::from_string("Mathlib"), Name::from_string("Init"));

    let data = g.to_json().expect("serialize");
    let g2 = ExtDepGraph::from_json(&data).expect("deserialize");

    assert!(g2.deps_of(&b).contains(&a));
    assert!(g2.dependents_of(&a).contains(&b));
    assert_eq!(g2.stamps.get(&a), Some(&100));
    assert_eq!(g2.stamps.get(&b), Some(&200));
    let imports = g2.module_imports.get(&Name::from_string("Mathlib"));
    assert!(imports.is_some());
    assert!(imports.unwrap().contains(&Name::from_string("Init")));
}

#[test]
fn test_serialize_roundtrip_preserves_graph_structure() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    let c = node("M", "c");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(c.clone(), a.clone());
    g.add_dep(c.clone(), b.clone());

    let data = g.to_json().expect("serialize");
    let g2 = ExtDepGraph::from_json(&data).expect("deserialize");

    assert_eq!(g2.deps_of(&c).len(), 2);
    assert_eq!(g2.dependents_of(&a).len(), 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Stale dependency detection
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_stale_none_when_stamps_equal() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(b.clone(), a.clone());
    g.set_stamp(a.clone(), 100);
    g.set_stamp(b.clone(), 100);

    assert!(g.stale_nodes().is_empty());
}

#[test]
fn test_stale_detected_when_dep_newer() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(b.clone(), a.clone());
    g.set_stamp(a.clone(), 200);
    g.set_stamp(b.clone(), 100);

    let stale = g.stale_nodes();
    assert!(stale.contains(&b));
    assert!(!stale.contains(&a));
}

#[test]
fn test_stale_not_detected_when_dep_older() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(b.clone(), a.clone());
    g.set_stamp(a.clone(), 50);
    g.set_stamp(b.clone(), 100);

    assert!(g.stale_nodes().is_empty());
}

#[test]
fn test_stale_missing_stamp_treated_as_zero() {
    let mut g = ExtDepGraph::new();
    let a = node("M", "a");
    let b = node("M", "b");
    g.add_dep(b.clone(), a.clone());
    g.set_stamp(a.clone(), 1);
    // b has no stamp (implicit 0)

    let stale = g.stale_nodes();
    assert!(stale.contains(&b));
}

// ─────────────────────────────────────────────────────────────────────────────
// Disconnected graph
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn test_disconnected_components_schedule_independently() {
    let mut g = ExtDepGraph::new();
    let a = node("M1", "a");
    let b = node("M1", "b");
    let c = node("M2", "c");
    let d = node("M2", "d");
    g.add_dep(b.clone(), a.clone());
    g.add_dep(d.clone(), c.clone());

    let waves = g.schedule_waves().expect("disconnected DAG has no cycles");
    // Wave 0: a, c (both are roots); Wave 1: b, d
    assert_eq!(waves.len(), 2);
    assert_eq!(waves[0].nodes.len(), 2);
    assert_eq!(waves[1].nodes.len(), 2);
}

#[test]
fn test_disconnected_recheck_only_affected_component() {
    let mut g = ExtDepGraph::new();
    let a = node("M1", "a");
    let b = node("M1", "b");
    let c = node("M2", "c");
    g.add_dep(b.clone(), a.clone());
    g.ensure_node(c.clone());

    let recheck = g.recheck_set(std::slice::from_ref(&a));
    assert!(recheck.contains(&a));
    assert!(recheck.contains(&b));
    assert!(!recheck.contains(&c));
}
