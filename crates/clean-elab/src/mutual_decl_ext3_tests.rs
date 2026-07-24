// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for phase-3 extended mutual declaration analysis: cycle
//! classification, elaboration ordering, type dependency tracking,
//! stratification, size estimation, signature analysis, and DOT
//! visualization.

use super::mutual_decl_ext3::*;
use crate::mutual_decl::{MutualBlock, MutualEntry};
use clean_kernel::{BinderInfo, Expr, Level};

// ─── Helpers ────────────────────────────────────────────────────────────────

fn mk_entry(name: &str) -> MutualEntry {
    MutualEntry {
        name: name.to_string(),
        ty: None,
        body: Expr::sort(Level::zero()),
        is_noncomputable: false,
    }
}

fn mk_entry_noncomp(name: &str) -> MutualEntry {
    MutualEntry {
        name: name.to_string(),
        ty: None,
        body: Expr::sort(Level::zero()),
        is_noncomputable: true,
    }
}

fn mk_entry_with_type(name: &str, ty: Expr) -> MutualEntry {
    MutualEntry {
        name: name.to_string(),
        ty: Some(ty),
        body: Expr::sort(Level::zero()),
        is_noncomputable: false,
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

fn mk_pi_type(depth: usize) -> Expr {
    let mut ty = Expr::sort(Level::zero());
    for _ in 0..depth {
        ty = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), ty);
    }
    ty
}

fn default_config() -> MutualDeclExt3Config {
    MutualDeclExt3Config::default()
}

// ─── Config ─────────────────────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let config = MutualDeclExt3Config::default();
    assert_eq!(config.max_declarations, 128);
    assert_eq!(config.max_cycle_report_len, 32);
    assert_eq!(config.size_warning_threshold, 10_000);
}

#[test]
fn test_config_custom_values() {
    let config = MutualDeclExt3Config {
        max_declarations: 64,
        max_cycle_report_len: 16,
        size_warning_threshold: 500,
    };
    assert_eq!(config.max_declarations, 64);
    assert_eq!(config.max_cycle_report_len, 16);
    assert_eq!(config.size_warning_threshold, 500);
}

// ─── Cycle analysis ─────────────────────────────────────────────────────────

#[test]
fn test_find_cycles_empty_block() {
    let block = MutualBlock::new();
    let cycles = find_cycles(&block);
    assert!(cycles.is_empty());
}

#[test]
fn test_find_cycles_no_cycles() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.dep_graph.add_edge(0, 1);
    let cycles = find_cycles(&block);
    assert!(cycles.is_empty());
}

#[test]
fn test_find_cycles_self_loop() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.dep_graph.add_edge(0, 0);
    let cycles = find_cycles(&block);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].kind, CycleKind::SelfLoop);
    assert_eq!(cycles[0].names, vec!["f"]);
}

#[test]
fn test_find_cycles_binary_cycle() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("even"));
    block.add_entry(mk_entry("odd"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let cycles = find_cycles(&block);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].kind, CycleKind::Binary);
    assert_eq!(cycles[0].indices.len(), 2);
}

#[test]
fn test_find_cycles_complex_three_way() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    block.dep_graph.add_edge(2, 0);
    let cycles = find_cycles(&block);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].kind, CycleKind::Complex { len: 3 });
}

#[test]
fn test_find_cycles_two_independent_cycles() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    block.add_entry(mk_entry("d"));
    // a <-> b
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    // c <-> d
    block.dep_graph.add_edge(2, 3);
    block.dep_graph.add_edge(3, 2);
    let cycles = find_cycles(&block);
    assert_eq!(cycles.len(), 2);
    assert!(cycles.iter().all(|c| c.kind == CycleKind::Binary));
}

#[test]
fn test_find_cycles_mixed_cyclic_and_acyclic() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.add_entry(mk_entry("h"));
    // f <-> g cycle, h depends on f (no cycle)
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    block.dep_graph.add_edge(2, 0);
    let cycles = find_cycles(&block);
    assert_eq!(cycles.len(), 1);
    assert_eq!(cycles[0].kind, CycleKind::Binary);
}

// ─── Elaboration ordering ───────────────────────────────────────────────────

#[test]
fn test_elaboration_order_empty() {
    let block = MutualBlock::new();
    let order = compute_elaboration_order(&block).unwrap();
    assert!(order.is_empty());
}

#[test]
fn test_elaboration_order_single() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let order = compute_elaboration_order(&block).unwrap();
    assert_eq!(order, vec![0]);
}

#[test]
fn test_elaboration_order_deps_first() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a -> b -> c
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    let order = compute_elaboration_order(&block).unwrap();
    let pos_a = order.iter().position(|&x| x == 0).unwrap();
    let pos_b = order.iter().position(|&x| x == 1).unwrap();
    let pos_c = order.iter().position(|&x| x == 2).unwrap();
    assert!(pos_c < pos_b);
    assert!(pos_b < pos_a);
}

#[test]
fn test_elaboration_order_cycle_grouped() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    // f <-> g
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let order = compute_elaboration_order(&block).unwrap();
    assert_eq!(order.len(), 2);
}

// ─── Forward reference counting ─────────────────────────────────────────────

#[test]
fn test_forward_refs_none_in_optimal_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    // a -> b
    block.dep_graph.add_edge(0, 1);
    // Optimal order: b first, then a
    let count = count_forward_refs(&block, &[1, 0]);
    assert_eq!(count, 0);
}

#[test]
fn test_forward_refs_one_in_reverse_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    // a -> b
    block.dep_graph.add_edge(0, 1);
    // Reverse order: a first (references b which comes later)
    let count = count_forward_refs(&block, &[0, 1]);
    assert_eq!(count, 1);
}

#[test]
fn test_forward_refs_empty() {
    let block = MutualBlock::new();
    let count = count_forward_refs(&block, &[]);
    assert_eq!(count, 0);
}

#[test]
fn test_forward_refs_no_edges() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.build_dep_graph();
    let count = count_forward_refs(&block, &[0, 1]);
    assert_eq!(count, 0);
}

// ─── Type dependency tracking ───────────────────────────────────────────────

#[test]
fn test_type_deps_empty_block() {
    let block = MutualBlock::new();
    let deps = collect_type_dependencies(&block);
    assert!(deps.is_empty());
}

#[test]
fn test_type_deps_no_refs() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let deps = collect_type_dependencies(&block);
    assert_eq!(deps.len(), 1);
    assert_eq!(deps[0].decl_name, "f");
    assert!(deps[0].type_refs.is_empty());
}

#[test]
fn test_type_deps_body_const_ref() {
    let mut block = MutualBlock::new();
    let body = Expr::app(Expr::const_str("Nat.add"), Expr::bvar(0));
    block.add_entry(mk_entry_with_body("f", body));
    let deps = collect_type_dependencies(&block);
    assert_eq!(deps[0].body_refs, vec!["Nat.add"]);
}

#[test]
fn test_type_deps_type_ref() {
    let mut block = MutualBlock::new();
    let ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::sort(Level::zero()),
    );
    block.add_entry(mk_entry_with_type("f", ty));
    let deps = collect_type_dependencies(&block);
    assert!(deps[0].type_refs.contains(&"Nat".to_string()));
}

#[test]
fn test_type_deps_preserves_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("alpha"));
    block.add_entry(mk_entry("beta"));
    let deps = collect_type_dependencies(&block);
    assert_eq!(deps[0].decl_index, 0);
    assert_eq!(deps[0].decl_name, "alpha");
    assert_eq!(deps[1].decl_index, 1);
    assert_eq!(deps[1].decl_name, "beta");
}

// ─── Stratification analysis ────────────────────────────────────────────────

#[test]
fn test_stratification_empty() {
    let block = MutualBlock::new();
    let result = analyze_stratification(&block);
    assert!(result.is_stratifiable);
    assert_eq!(result.num_components, 0);
    assert!(result.layers.is_empty());
}

#[test]
fn test_stratification_single_decl() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let result = analyze_stratification(&block);
    assert!(!result.is_stratifiable); // 1 component is not "split"
    assert_eq!(result.num_components, 1);
}

#[test]
fn test_stratification_two_independent() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.build_dep_graph();
    let result = analyze_stratification(&block);
    assert!(result.is_stratifiable);
    assert_eq!(result.num_components, 2);
    assert_eq!(result.layers.len(), 2);
}

#[test]
fn test_stratification_connected_pair() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    let result = analyze_stratification(&block);
    assert!(!result.is_stratifiable);
    assert_eq!(result.num_components, 1);
    assert_eq!(result.layers[0].decl_indices.len(), 2);
}

#[test]
fn test_stratification_three_with_two_components() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a -> b, c is independent
    block.dep_graph.add_edge(0, 1);
    let result = analyze_stratification(&block);
    assert!(result.is_stratifiable);
    assert_eq!(result.num_components, 2);
}

#[test]
fn test_stratification_layer_names_populated() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("alpha"));
    block.add_entry(mk_entry("beta"));
    block.build_dep_graph();
    let result = analyze_stratification(&block);
    for layer in &result.layers {
        assert!(!layer.decl_names.is_empty());
        for name in &layer.decl_names {
            assert!(name == "alpha" || name == "beta");
        }
    }
}

// ─── Size estimation ────────────────────────────────────────────────────────

#[test]
fn test_size_estimate_empty() {
    let block = MutualBlock::new();
    let est = estimate_block_size(&block, &default_config());
    assert_eq!(est.total_nodes, 0);
    assert!(!est.exceeds_threshold);
}

#[test]
fn test_size_estimate_single_sort_body() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let est = estimate_block_size(&block, &default_config());
    // Sort(0) = 1 node
    assert_eq!(est.declarations[0].body_nodes, 1);
    assert_eq!(est.declarations[0].type_nodes, 0);
    assert_eq!(est.total_nodes, 1);
}

#[test]
fn test_size_estimate_app_body() {
    let mut block = MutualBlock::new();
    let body = Expr::app(Expr::const_str("f"), Expr::bvar(0));
    block.add_entry(mk_entry_with_body("g", body));
    let est = estimate_block_size(&block, &default_config());
    // app(const, bvar) = 1 + 1 + 1 = 3 nodes
    assert_eq!(est.declarations[0].body_nodes, 3);
}

#[test]
fn test_size_estimate_with_type() {
    let mut block = MutualBlock::new();
    let ty = mk_pi_type(2);
    block.add_entry(mk_entry_with_type("f", ty));
    let est = estimate_block_size(&block, &default_config());
    // Pi(Sort, Pi(Sort, Sort)) = 1+1 + 1+1+1 = 5
    assert!(est.declarations[0].type_nodes > 0);
    assert!(est.declarations[0].total > est.declarations[0].body_nodes);
}

#[test]
fn test_size_estimate_threshold_exceeded() {
    let config = MutualDeclExt3Config {
        size_warning_threshold: 0,
        ..default_config()
    };
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let est = estimate_block_size(&block, &config);
    assert!(est.exceeds_threshold);
}

#[test]
fn test_size_estimate_multiple_decls() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    let est = estimate_block_size(&block, &default_config());
    assert_eq!(est.declarations.len(), 3);
    assert_eq!(est.total_nodes, 3); // 3 Sort nodes
}

// ─── Signature analysis ─────────────────────────────────────────────────────

#[test]
fn test_signature_analysis_empty() {
    let block = MutualBlock::new();
    let result = analyze_signatures(&block);
    assert!(result.signatures.is_empty());
    assert!(result.uniform_arity);
    assert_eq!(result.missing_type_count, 0);
}

#[test]
fn test_signature_analysis_all_untyped() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    let result = analyze_signatures(&block);
    assert_eq!(result.missing_type_count, 2);
    assert!(result.uniform_arity); // vacuously true
}

#[test]
fn test_signature_analysis_uniform_arity() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_with_type("f", mk_pi_type(2)));
    block.add_entry(mk_entry_with_type("g", mk_pi_type(2)));
    let result = analyze_signatures(&block);
    assert!(result.uniform_arity);
    assert_eq!(result.missing_type_count, 0);
}

#[test]
fn test_signature_analysis_non_uniform_arity() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_with_type("f", mk_pi_type(1)));
    block.add_entry(mk_entry_with_type("g", mk_pi_type(3)));
    let result = analyze_signatures(&block);
    assert!(!result.uniform_arity);
}

#[test]
fn test_signature_analysis_mixed_typed_untyped() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_with_type("f", mk_pi_type(2)));
    block.add_entry(mk_entry("g"));
    let result = analyze_signatures(&block);
    assert_eq!(result.missing_type_count, 1);
    assert!(result.uniform_arity); // only one typed, so uniform
}

#[test]
fn test_signature_analysis_return_sort_level() {
    let mut block = MutualBlock::new();
    // Pi(Sort(0), Sort(0)) => return sort level = 0
    block.add_entry(mk_entry_with_type("f", mk_pi_type(1)));
    let result = analyze_signatures(&block);
    assert_eq!(result.signatures[0].return_sort_level, Some(0));
}

#[test]
fn test_signature_analysis_param_count() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_with_type("f", mk_pi_type(4)));
    let result = analyze_signatures(&block);
    assert_eq!(result.signatures[0].num_params, 4);
}

// ─── DOT visualization ──────────────────────────────────────────────────────

#[test]
fn test_dot_empty() {
    let block = MutualBlock::new();
    let dot = to_dot(&block);
    assert!(dot.contains("digraph mutual_decls"));
    assert!(dot.contains('}'));
}

#[test]
fn test_dot_single_node() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let dot = to_dot(&block);
    assert!(dot.contains("n0"));
    assert!(dot.contains("\"f\""));
    assert!(dot.contains("ellipse"));
}

#[test]
fn test_dot_noncomputable_box_shape() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_noncomp("f"));
    block.build_dep_graph();
    let dot = to_dot(&block);
    assert!(dot.contains("box"));
}

#[test]
fn test_dot_edge_rendering() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.dep_graph.add_edge(0, 1);
    let dot = to_dot(&block);
    assert!(dot.contains("n0 -> n1"));
}

#[test]
fn test_dot_self_loop_dotted() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.dep_graph.add_edge(0, 0);
    let dot = to_dot(&block);
    assert!(dot.contains("dotted"));
}

#[test]
fn test_dot_deduplicates_edges() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(0, 1);
    let dot = to_dot(&block);
    let edge_count = dot.matches("n0 -> n1").count();
    assert_eq!(edge_count, 1);
}

// ─── Full analysis ──────────────────────────────────────────────────────────

#[test]
fn test_analyze_ext3_basic() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let result =
        analyze_mutual_block_ext3(&block, &default_config()).expect("analysis should succeed");
    assert_eq!(result.cycles.len(), 1);
    assert_eq!(result.elaboration_order.len(), 2);
    assert_eq!(result.type_dependencies.len(), 2);
    assert!(!result.stratification.is_stratifiable);
    assert_eq!(result.size_estimate.declarations.len(), 2);
    assert_eq!(result.signature_analysis.signatures.len(), 2);
}

#[test]
fn test_analyze_ext3_exceeds_declaration_limit() {
    let config = MutualDeclExt3Config {
        max_declarations: 2,
        ..default_config()
    };
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    block.build_dep_graph();
    let result = analyze_mutual_block_ext3(&block, &config);
    assert!(result.is_err());
    let err = format!("{}", result.unwrap_err());
    assert!(err.contains("exceeds limit"));
}

#[test]
fn test_analyze_ext3_no_cycles_no_forward_refs() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.dep_graph.add_edge(0, 1); // a depends on b, no reverse
    let result =
        analyze_mutual_block_ext3(&block, &default_config()).expect("analysis should succeed");
    assert!(result.cycles.is_empty());
    // Optimal order places b before a, so 0 forward refs.
    assert_eq!(result.forward_ref_count, 0);
}

#[test]
fn test_analyze_ext3_independent_stratifiable() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("x"));
    block.add_entry(mk_entry("y"));
    block.build_dep_graph();
    let result =
        analyze_mutual_block_ext3(&block, &default_config()).expect("analysis should succeed");
    assert!(result.stratification.is_stratifiable);
    assert_eq!(result.stratification.num_components, 2);
}
