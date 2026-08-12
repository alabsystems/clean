// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for phase-2 extended mutual declaration elaboration: structural
//! recursion detection, well-founded markers, stratification, forward
//! references, type inference, block validation, compilation order,
//! universe polymorphism, and unfolding hints.

use super::mutual_decl_ext2::*;
use crate::mutual_decl::{MutualBlock, MutualEntry};
use crate::mutual_decl_ext::partition_into_sccs;
use clean_kernel::{BinderInfo, Expr, Level, Name};

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

fn default_config() -> MutualDeclExt2Config {
    MutualDeclExt2Config::default()
}

fn mk_pi_type(depth: usize) -> Expr {
    let mut ty = Expr::sort(Level::zero());
    for _ in 0..depth {
        ty = Expr::pi(BinderInfo::Default, Expr::sort(Level::zero()), ty);
    }
    ty
}

/// Build a lambda body that references `name` as a Const (simulating recursion).
// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn mk_recursive_body(name: &str, num_params: usize) -> Expr {
    // \x0 \x1 ... \xn => name (BVar 0)
    let inner = Expr::app(Expr::const_str(name), Expr::bvar(0));
    let mut body = inner;
    for _ in 0..num_params {
        body = Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), body);
    }
    body
}

/// Build a lambda body that does NOT reference itself (non-recursive).
fn mk_nonrecursive_body(num_params: usize) -> Expr {
    let inner = Expr::sort(Level::zero());
    let mut body = inner;
    for _ in 0..num_params {
        body = Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), body);
    }
    body
}

// ─── MutualDeclExt2Config ──────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let config = MutualDeclExt2Config::default();
    assert_eq!(config.max_structural_depth, 100);
    assert_eq!(config.max_strata, 64);
    assert!(config.enable_wf_markers);
    assert_eq!(config.max_universe_params, 16);
}

#[test]
fn test_config_custom_values() {
    let config = MutualDeclExt2Config {
        max_structural_depth: 50,
        max_strata: 10,
        enable_wf_markers: false,
        max_universe_params: 4,
    };
    assert_eq!(config.max_structural_depth, 50);
    assert!(!config.enable_wf_markers);
}

// ─── Structural recursion detection ────────────────────────────────────────

#[test]
fn test_detect_structural_nonrecursive_body() {
    let body = mk_nonrecursive_body(2);
    let kind = detect_structural_recursion(&body, "f", &default_config());
    assert_eq!(kind, RecursionKind::NonRecursive);
}

#[test]
fn test_detect_structural_no_params() {
    // Body is just a constant, no lambdas.
    let body = Expr::const_str("f");
    let kind = detect_structural_recursion(&body, "f", &default_config());
    assert_eq!(kind, RecursionKind::NonRecursive);
}

#[test]
fn test_detect_structural_recursive_with_bvar_arg() {
    // \x => f x  — recursive call with BVar arg = structural candidate
    let inner = Expr::app(Expr::const_str("f"), Expr::bvar(0));
    let body = Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), inner);
    let kind = detect_structural_recursion(&body, "f", &default_config());
    assert_eq!(kind, RecursionKind::Structural { param_idx: 0 });
}

#[test]
fn test_detect_structural_recursive_without_structural_decrease() {
    // \x => f (const "other")  — recursive but no structural decrease
    let inner = Expr::app(Expr::const_str("f"), Expr::const_str("other"));
    let body = Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), inner);
    let kind = detect_structural_recursion(&body, "f", &default_config());
    assert_eq!(kind, RecursionKind::WellFounded);
}

#[test]
fn test_detect_structural_self_ref_in_let() {
    // \x => let y := g x in y
    let call = Expr::app(Expr::const_str("g"), Expr::bvar(0));
    let body = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::let_named(
            Name::from_string("y"),
            Expr::sort(Level::zero()),
            call,
            Expr::bvar(0),
            false,
        ),
    );
    let kind = detect_structural_recursion(&body, "g", &default_config());
    assert_eq!(kind, RecursionKind::Structural { param_idx: 0 });
}

#[test]
fn test_detect_structural_deeply_nested() {
    // \x0 \x1 \x2 => f (BVar 2)
    let inner = Expr::app(Expr::const_str("f"), Expr::bvar(2));
    let body = Expr::lam(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), inner),
        ),
    );
    let kind = detect_structural_recursion(&body, "f", &default_config());
    assert_eq!(kind, RecursionKind::Structural { param_idx: 0 });
}

// ─── Well-founded recursion markers ────────────────────────────────────────

#[test]
fn test_wf_markers_no_recursive_groups() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let groups = partition_into_sccs(&block);
    let markers = collect_wf_markers(&groups, &block, &default_config());
    assert!(markers.is_empty());
}

#[test]
fn test_wf_markers_recursive_group() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    let markers = collect_wf_markers(&groups, &block, &default_config());
    // Both f and g should have WF markers (bodies are Sort 0, no structural decrease).
    assert_eq!(markers.len(), 2);
}

#[test]
fn test_wf_markers_disabled() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    let config = MutualDeclExt2Config {
        enable_wf_markers: false,
        ..default_config()
    };
    let markers = collect_wf_markers(&groups, &block, &config);
    assert!(markers.is_empty());
}

#[test]
fn test_wf_marker_has_measure_for_lambda_body() {
    let mut block = MutualBlock::new();
    let body = mk_nonrecursive_body(2);
    block.add_entry(mk_entry_with_body("f", body));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    let markers = collect_wf_markers(&groups, &block, &default_config());
    // f has lambda body -> measure inferred
    let f_marker = markers.iter().find(|m| m.def_name == "f");
    assert!(f_marker.is_some());
    assert!(f_marker.unwrap().measure.is_some());
}

// ─── Definition stratification ─────────────────────────────────────────────

#[test]
fn test_stratify_empty_block() {
    let block = MutualBlock::new();
    let strata = stratify_definitions(&block);
    assert!(strata.is_empty());
}

#[test]
fn test_stratify_single_definition() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let strata = stratify_definitions(&block);
    assert_eq!(strata.len(), 1);
    assert_eq!(strata[0].level, 0);
    assert_eq!(strata[0].indices, vec![0]);
}

#[test]
fn test_stratify_chain_creates_levels() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a depends on b, b depends on c
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    let strata = stratify_definitions(&block);
    assert!(strata.len() >= 2);
    // c at level 0, b at level 1, a at level 2
    let c_stratum = strata.iter().find(|s| s.indices.contains(&2)).unwrap();
    let a_stratum = strata.iter().find(|s| s.indices.contains(&0)).unwrap();
    assert!(a_stratum.level > c_stratum.level);
}

#[test]
fn test_stratify_independent_defs_same_level() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    block.build_dep_graph();
    let strata = stratify_definitions(&block);
    assert_eq!(strata.len(), 1);
    assert_eq!(strata[0].level, 0);
    assert_eq!(strata[0].indices.len(), 3);
}

// ─── Forward reference resolution ──────────────────────────────────────────

#[test]
fn test_forward_ref_from_block() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    let resolver = ForwardRefResolver::from_block(&block);
    assert_eq!(resolver.len(), 2);
    assert!(!resolver.is_empty());
    assert!(resolver.lookup("f").is_some());
    assert!(resolver.lookup("g").is_some());
    assert!(resolver.lookup("h").is_none());
}

#[test]
fn test_forward_ref_resolve() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    let mut resolver = ForwardRefResolver::from_block(&block);
    assert_eq!(resolver.unresolved().len(), 2);

    assert!(resolver.resolve("f"));
    assert_eq!(resolver.unresolved().len(), 1);
    assert!(resolver.lookup("f").unwrap().resolved);
    assert!(!resolver.lookup("g").unwrap().resolved);

    // Resolving again returns false.
    assert!(!resolver.resolve("f"));
}

#[test]
fn test_forward_ref_resolution_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    let mut resolver = ForwardRefResolver::from_block(&block);
    resolver.resolve("c");
    resolver.resolve("a");
    resolver.resolve("b");
    assert_eq!(resolver.resolution_order(), &["c", "a", "b"]);
}

#[test]
fn test_forward_ref_empty_block() {
    let block = MutualBlock::new();
    let resolver = ForwardRefResolver::from_block(&block);
    assert!(resolver.is_empty());
    assert_eq!(resolver.len(), 0);
}

#[test]
fn test_forward_ref_with_typed_entry() {
    let mut block = MutualBlock::new();
    let ty = mk_pi_type(2);
    block.add_entry(mk_entry_with_type("f", ty.clone()));
    let resolver = ForwardRefResolver::from_block(&block);
    let entry = resolver.lookup("f").unwrap();
    // Placeholder type should be the user-provided type.
    assert!(!entry.resolved);
}

// ─── Type inference across mutual defs ─────────────────────────────────────

#[test]
fn test_infer_types_no_annotation() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let types = infer_mutual_types(&block);
    assert_eq!(types.len(), 1);
    assert_eq!(types[0].name, "f");
    assert!(!types[0].is_user_provided);
}

#[test]
fn test_infer_types_with_annotation() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_with_type("f", mk_pi_type(3)));
    let types = infer_mutual_types(&block);
    assert_eq!(types.len(), 1);
    assert!(types[0].is_user_provided);
}

#[test]
fn test_infer_types_preserves_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry_with_type("b", mk_pi_type(1)));
    block.add_entry(mk_entry("c"));
    let types = infer_mutual_types(&block);
    assert_eq!(types[0].name, "a");
    assert_eq!(types[1].name, "b");
    assert_eq!(types[2].name, "c");
    assert_eq!(types[0].index, 0);
    assert_eq!(types[1].index, 1);
    assert_eq!(types[2].index, 2);
}

// ─── Block validation ──────────────────────────────────────────────────────

#[test]
fn test_validate_empty_block_fails() {
    let block = MutualBlock::new();
    let result = validate_mutual_block(&block, &default_config());
    assert!(result.is_err());
}

#[test]
fn test_validate_duplicate_names_fails() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let result = validate_mutual_block(&block, &default_config());
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("duplicate"));
}

#[test]
fn test_validate_single_def_ok() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let result = validate_mutual_block(&block, &default_config());
    assert!(result.is_ok());
}

#[test]
fn test_validate_mixed_comp_noncomp_cycle_fails() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry_noncomp("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let result = validate_mutual_block(&block, &default_config());
    assert!(result.is_err());
}

#[test]
fn test_validate_strata_limit_exceeded() {
    let config = MutualDeclExt2Config {
        max_strata: 2,
        ..default_config()
    };
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a -> b -> c: 3 strata
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    let result = validate_mutual_block(&block, &config);
    assert!(result.is_err());
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("strata"));
}

// ─── Compilation order (topological sort) ──────────────────────────────────

#[test]
fn test_compilation_order_empty() {
    let block = MutualBlock::new();
    let order = compute_compilation_order(&block).unwrap();
    assert!(order.is_empty());
}

#[test]
fn test_compilation_order_single() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let order = compute_compilation_order(&block).unwrap();
    assert_eq!(order, vec![0]);
}

#[test]
fn test_compilation_order_respects_dependencies() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a depends on b, b depends on c
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    let order = compute_compilation_order(&block).unwrap();
    // c must come before b, b before a
    let pos_a = order.iter().position(|&x| x == 0).unwrap();
    let pos_b = order.iter().position(|&x| x == 1).unwrap();
    let pos_c = order.iter().position(|&x| x == 2).unwrap();
    assert!(pos_c < pos_b);
    assert!(pos_b < pos_a);
}

#[test]
fn test_compilation_order_cycle_groups_together() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.add_entry(mk_entry("h"));
    // f <-> g cycle, h depends on f
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    block.dep_graph.add_edge(2, 0);
    let order = compute_compilation_order(&block).unwrap();
    assert_eq!(order.len(), 3);
    // f and g should come before h
    let pos_h = order.iter().position(|&x| x == 2).unwrap();
    let pos_f = order.iter().position(|&x| x == 0).unwrap();
    let pos_g = order.iter().position(|&x| x == 1).unwrap();
    assert!(pos_f < pos_h);
    assert!(pos_g < pos_h);
}

// ─── Unfolding hints ──────────────────────────────────────────────────────

#[test]
fn test_unfold_hints_nonrecursive_always() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let kinds = vec![RecursionKind::NonRecursive];
    let hints = assign_unfold_hints(&block, &kinds);
    assert_eq!(hints.len(), 1);
    assert_eq!(hints[0], ("f".to_string(), UnfoldHint::Always));
}

#[test]
fn test_unfold_hints_structural_on_constructor() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let kinds = vec![RecursionKind::Structural { param_idx: 0 }];
    let hints = assign_unfold_hints(&block, &kinds);
    assert_eq!(hints[0].1, UnfoldHint::OnConstructor);
}

#[test]
fn test_unfold_hints_wf_bounded() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let kinds = vec![RecursionKind::WellFounded];
    let hints = assign_unfold_hints(&block, &kinds);
    assert_eq!(hints[0].1, UnfoldHint::Bounded { max_depth: 32 });
}

// ─── Universe polymorphism ─────────────────────────────────────────────────

#[test]
fn test_collect_universe_params_empty() {
    let result = collect_universe_params(&[], &default_config()).unwrap();
    assert!(result.params.is_empty());
}

#[test]
fn test_collect_universe_params_single() {
    let lists = vec![vec!["u".to_string(), "v".to_string()]];
    let result = collect_universe_params(&lists, &default_config()).unwrap();
    assert_eq!(result.params, vec!["u", "v"]);
}

#[test]
fn test_collect_universe_params_merge_unique() {
    let lists = vec![
        vec!["u".to_string()],
        vec!["v".to_string()],
        vec!["u".to_string(), "w".to_string()],
    ];
    let result = collect_universe_params(&lists, &default_config()).unwrap();
    assert_eq!(result.params, vec!["u", "v", "w"]);
}

#[test]
fn test_collect_universe_params_exceeds_limit() {
    let config = MutualDeclExt2Config {
        max_universe_params: 2,
        ..default_config()
    };
    let lists = vec![vec!["u".to_string(), "v".to_string(), "w".to_string()]];
    let result = collect_universe_params(&lists, &config);
    assert!(result.is_err());
}

#[test]
fn test_validate_universe_compatibility_ok() {
    let shared = MutualUniverseParams {
        params: vec!["u".to_string(), "v".to_string()],
    };
    let lists = vec![
        vec!["u".to_string()],
        vec!["u".to_string(), "v".to_string()],
    ];
    let result = validate_universe_compatibility(&lists, &shared);
    assert!(result.is_ok());
}

#[test]
fn test_validate_universe_compatibility_unknown_param() {
    let shared = MutualUniverseParams {
        params: vec!["u".to_string()],
    };
    let lists = vec![vec!["u".to_string(), "w".to_string()]];
    let result = validate_universe_compatibility(&lists, &shared);
    assert!(result.is_err());
}

// ─── Top-level analysis ────────────────────────────────────────────────────

#[test]
fn test_analyze_ext2_basic() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    let universe_lists = vec![vec!["u".to_string()], vec!["u".to_string()]];
    let result = analyze_mutual_block_ext2(&block, &groups, &universe_lists, &default_config())
        .expect("analysis should succeed");
    assert!(!result.strata.is_empty());
    assert_eq!(result.compilation_order.len(), 2);
    assert_eq!(result.inferred_types.len(), 2);
    assert_eq!(result.recursion_kinds.len(), 2);
    assert_eq!(result.unfold_hints.len(), 2);
    assert_eq!(result.universe_params.params, vec!["u"]);
}

#[test]
fn test_analyze_ext2_rejects_empty() {
    let block = MutualBlock::new();
    let groups = vec![];
    let result = analyze_mutual_block_ext2(&block, &groups, &[], &default_config());
    assert!(result.is_err());
}
