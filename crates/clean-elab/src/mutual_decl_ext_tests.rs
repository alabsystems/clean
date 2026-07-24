// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended mutual declaration elaboration (SCC analysis,
//! termination inference, forward references, unfolding control).

use super::mutual_decl_ext::*;
use crate::mutual_decl::{MutualBlock, MutualEntry};
use clean_kernel::{Expr, Level};
use clean_parser::{TerminationBy, TerminationHints, TerminationKind};

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

fn mk_pi_type(depth: usize) -> Expr {
    let mut ty = Expr::sort(Level::zero());
    for _ in 0..depth {
        ty = Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::sort(Level::zero()),
            ty,
        );
    }
    ty
}

fn default_config() -> MutualDeclExtConfig {
    MutualDeclExtConfig::default()
}

fn no_hints(n: usize) -> Vec<Option<TerminationHints>> {
    vec![None; n]
}

// ─── MutualDeclExtConfig ────────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let config = MutualDeclExtConfig::default();
    assert_eq!(config.max_mutual_defs, 64);
    assert_eq!(config.max_unfold_depth, 32);
    assert!(config.try_structural);
    assert!(config.allow_wf_fallback);
}

// ─── partition_into_sccs ────────────────────────────────────────────────────

#[test]
fn test_partition_empty_block() {
    let block = MutualBlock::new();
    let groups = partition_into_sccs(&block);
    assert!(groups.is_empty());
}

#[test]
fn test_partition_single_nonrecursive() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 1);
    assert!(!groups[0].is_recursive);
    assert_eq!(groups[0].indices, vec![0]);
}

#[test]
fn test_partition_two_independent() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.build_dep_graph();
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 2);
    assert!(!groups[0].is_recursive);
    assert!(!groups[1].is_recursive);
}

#[test]
fn test_partition_simple_mutual_recursion() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("even"));
    block.add_entry(mk_entry("odd"));
    // even <-> odd
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 1);
    assert!(groups[0].is_recursive);
    assert_eq!(groups[0].indices.len(), 2);
}

#[test]
fn test_partition_chain_dependency() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a -> b -> c (linear, no cycles)
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 3);
    for g in &groups {
        assert!(!g.is_recursive);
    }
}

#[test]
fn test_partition_mixed_scc_and_independent() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.add_entry(mk_entry("h"));
    // f <-> g (mutual), h independent
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 2);

    let recursive_group = groups.iter().find(|g| g.is_recursive).unwrap();
    assert_eq!(recursive_group.indices.len(), 2);

    let non_rec_group = groups.iter().find(|g| !g.is_recursive).unwrap();
    assert_eq!(non_rec_group.indices.len(), 1);
}

#[test]
fn test_partition_self_loop_is_recursive() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    // f -> f (self-loop)
    block.dep_graph.add_edge(0, 0);
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 1);
    assert!(groups[0].is_recursive);
}

#[test]
fn test_partition_three_way_cycle() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("a"));
    block.add_entry(mk_entry("b"));
    block.add_entry(mk_entry("c"));
    // a -> b -> c -> a
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 2);
    block.dep_graph.add_edge(2, 0);
    let groups = partition_into_sccs(&block);
    assert_eq!(groups.len(), 1);
    assert!(groups[0].is_recursive);
    assert_eq!(groups[0].indices.len(), 3);
}

// ─── pre_elaborate_signatures ───────────────────────────────────────────────

#[test]
fn test_pre_elab_signatures_no_annotation() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    let sigs = pre_elaborate_signatures(&block);
    assert_eq!(sigs.len(), 1);
    assert_eq!(sigs[0].name, "f");
    assert_eq!(sigs[0].num_params, 0);
}

#[test]
fn test_pre_elab_signatures_with_pi_type() {
    let mut block = MutualBlock::new();
    let ty = mk_pi_type(3);
    block.add_entry(mk_entry_with_type("f", ty));
    let sigs = pre_elaborate_signatures(&block);
    assert_eq!(sigs[0].num_params, 3);
}

#[test]
fn test_pre_elab_signatures_preserves_order() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("alpha"));
    block.add_entry(mk_entry("beta"));
    block.add_entry(mk_entry("gamma"));
    let sigs = pre_elaborate_signatures(&block);
    assert_eq!(sigs[0].name, "alpha");
    assert_eq!(sigs[1].name, "beta");
    assert_eq!(sigs[2].name, "gamma");
    assert_eq!(sigs[0].index, 0);
    assert_eq!(sigs[1].index, 1);
    assert_eq!(sigs[2].index, 2);
}

// ─── ForwardRefContext ──────────────────────────────────────────────────────

#[test]
fn test_forward_ref_from_signatures() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    let sigs = pre_elaborate_signatures(&block);
    let ctx = ForwardRefContext::from_signatures(&sigs);
    assert_eq!(ctx.len(), 2);
    assert!(!ctx.is_empty());
    assert!(ctx.lookup("f").is_some());
    assert!(ctx.lookup("g").is_some());
    assert!(ctx.lookup("h").is_none());
}

#[test]
fn test_forward_ref_mark_resolved() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    let sigs = pre_elaborate_signatures(&block);
    let mut ctx = ForwardRefContext::from_signatures(&sigs);

    assert_eq!(ctx.unresolved_names().len(), 2);
    ctx.mark_resolved("f");
    assert_eq!(ctx.unresolved_names().len(), 1);
    assert!(ctx.lookup("f").unwrap().resolved);
    assert!(!ctx.lookup("g").unwrap().resolved);
}

#[test]
fn test_forward_ref_empty_context() {
    let ctx = ForwardRefContext::from_signatures(&[]);
    assert!(ctx.is_empty());
    assert_eq!(ctx.len(), 0);
    assert!(ctx.unresolved_names().is_empty());
}

// ─── UnfoldState ────────────────────────────────────────────────────────────

#[test]
fn test_unfold_state_initial() {
    let state = UnfoldState::new(5);
    assert!(state.can_unfold("f"));
    assert_eq!(state.depth("f"), 0);
}

#[test]
fn test_unfold_state_record_and_check() {
    let mut state = UnfoldState::new(2);
    assert!(state.record_unfold("f"));
    assert_eq!(state.depth("f"), 1);
    assert!(state.can_unfold("f"));
    assert!(state.record_unfold("f"));
    assert_eq!(state.depth("f"), 2);
    assert!(!state.can_unfold("f"));
    assert!(!state.record_unfold("f"));
}

#[test]
fn test_unfold_state_independent_names() {
    let mut state = UnfoldState::new(1);
    assert!(state.record_unfold("f"));
    assert!(!state.can_unfold("f"));
    assert!(state.can_unfold("g")); // g is independent
}

#[test]
fn test_unfold_state_reset_single() {
    let mut state = UnfoldState::new(2);
    state.record_unfold("f");
    state.record_unfold("g");
    state.reset("f");
    assert_eq!(state.depth("f"), 0);
    assert_eq!(state.depth("g"), 1);
}

#[test]
fn test_unfold_state_reset_all() {
    let mut state = UnfoldState::new(2);
    state.record_unfold("f");
    state.record_unfold("g");
    state.reset_all();
    assert_eq!(state.depth("f"), 0);
    assert_eq!(state.depth("g"), 0);
}

#[test]
fn test_unfold_state_zero_depth() {
    let state = UnfoldState::new(0);
    assert!(!state.can_unfold("f"));
}

// ─── TerminationStrategy ────────────────────────────────────────────────────

#[test]
fn test_termination_strategy_non_recursive_group() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let groups = partition_into_sccs(&block);
    assert_eq!(groups[0].strategies[0], TerminationStrategy::NonRecursive);
}

#[test]
fn test_termination_strategy_recursive_defaults_to_wf() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    for strategy in &groups[0].strategies {
        assert!(matches!(strategy, TerminationStrategy::WellFounded { .. }));
    }
}

// ─── infer_termination_metrics ──────────────────────────────────────────────

#[test]
fn test_infer_metrics_user_hint_takes_priority() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let mut groups = partition_into_sccs(&block);

    let hints = vec![
        Some(TerminationHints {
            termination_by: Some(TerminationBy {
                span: clean_parser::Span::dummy(),
                kind: TerminationKind::Structural("n".to_string()),
                params: vec!["n".to_string()],
                measure: None,
            }),
            decreasing_by: None,
        }),
        None,
    ];

    infer_termination_metrics(&mut groups[0], &block, &hints, &default_config());
    assert!(matches!(
        &groups[0].strategies[0],
        TerminationStrategy::UserProvided { .. }
    ));
}

#[test]
fn test_infer_metrics_skips_non_recursive() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let mut groups = partition_into_sccs(&block);
    let hints = no_hints(1);
    infer_termination_metrics(&mut groups[0], &block, &hints, &default_config());
    // Should remain NonRecursive.
    assert_eq!(groups[0].strategies[0], TerminationStrategy::NonRecursive);
}

// ─── encode_wf_mutual ───────────────────────────────────────────────────────

#[test]
fn test_encode_wf_mutual_recursive_group() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let groups = partition_into_sccs(&block);
    let encoded = encode_wf_mutual(&groups[0], &block).expect("should encode recursive group");
    assert_eq!(encoded.len(), 2);
    assert_eq!(encoded[0].name, "f");
    assert_eq!(encoded[1].name, "g");
}

#[test]
fn test_encode_wf_mutual_non_recursive_fails() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.build_dep_graph();
    let groups = partition_into_sccs(&block);
    let result = encode_wf_mutual(&groups[0], &block);
    assert!(result.is_err());
}

// ─── analyze_mutual_block ───────────────────────────────────────────────────

#[test]
fn test_analyze_mutual_block_basic() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("even"));
    block.add_entry(mk_entry("odd"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let hints = no_hints(2);
    let result =
        analyze_mutual_block(&block, &hints, &default_config()).expect("analysis should succeed");
    assert_eq!(result.groups.len(), 1);
    assert_eq!(result.signatures.len(), 2);
    assert_eq!(result.forward_refs.len(), 2);
}

#[test]
fn test_analyze_mutual_block_exceeds_limit() {
    let mut block = MutualBlock::new();
    let config = MutualDeclExtConfig {
        max_mutual_defs: 2,
        ..default_config()
    };
    for i in 0..3 {
        block.add_entry(mk_entry(&format!("f{i}")));
    }
    block.build_dep_graph();
    let hints = no_hints(3);
    let result = analyze_mutual_block(&block, &hints, &config);
    assert!(result.is_err());
}

// ─── validate_scc_structure ─────────────────────────────────────────────────

#[test]
fn test_validate_scc_mixed_computable_noncomputable() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f")); // computable
    block.add_entry(mk_entry_noncomp("g")); // noncomputable
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let hints = no_hints(2);
    let result =
        analyze_mutual_block(&block, &hints, &default_config()).expect("analysis should succeed");
    let validation = validate_scc_structure(&result, &block, &default_config());
    assert!(
        validation.is_err(),
        "mixed comp/noncomp in recursive SCC should fail"
    );
}

#[test]
fn test_validate_scc_wf_fallback_disabled() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let config = MutualDeclExtConfig {
        allow_wf_fallback: false,
        ..default_config()
    };
    let hints = no_hints(2);
    let result = analyze_mutual_block(&block, &hints, &config).expect("analysis should succeed");
    let validation = validate_scc_structure(&result, &block, &config);
    assert!(
        validation.is_err(),
        "wf fallback disabled should reject wf strategy"
    );
}

#[test]
fn test_validate_scc_all_computable_ok() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry("f"));
    block.add_entry(mk_entry("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let hints = no_hints(2);
    let result =
        analyze_mutual_block(&block, &hints, &default_config()).expect("analysis should succeed");
    let validation = validate_scc_structure(&result, &block, &default_config());
    assert!(validation.is_ok());
}

#[test]
fn test_validate_scc_all_noncomputable_ok() {
    let mut block = MutualBlock::new();
    block.add_entry(mk_entry_noncomp("f"));
    block.add_entry(mk_entry_noncomp("g"));
    block.dep_graph.add_edge(0, 1);
    block.dep_graph.add_edge(1, 0);
    let hints = no_hints(2);
    let result =
        analyze_mutual_block(&block, &hints, &default_config()).expect("analysis should succeed");
    let validation = validate_scc_structure(&result, &block, &default_config());
    assert!(validation.is_ok());
}
