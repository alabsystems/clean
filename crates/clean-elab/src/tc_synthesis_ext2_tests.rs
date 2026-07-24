// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended type class synthesis (`tc_synthesis_ext2`).

use crate::instance_priority::{DefaultInstanceFallback, InstancePriority};
use crate::instances::{InstanceTable, DEFAULT_PRIORITY};
use crate::tc_synthesis_ext2::*;
use clean_kernel::expr::{Expr, ExprKind, FVarId};
use clean_kernel::name::Name;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn class_app(class: &str, args: &[&str]) -> Expr {
    let mut result = Expr::const_(Name::from_string(class), vec![]);
    for arg in args {
        result = Expr::app(result, Expr::const_(Name::from_string(arg), vec![]));
    }
    result
}

fn register(
    table: &mut InstanceTable,
    class: &str,
    num_params: usize,
    inst_name: &str,
    args: &[&str],
    priority: u32,
) {
    let cn = Name::from_string(class);
    if !table.is_class(&cn) {
        table.register_class(cn.clone(), num_params, vec![]);
    }
    table.add_instance(
        Name::from_string(inst_name),
        cn,
        Expr::const_(Name::from_string(inst_name), vec![]),
        class_app(class, args),
        priority,
    );
}

fn register_with_outparams(
    table: &mut InstanceTable,
    class: &str,
    num_params: usize,
    out_params: Vec<usize>,
    inst_name: &str,
    args: &[&str],
    priority: u32,
) {
    let cn = Name::from_string(class);
    if !table.is_class(&cn) {
        table.register_class(cn.clone(), num_params, out_params);
    }
    table.add_instance(
        Name::from_string(inst_name),
        cn,
        Expr::const_(Name::from_string(inst_name), vec![]),
        class_app(class, args),
        priority,
    );
}

// ===========================================================================
// Single-parameter resolution
// ===========================================================================

#[test]
fn test_single_param_resolve_add_nat() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    assert!(result.is_ok());
}

#[test]
fn test_single_param_no_instance() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Add", &["Bool"]), &mut state);
    assert!(matches!(result.unwrap_err(), ExtSynthError::NoInstance(_)));
}

#[test]
fn test_single_param_not_class_application() {
    let table = InstanceTable::new();
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&Expr::bvar(0), &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::NotClassApplication
    ));
}

#[test]
fn test_single_param_unregistered_class() {
    let table = InstanceTable::new();
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Unknown", &["Nat"]), &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::NotClassApplication | ExtSynthError::UnregisteredClass(_)
    ));
}

// ===========================================================================
// Multi-parameter resolution
// ===========================================================================

#[test]
fn test_multi_param_hadd_nat_nat() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "HAdd",
        3,
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("HAdd", &["Nat", "Nat", "Nat"]), &mut state);
    assert!(result.is_ok());
}

#[test]
fn test_multi_param_partial_mismatch() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "HAdd",
        3,
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("HAdd", &["Nat", "Int", "Nat"]), &mut state);
    assert!(result.is_err());
}

#[test]
fn test_multi_param_two_params() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Functor",
        2,
        "instFunctorList",
        &["List", "Type"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Functor", &["List", "Type"]), &mut state);
    assert!(result.is_ok());
}

// ===========================================================================
// Functional dependency resolution
// ===========================================================================

#[test]
fn test_fundep_basic_registration() {
    let mut registry = FunDepRegistry::new();
    let cn = Name::from_string("HAdd");
    registry.register(
        cn.clone(),
        FunDep {
            inputs: vec![0, 1],
            outputs: vec![2],
        },
    );
    assert!(registry.has_fundeps(&cn));
    assert_eq!(registry.get(&cn).len(), 1);
}

#[test]
fn test_fundep_no_deps() {
    let registry = FunDepRegistry::new();
    let cn = Name::from_string("Add");
    assert!(!registry.has_fundeps(&cn));
    assert!(registry.get(&cn).is_empty());
}

#[test]
fn test_fundep_resolution_with_outparam() {
    let mut table = InstanceTable::new();
    register_with_outparams(
        &mut table,
        "HAdd",
        3,
        vec![2],
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let mut fundeps = FunDepRegistry::new();
    fundeps.register(
        Name::from_string("HAdd"),
        FunDep {
            inputs: vec![0, 1],
            outputs: vec![2],
        },
    );
    let config = ExtSynthConfig::default();
    let synth = ExtSynthesizer::new(&table, None, Some(&fundeps), config);
    let mut state = ExtSynthState::new();
    // Goal with outparam position (index 2) — should match
    let result = synth.synthesize(&class_app("HAdd", &["Nat", "Nat", "Int"]), &mut state);
    assert!(result.is_ok());
}

#[test]
fn test_fundep_infer_outparams() {
    let mut table = InstanceTable::new();
    register_with_outparams(
        &mut table,
        "HAdd",
        3,
        vec![2],
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let mut fundeps = FunDepRegistry::new();
    fundeps.register(
        Name::from_string("HAdd"),
        FunDep {
            inputs: vec![0, 1],
            outputs: vec![2],
        },
    );
    let synth = ExtSynthesizer::new(&table, None, Some(&fundeps), ExtSynthConfig::default());
    let cn = Name::from_string("HAdd");
    let instances = table.get_instances(&cn);
    let solutions = synth.infer_outparams(&cn, &instances[0]);
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].0, 2);
}

#[test]
fn test_fundep_no_fundeps_returns_empty_outparams() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let cn = Name::from_string("Add");
    let instances = table.get_instances(&cn);
    let solutions = synth.infer_outparams(&cn, &instances[0]);
    assert!(solutions.is_empty());
}

// ===========================================================================
// Backtracking with depth limits
// ===========================================================================

#[test]
fn test_max_depth_exceeded() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let config = ExtSynthConfig {
        max_depth: 0,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    state.depth = 1; // exceed depth
    let result = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::MaxDepthExceeded(0)
    ));
}

#[test]
fn test_max_heartbeats_exceeded() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let config = ExtSynthConfig {
        max_heartbeats: 0,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    state.heartbeats = 1;
    let result = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::MaxHeartbeatsExceeded(0)
    ));
}

#[test]
fn test_depth_increments_during_resolution() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let _ = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    // After successful single-level resolution, depth should be back to 0
    assert_eq!(state.depth, 0);
}

// ===========================================================================
// Instance overlap and priority ordering
// ===========================================================================

#[test]
fn test_priority_higher_wins() {
    let mut table = InstanceTable::new();
    register(&mut table, "Show", 1, "showLow", &["Nat"], 50);
    register(&mut table, "Show", 1, "showHigh", &["Nat"], 200);
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Show", &["Nat"]), &mut state);
    let expr = result.unwrap();
    assert!(matches!(expr.kind(), ExprKind::Const(n, _) if *n == Name::from_string("showHigh")));
}

#[test]
fn test_overlap_detection_identical_args() {
    let mut table = InstanceTable::new();
    register(&mut table, "Show", 1, "showA", &["Nat"], 100);
    register(&mut table, "Show", 1, "showB", &["Nat"], 50);
    let overlaps = detect_overlaps(&Name::from_string("Show"), &table);
    assert_eq!(overlaps.len(), 1);
    assert_eq!(overlaps[0].inst_a, Name::from_string("showA"));
    assert_eq!(overlaps[0].inst_b, Name::from_string("showB"));
}

#[test]
fn test_overlap_detection_no_overlap() {
    let mut table = InstanceTable::new();
    register(&mut table, "Show", 1, "showNat", &["Nat"], 100);
    register(&mut table, "Show", 1, "showBool", &["Bool"], 100);
    let overlaps = detect_overlaps(&Name::from_string("Show"), &table);
    assert!(overlaps.is_empty());
}

#[test]
fn test_overlap_detection_multi_param() {
    let mut table = InstanceTable::new();
    register(&mut table, "HAdd", 3, "haddA", &["Nat", "Nat", "Nat"], 100);
    register(&mut table, "HAdd", 3, "haddB", &["Nat", "Nat", "Nat"], 50);
    let overlaps = detect_overlaps(&Name::from_string("HAdd"), &table);
    assert_eq!(overlaps.len(), 1);
}

#[test]
fn test_all_candidates_failed_error() {
    let mut table = InstanceTable::new();
    register(&mut table, "Show", 1, "showNat", &["Nat"], DEFAULT_PRIORITY);
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Show", &["Bool"]), &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::AllCandidatesFailed { count: 1, .. }
    ));
}

// ===========================================================================
// Default instance fallback
// ===========================================================================

#[test]
fn test_default_instance_fallback() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Repr"), 1, vec![]);
    // No regular instances
    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Repr"),
        Name::from_string("defaultReprNat"),
        Expr::const_(Name::from_string("defaultReprNat"), vec![]),
        class_app("Repr", &["Nat"]),
        InstancePriority::DEFAULT_INSTANCE,
    );
    let config = ExtSynthConfig::default();
    let synth = ExtSynthesizer::new(&table, Some(&defaults), None, config);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Repr", &["Nat"]), &mut state);
    assert!(result.is_ok());
}

#[test]
fn test_default_instance_not_used_when_regular_matches() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Repr",
        1,
        "regularRepr",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Repr"),
        Name::from_string("defaultRepr"),
        Expr::const_(Name::from_string("defaultRepr"), vec![]),
        class_app("Repr", &["Nat"]),
        InstancePriority::DEFAULT_INSTANCE,
    );
    let synth = ExtSynthesizer::new(&table, Some(&defaults), None, ExtSynthConfig::default());
    let mut state = ExtSynthState::new();
    let result = synth
        .synthesize(&class_app("Repr", &["Nat"]), &mut state)
        .unwrap();
    assert!(
        matches!(result.kind(), ExprKind::Const(n, _) if *n == Name::from_string("regularRepr"))
    );
}

#[test]
fn test_default_disabled_in_config() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Repr"), 1, vec![]);
    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Repr"),
        Name::from_string("defaultRepr"),
        Expr::const_(Name::from_string("defaultRepr"), vec![]),
        class_app("Repr", &["Nat"]),
        InstancePriority::DEFAULT_INSTANCE,
    );
    let config = ExtSynthConfig {
        use_defaults: false,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, Some(&defaults), None, config);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Repr", &["Nat"]), &mut state);
    assert!(result.is_err());
}

// ===========================================================================
// Outparam inference
// ===========================================================================

#[test]
fn test_outparam_skipped_during_matching() {
    let mut table = InstanceTable::new();
    register_with_outparams(
        &mut table,
        "HAdd",
        3,
        vec![2],
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    // Goal with different outparam — should still match since idx 2 is outparam
    let result = synth.synthesize(&class_app("HAdd", &["Nat", "Nat", "Int"]), &mut state);
    assert!(result.is_ok());
}

#[test]
fn test_outparam_non_outparam_mismatch_fails() {
    let mut table = InstanceTable::new();
    register_with_outparams(
        &mut table,
        "HAdd",
        3,
        vec![2],
        "instHAddNatNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    // Input param 1 is "Int" instead of "Nat" — should fail
    let result = synth.synthesize(&class_app("HAdd", &["Nat", "Int", "Nat"]), &mut state);
    assert!(result.is_err());
}

// ===========================================================================
// Trace generation
// ===========================================================================

#[test]
fn test_trace_enabled_records_entries() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let config = ExtSynthConfig {
        trace_enabled: true,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    let _ = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    assert!(!state.trace.is_empty());
    assert_eq!(state.success_count(), 1);
}

#[test]
fn test_trace_disabled_no_entries() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let config = ExtSynthConfig {
        trace_enabled: false,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    let _ = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    assert!(state.trace.is_empty());
}

#[test]
fn test_trace_records_mismatches() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    register(&mut table, "Add", 1, "instAddBool", &["Bool"], 50);
    let config = ExtSynthConfig {
        trace_enabled: true,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    let _ = synth.synthesize(&class_app("Add", &["Bool"]), &mut state);
    // instAddNat tried first (higher priority) → mismatch, instAddBool → success
    let mismatches = state
        .trace
        .iter()
        .filter(|e| e.outcome == ExtTraceOutcome::StructuralMismatch)
        .count();
    assert!(mismatches >= 1);
}

#[test]
fn test_trace_summary_only_successes() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    register(&mut table, "Add", 1, "instAddBool", &["Bool"], 50);
    let config = ExtSynthConfig {
        trace_enabled: true,
        ..Default::default()
    };
    let synth = ExtSynthesizer::new(&table, None, None, config);
    let mut state = ExtSynthState::new();
    let _ = synth.synthesize(&class_app("Add", &["Nat"]), &mut state);
    let summary = ExtSynthesizer::trace_summary(&state);
    assert_eq!(summary.len(), 1);
    assert_eq!(summary[0].1, Name::from_string("instAddNat"));
}

// ===========================================================================
// Stuck instance detection
// ===========================================================================

#[test]
fn test_stuck_goal_with_fvar() {
    let goal = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::fvar(FVarId::new(42)),
    );
    assert!(is_stuck_goal(&goal));
}

#[test]
fn test_not_stuck_goal_concrete() {
    let goal = class_app("Add", &["Nat"]);
    assert!(!is_stuck_goal(&goal));
}

#[test]
fn test_stuck_goal_not_class_app() {
    assert!(!is_stuck_goal(&Expr::bvar(0)));
}

#[test]
fn test_synthesize_stuck_returns_error() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let goal = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::fvar(FVarId::new(99)),
    );
    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        ExtSynthError::StuckInstance { .. }
    ));
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_empty_instance_table() {
    let table = InstanceTable::new();
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let result = synth.synthesize(&class_app("Anything", &["Nat"]), &mut state);
    assert!(result.is_err());
}

#[test]
fn test_cache_hit_on_repeated_synthesis() {
    let mut table = InstanceTable::new();
    register(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let goal = class_app("Add", &["Nat"]);
    let _ = synth.synthesize(&goal, &mut state);
    let heartbeats_after_first = state.heartbeats;
    let _ = synth.synthesize(&goal, &mut state);
    // Second call should hit cache, so heartbeats should not increase
    assert_eq!(state.heartbeats, heartbeats_after_first);
}

#[test]
fn test_cache_negative_result() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    let synth = ExtSynthesizer::with_defaults(&table);
    let mut state = ExtSynthState::new();
    let goal = class_app("Add", &["Bool"]);
    let _ = synth.synthesize(&goal, &mut state);
    // Second call should hit negative cache
    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(result.unwrap_err(), ExtSynthError::NoInstance(_)));
}

#[test]
fn test_build_ext_class_app() {
    let expr = build_ext_class_app(
        &Name::from_string("Add"),
        &[Expr::const_(Name::from_string("Nat"), vec![])],
    );
    // Should be App(Const("Add"), Const("Nat"))
    assert!(matches!(expr.kind(), ExprKind::App(_, _)));
}

#[test]
fn test_build_ext_class_app_no_args() {
    let expr = build_ext_class_app(&Name::from_string("Inhabited"), &[]);
    assert!(matches!(expr.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Inhabited")));
}

#[test]
fn test_config_default_values() {
    let config = ExtSynthConfig::default();
    assert_eq!(config.max_depth, 32);
    assert_eq!(config.max_heartbeats, 10_000);
    assert!(config.use_defaults);
    assert!(!config.trace_enabled);
}

#[test]
fn test_state_new_is_zeroed() {
    let state = ExtSynthState::new();
    assert_eq!(state.depth, 0);
    assert_eq!(state.heartbeats, 0);
    assert!(state.trace.is_empty());
    assert!(state.cache.is_empty());
    assert_eq!(state.success_count(), 0);
}
