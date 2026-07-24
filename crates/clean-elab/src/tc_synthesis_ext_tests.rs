// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for enhanced type class synthesis (`tc_synthesis_ext`).

use crate::instance_priority::{DefaultInstanceFallback, InstancePriority};
use crate::instances::{extract_class_app, InstanceTable, DEFAULT_PRIORITY};
use crate::tc_synthesis_ext::*;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a simple class application `ClassName Arg1 Arg2 ...`.
fn class_app(class: &str, args: &[&str]) -> Expr {
    let mut result = Expr::const_(Name::from_string(class), vec![]);
    for arg in args {
        result = Expr::app(result, Expr::const_(Name::from_string(arg), vec![]));
    }
    result
}

/// Register a class and add a simple instance.
fn register_simple(
    table: &mut InstanceTable,
    class: &str,
    num_params: usize,
    inst_name: &str,
    args: &[&str],
    priority: u32,
) {
    let class_name = Name::from_string(class);
    if !table.is_class(&class_name) {
        table.register_class(class_name.clone(), num_params, vec![]);
    }
    let inst_type = class_app(class, args);
    let inst_expr = Expr::const_(Name::from_string(inst_name), vec![]);
    table.add_instance(
        Name::from_string(inst_name),
        class_name,
        inst_expr,
        inst_type,
        priority,
    );
}

// ---------------------------------------------------------------------------
// Basic synthesis
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_basic_nat_instance() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Add", &["Nat"]);

    let result = synth.synthesize(&goal, &mut state);
    let expr = result.expect("should resolve Add Nat");
    assert!(
        matches!(expr.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instAddNat"))
    );
}

#[test]
fn test_synthesize_no_instance_returns_error() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Add", &["Bool"]);

    let result = synth.synthesize(&goal, &mut state);
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), TcSynthError::NoInstance(_)));
}

#[test]
fn test_synthesize_unregistered_class_error() {
    let table = InstanceTable::new();
    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("NotAClass", &["Nat"]);

    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        TcSynthError::NotClassApplication | TcSynthError::UnregisteredClass(_)
    ));
}

#[test]
fn test_synthesize_non_class_goal_error() {
    let table = InstanceTable::new();
    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    // BVar is not a class application
    let goal = Expr::bvar(0);

    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        TcSynthError::NotClassApplication
    ));
}

// ---------------------------------------------------------------------------
// Priority ordering / backtracking
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_priority_order_high_wins() {
    let mut table = InstanceTable::new();
    let class = "Show";
    let class_name = Name::from_string(class);
    table.register_class(class_name.clone(), 1, vec![]);

    // Low priority instance
    register_simple(&mut table, class, 1, "showLow", &["Nat"], 50);
    // High priority instance
    register_simple(&mut table, class, 1, "showHigh", &["Nat"], 200);
    // Medium priority instance
    register_simple(&mut table, class, 1, "showMed", &["Nat"], 100);

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app(class, &["Nat"]);

    let result = synth.synthesize(&goal, &mut state).unwrap();
    // Should return the highest-priority instance
    assert!(
        matches!(result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("showHigh"))
    );
}

#[test]
fn test_synthesize_backtracking_skips_wrong_arg() {
    let mut table = InstanceTable::new();
    let class = "Repr";
    table.register_class(Name::from_string(class), 1, vec![]);

    // Instance for Int (high priority but wrong arg)
    register_simple(&mut table, class, 1, "reprInt", &["Int"], 200);
    // Instance for Nat (lower priority but correct)
    register_simple(&mut table, class, 1, "reprNat", &["Nat"], 100);

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app(class, &["Nat"]);

    let result = synth.synthesize(&goal, &mut state).unwrap();
    assert!(
        matches!(result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("reprNat"))
    );
}

// ---------------------------------------------------------------------------
// Depth limiting
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_max_depth_exceeded() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let config = TcSynthConfig {
        max_depth: 2,
        ..TcSynthConfig::default()
    };
    let synth = TcSynthesizer::new(&table, None, config);

    let mut state = TcSynthState::new();
    state.depth = 3; // Already beyond max
    let goal = class_app("Add", &["Nat"]);

    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        TcSynthError::MaxDepthExceeded(2)
    ));
}

#[test]
fn test_synthesize_max_heartbeats_exceeded() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let config = TcSynthConfig {
        max_heartbeats: 0,
        ..TcSynthConfig::default()
    };
    let synth = TcSynthesizer::new(&table, None, config);
    let mut state = TcSynthState::new();
    state.heartbeats = 1; // Already beyond max
    let goal = class_app("Add", &["Nat"]);

    let result = synth.synthesize(&goal, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        TcSynthError::MaxHeartbeatsExceeded(0)
    ));
}

// ---------------------------------------------------------------------------
// Synthesis cache
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_cache_hit() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Add", &["Nat"]);

    // First call populates cache
    let result1 = synth.synthesize(&goal, &mut state).unwrap();
    assert_eq!(state.cache_size(), 1);

    // Second call should use cache
    let heartbeats_before = state.heartbeats;
    let result2 = synth.synthesize(&goal, &mut state).unwrap();
    // Cache hit means no additional heartbeats
    assert_eq!(state.heartbeats, heartbeats_before);

    // Results should be the same
    assert_eq!(format!("{result1:?}"), format!("{result2:?}"));
}

#[test]
fn test_synthesize_negative_cache() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    // No instances for Bool

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Add", &["Bool"]);

    // First call: no instance
    assert!(synth.synthesize(&goal, &mut state).is_err());
    assert_eq!(state.cache_size(), 1);

    // Second call: should hit negative cache
    assert!(synth.synthesize(&goal, &mut state).is_err());
}

// ---------------------------------------------------------------------------
// Default instances
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_default_instance_fallback() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Inhabited"), 1, vec![]);
    // No regular instances

    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Inhabited"),
        Name::from_string("instInhabitedDefault"),
        Expr::const_(Name::from_string("instInhabitedDefault"), vec![]),
        class_app("Inhabited", &["Unit"]),
        InstancePriority::DEFAULT_INSTANCE,
    );

    let synth = TcSynthesizer::new(&table, Some(&defaults), TcSynthConfig::default());
    let mut state = TcSynthState::new();
    let goal = class_app("Inhabited", &["Unit"]);

    let result = synth.synthesize(&goal, &mut state).unwrap();
    assert!(
        matches!(result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instInhabitedDefault"))
    );
}

#[test]
fn test_synthesize_regular_before_default() {
    let mut table = InstanceTable::new();
    register_simple(&mut table, "Inhabited", 1, "instRegular", &["Nat"], 100);

    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Inhabited"),
        Name::from_string("instDefault"),
        Expr::const_(Name::from_string("instDefault"), vec![]),
        class_app("Inhabited", &["Nat"]),
        InstancePriority::DEFAULT_INSTANCE,
    );

    let synth = TcSynthesizer::new(&table, Some(&defaults), TcSynthConfig::default());
    let mut state = TcSynthState::new();
    let goal = class_app("Inhabited", &["Nat"]);

    let result = synth.synthesize(&goal, &mut state).unwrap();
    // Regular instance should win over default
    assert!(
        matches!(result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instRegular"))
    );
}

#[test]
fn test_synthesize_default_instances_disabled() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Inhabited"), 1, vec![]);

    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        Name::from_string("Inhabited"),
        Name::from_string("instDefault"),
        Expr::const_(Name::from_string("instDefault"), vec![]),
        class_app("Inhabited", &["Unit"]),
        InstancePriority::DEFAULT_INSTANCE,
    );

    let config = TcSynthConfig {
        use_default_instances: false,
        ..TcSynthConfig::default()
    };
    let synth = TcSynthesizer::new(&table, Some(&defaults), config);
    let mut state = TcSynthState::new();
    let goal = class_app("Inhabited", &["Unit"]);

    // Should fail because defaults are disabled
    assert!(synth.synthesize(&goal, &mut state).is_err());
}

// ---------------------------------------------------------------------------
// OutParam propagation
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_with_out_params() {
    let mut table = InstanceTable::new();
    // HAdd has 3 params: (a, b, outParam c)
    let hadd = Name::from_string("HAdd");
    table.register_class(hadd.clone(), 3, vec![2]); // index 2 is outParam

    let inst_type = class_app("HAdd", &["Nat", "Nat", "Nat"]);
    let inst_expr = Expr::const_(Name::from_string("instHAddNat"), vec![]);
    table.add_instance(
        Name::from_string("instHAddNat"),
        hadd.clone(),
        inst_expr,
        inst_type,
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    // Goal: HAdd Nat Nat ?outparam -- use a placeholder for the outparam
    let goal = class_app("HAdd", &["Nat", "Nat", "Nat"]);

    let result = synth.synthesize(&goal, &mut state).unwrap();
    assert!(
        matches!(result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instHAddNat"))
    );
}

#[test]
fn test_out_param_propagation_extracts_solutions() {
    let mut table = InstanceTable::new();
    let hadd = Name::from_string("HAdd");
    table.register_class(hadd.clone(), 3, vec![2]);

    let inst_type = class_app("HAdd", &["Nat", "Nat", "Int"]);
    let inst_expr = Expr::const_(Name::from_string("instHAddNatInt"), vec![]);
    table.add_instance(
        Name::from_string("instHAddNatInt"),
        hadd.clone(),
        inst_expr,
        inst_type,
        DEFAULT_PRIORITY,
    );

    let info = &table.get_instances(&hadd)[0];
    let solutions = extract_out_param_solutions(info, &[2]);
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].0, 2);
    // The outparam solution should be "Int"
    assert!(matches!(
        solutions[0].1.kind(),
        clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("Int")
    ));
}

#[test]
fn test_propagate_out_params_replaces_args() {
    let goal_args = vec![
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::bvar(99), // placeholder for outparam
    ];
    let solutions = vec![(2, Expr::const_(Name::from_string("Int"), vec![]))];

    let result = propagate_out_params(&goal_args, &solutions);
    assert_eq!(result.len(), 3);
    assert!(matches!(
        result[2].kind(),
        clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("Int")
    ));
}

// ---------------------------------------------------------------------------
// Synthesis tracing
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_trace_records_steps() {
    let mut table = InstanceTable::new();
    register_simple(&mut table, "Repr", 1, "reprInt", &["Int"], 200);
    register_simple(&mut table, "Repr", 1, "reprNat", &["Nat"], 100);

    let config = TcSynthConfig {
        trace_enabled: true,
        ..TcSynthConfig::default()
    };
    let synth = TcSynthesizer::new(&table, None, config);
    let mut state = TcSynthState::new();
    let goal = class_app("Repr", &["Nat"]);

    let _ = synth.synthesize(&goal, &mut state).unwrap();
    // Trace should have 2 entries: reprInt (failed), reprNat (success)
    assert_eq!(state.trace.len(), 2);
    assert_eq!(state.trace[0].outcome, SynthOutcome::StructuralMismatch);
    assert_eq!(state.trace[1].outcome, SynthOutcome::Success);
}

#[test]
fn test_synthesize_trace_disabled_no_entries() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let config = TcSynthConfig {
        trace_enabled: false,
        ..TcSynthConfig::default()
    };
    let synth = TcSynthesizer::new(&table, None, config);
    let mut state = TcSynthState::new();
    let goal = class_app("Add", &["Nat"]);

    let _ = synth.synthesize(&goal, &mut state).unwrap();
    assert!(state.trace.is_empty());
}

// ---------------------------------------------------------------------------
// has_candidates
// ---------------------------------------------------------------------------

#[test]
fn test_has_candidates_true() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);
    assert!(synth.has_candidates(&class_app("Add", &["Nat"])));
}

#[test]
fn test_has_candidates_false_no_instances() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);

    let synth = TcSynthesizer::with_defaults(&table);
    assert!(!synth.has_candidates(&class_app("Add", &["Nat"])));
}

#[test]
fn test_has_candidates_false_not_class() {
    let table = InstanceTable::new();
    let synth = TcSynthesizer::with_defaults(&table);
    assert!(!synth.has_candidates(&Expr::bvar(0)));
}

// ---------------------------------------------------------------------------
// build_class_app helper
// ---------------------------------------------------------------------------

#[test]
fn test_build_class_app_roundtrip() {
    let class_name = Name::from_string("Functor");
    let args = vec![
        Expr::const_(Name::from_string("List"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    ];
    let expr = build_class_app(&class_name, &args);

    let (extracted_name, extracted_args) = extract_class_app(&expr).unwrap();
    assert_eq!(extracted_name, class_name);
    assert_eq!(extracted_args.len(), 2);
}

#[test]
fn test_build_class_app_no_args() {
    let class_name = Name::from_string("Inhabited");
    let expr = build_class_app(&class_name, &[]);

    let (extracted_name, extracted_args) = extract_class_app(&expr).unwrap();
    assert_eq!(extracted_name, class_name);
    assert_eq!(extracted_args.len(), 0);
}

// ---------------------------------------------------------------------------
// Dependency-aware synthesis
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_with_deps_all_resolved() {
    let mut table = InstanceTable::new();
    // Register Add and HAdd classes
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    register_simple(
        &mut table,
        "HAdd",
        3,
        "instHAddNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    table.register_class(Name::from_string("HAdd"), 3, vec![]);

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("HAdd", &["Nat", "Nat", "Nat"]);
    let deps = vec![SynthDependency {
        class_name: Name::from_string("Add"),
        args: vec![Expr::const_(Name::from_string("Nat"), vec![])],
    }];

    let result = synth.synthesize_with_deps(&goal, &deps, &mut state);
    let _ = result.expect("should resolve HAdd Nat Nat Nat with Add Nat dependency");
}

#[test]
fn test_synthesize_with_deps_dep_fails() {
    let mut table = InstanceTable::new();
    // HAdd registered but Add is not
    register_simple(
        &mut table,
        "HAdd",
        3,
        "instHAddNat",
        &["Nat", "Nat", "Nat"],
        DEFAULT_PRIORITY,
    );
    table.register_class(Name::from_string("Add"), 1, vec![]);
    // No Add instances

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("HAdd", &["Nat", "Nat", "Nat"]);
    let deps = vec![SynthDependency {
        class_name: Name::from_string("Add"),
        args: vec![Expr::const_(Name::from_string("Nat"), vec![])],
    }];

    let result = synth.synthesize_with_deps(&goal, &deps, &mut state);
    assert!(matches!(
        result.unwrap_err(),
        TcSynthError::DependencyFailed { .. }
    ));
}

// ---------------------------------------------------------------------------
// TcSynthState
// ---------------------------------------------------------------------------

#[test]
fn test_synth_state_success_count() {
    let mut state = TcSynthState::new();
    state.trace.push(SynthTraceEntry {
        class_name: Name::from_string("Add"),
        candidate: Name::from_string("inst1"),
        depth: 0,
        outcome: SynthOutcome::StructuralMismatch,
    });
    state.trace.push(SynthTraceEntry {
        class_name: Name::from_string("Add"),
        candidate: Name::from_string("inst2"),
        depth: 0,
        outcome: SynthOutcome::Success,
    });
    assert_eq!(state.success_count(), 1);
}

#[test]
fn test_synth_state_with_cache() {
    let mut cache = HashMap::new();
    cache.insert(
        "key".to_string(),
        Some(Expr::const_(Name::from_string("cached"), vec![])),
    );
    let state = TcSynthState::with_cache(cache);
    assert_eq!(state.cache_size(), 1);
    assert_eq!(state.depth, 0);
    assert_eq!(state.heartbeats, 0);
}

// ---------------------------------------------------------------------------
// Multiple instances for same class, different args
// ---------------------------------------------------------------------------

#[test]
fn test_synthesize_multiple_types_same_class() {
    let mut table = InstanceTable::new();
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddNat",
        &["Nat"],
        DEFAULT_PRIORITY,
    );
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddInt",
        &["Int"],
        DEFAULT_PRIORITY,
    );
    register_simple(
        &mut table,
        "Add",
        1,
        "instAddFloat",
        &["Float"],
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);

    // Resolve Add Nat
    let mut state = TcSynthState::new();
    let nat_result = synth
        .synthesize(&class_app("Add", &["Nat"]), &mut state)
        .unwrap();
    assert!(
        matches!(nat_result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instAddNat"))
    );

    // Resolve Add Int
    let int_result = synth
        .synthesize(&class_app("Add", &["Int"]), &mut state)
        .unwrap();
    assert!(
        matches!(int_result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instAddInt"))
    );

    // Resolve Add Float
    let float_result = synth
        .synthesize(&class_app("Add", &["Float"]), &mut state)
        .unwrap();
    assert!(
        matches!(float_result.kind(), clean_kernel::expr::ExprKind::Const(n, _) if *n == Name::from_string("instAddFloat"))
    );
}

// ---------------------------------------------------------------------------
// Config variations
// ---------------------------------------------------------------------------

#[test]
fn test_config_defaults() {
    let config = TcSynthConfig::default();
    assert_eq!(config.max_depth, 32);
    assert_eq!(config.max_heartbeats, 10_000);
    assert!(config.use_default_instances);
    assert!(config.propagate_out_params);
    assert!(!config.trace_enabled);
}

// ---------------------------------------------------------------------------
// All candidates failed error
// ---------------------------------------------------------------------------

#[test]
fn test_all_candidates_failed_error() {
    let mut table = InstanceTable::new();
    // Register class with instances that don't match the goal
    register_simple(
        &mut table,
        "Mul",
        1,
        "instMulInt",
        &["Int"],
        DEFAULT_PRIORITY,
    );
    register_simple(
        &mut table,
        "Mul",
        1,
        "instMulFloat",
        &["Float"],
        DEFAULT_PRIORITY,
    );

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Mul", &["Nat"]); // No Nat instance

    let result = synth.synthesize(&goal, &mut state);
    match result.unwrap_err() {
        TcSynthError::AllCandidatesFailed { class_name, count } => {
            assert_eq!(class_name, Name::from_string("Mul"));
            assert_eq!(count, 2);
        }
        other => panic!("Expected AllCandidatesFailed, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Heartbeat accounting
// ---------------------------------------------------------------------------

#[test]
fn test_heartbeat_accounting() {
    let mut table = InstanceTable::new();
    register_simple(&mut table, "Show", 1, "showInt", &["Int"], 200);
    register_simple(&mut table, "Show", 1, "showFloat", &["Float"], 100);
    register_simple(&mut table, "Show", 1, "showNat", &["Nat"], 50);

    let synth = TcSynthesizer::with_defaults(&table);
    let mut state = TcSynthState::new();
    let goal = class_app("Show", &["Nat"]);

    let _ = synth.synthesize(&goal, &mut state).unwrap();
    // Should try showInt (fail), showFloat (fail), showNat (success) = 3 heartbeats
    assert_eq!(state.heartbeats, 3);
}
