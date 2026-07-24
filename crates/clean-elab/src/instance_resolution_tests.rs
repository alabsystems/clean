// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the standalone instance resolution engine.

use super::*;
use crate::instances::{InstanceTable, DEFAULT_PRIORITY};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

/// Helper: create a simple class type `ClassName ArgName`
fn class_app(class: &str, arg: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(class), vec![]),
        Expr::const_(Name::from_string(arg), vec![]),
    )
}

/// Helper: register a class and a simple instance in the table.
fn setup_simple_instance(
    table: &mut InstanceTable,
    class: &str,
    arg: &str,
    instance: &str,
    priority: u32,
) {
    let class_name = Name::from_string(class);
    if !table.is_class(&class_name) {
        table.register_class(class_name.clone(), 1, vec![]);
    }
    let inst_name = Name::from_string(instance);
    let inst_type = class_app(class, arg);
    let inst_expr = Expr::const_(inst_name.clone(), vec![]);
    table.add_instance(inst_name, class_name, inst_expr, inst_type, priority);
}

// ==========================================================================
// Basic resolution
// ==========================================================================

#[test]
fn test_resolve_simple_instance() {
    let mut table = InstanceTable::new();
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    let goal = class_app("Add", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    let inst = result.expect("should resolve Add Nat");
    // The result should be the instAddNat constant
    match inst.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("instAddNat"));
        }
        _ => panic!("expected Const, got {inst:?}"),
    }

    // Trace should have one step
    assert_eq!(state.trace.len(), 1);
    assert!(state.trace[0].success);
    assert_eq!(state.trace[0].depth, 0);
}

// ==========================================================================
// No instance
// ==========================================================================

#[test]
fn test_resolve_no_instance() {
    let mut table = InstanceTable::new();
    // Register class but no instances
    table.register_class(Name::from_string("Add"), 1, vec![]);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    let goal = class_app("Add", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    match result.unwrap_err() {
        ResolutionError::NoInstance(name) => {
            assert_eq!(name, Name::from_string("Add"));
        }
        other => panic!("expected NoInstance, got {other:?}"),
    }
}

// ==========================================================================
// Unregistered class
// ==========================================================================

#[test]
fn test_resolve_unregistered_class() {
    let table = InstanceTable::new();

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    let goal = class_app("Nonexistent", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    match result.unwrap_err() {
        ResolutionError::UnregisteredClass(name) => {
            assert_eq!(name, Name::from_string("Nonexistent"));
        }
        other => panic!("expected UnregisteredClass, got {other:?}"),
    }
}

// ==========================================================================
// Not a class application
// ==========================================================================

#[test]
fn test_resolve_not_class_app() {
    let table = InstanceTable::new();

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    // BVar is not a class application
    let goal = Expr::bvar(0);
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ResolutionError::NotClassApplication
    ));
}

// ==========================================================================
// Priority ordering
// ==========================================================================

#[test]
fn test_resolve_priority_ordering() {
    let mut table = InstanceTable::new();
    // Add two instances with different priorities
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNatLow", 50);
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNatHigh", 200);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    let goal = class_app("Add", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    let inst = result.expect("should resolve Add Nat");
    // Higher priority (200) should be tried and found first
    match inst.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("instAddNatHigh"));
        }
        _ => panic!("expected Const, got {inst:?}"),
    }

    // First trace entry should be the high-priority instance (tried first, succeeds)
    assert!(state.trace[0].success);
    assert_eq!(
        state.trace[0].instance_tried,
        Name::from_string("instAddNatHigh")
    );
}

// ==========================================================================
// Cache hit
// ==========================================================================

#[test]
fn test_resolve_cache_hit() {
    let mut table = InstanceTable::new();
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    let goal = class_app("Add", "Nat");

    // First resolution
    let result1 = resolve_instance(&goal, &table, &config, &mut state);
    assert!(result1.is_ok());
    assert_eq!(state.trace.len(), 1);

    // Second resolution should hit cache (no new trace entries)
    let heartbeats_before = state.heartbeats;
    let result2 = resolve_instance(&goal, &table, &config, &mut state);
    assert!(result2.is_ok());
    // No new trace entries because cache was hit
    assert_eq!(state.trace.len(), 1);
    // No additional heartbeats consumed
    assert_eq!(state.heartbeats, heartbeats_before);
}

// ==========================================================================
// Max depth exceeded
// ==========================================================================

#[test]
fn test_resolve_max_depth_exceeded() {
    let mut table = InstanceTable::new();
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig {
        max_depth: 5,
        ..Default::default()
    };
    let mut state = ResolutionState::new();
    state.depth = 6; // Already past the limit

    let goal = class_app("Add", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    match result.unwrap_err() {
        ResolutionError::MaxDepthExceeded(limit) => {
            assert_eq!(limit, 5);
        }
        other => panic!("expected MaxDepthExceeded, got {other:?}"),
    }
}

// ==========================================================================
// Max heartbeats exceeded
// ==========================================================================

#[test]
fn test_resolve_max_heartbeats_exceeded() {
    let mut table = InstanceTable::new();
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig {
        max_heartbeats: 0, // Immediate timeout
        ..Default::default()
    };
    let mut state = ResolutionState::new();
    state.heartbeats = 1; // Already past the limit

    let goal = class_app("Add", "Nat");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        ResolutionError::MaxHeartbeatsExceeded(_)
    ));
}

// ==========================================================================
// Wrong argument structural mismatch
// ==========================================================================

#[test]
fn test_resolve_structural_mismatch() {
    let mut table = InstanceTable::new();
    // Instance for Add Nat
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    // Goal: Add Bool (no matching instance)
    let goal = class_app("Add", "Bool");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    assert!(result.is_err());
    match result.unwrap_err() {
        ResolutionError::UnificationFailed {
            class_name,
            candidate_count,
        } => {
            assert_eq!(class_name, Name::from_string("Add"));
            assert_eq!(candidate_count, 1);
        }
        other => panic!("expected UnificationFailed, got {other:?}"),
    }

    // Trace should show the failed attempt
    assert_eq!(state.trace.len(), 1);
    assert!(!state.trace[0].success);
}

// ==========================================================================
// has_instance quick check
// ==========================================================================

#[test]
fn test_has_instance_true() {
    let mut table = InstanceTable::new();
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    assert!(has_instance(&Name::from_string("Add"), &table));
}

#[test]
fn test_has_instance_false_no_class() {
    let table = InstanceTable::new();
    assert!(!has_instance(&Name::from_string("Add"), &table));
}

#[test]
fn test_has_instance_false_no_instances() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    assert!(!has_instance(&Name::from_string("Add"), &table));
}

// ==========================================================================
// Default config values
// ==========================================================================

#[test]
fn test_resolution_config_defaults() {
    let config = ResolutionConfig::default();
    assert_eq!(config.max_depth, 32);
    assert_eq!(config.max_heartbeats, 10_000);
}

// ==========================================================================
// State initialization
// ==========================================================================

#[test]
fn test_resolution_state_new() {
    let state = ResolutionState::new();
    assert_eq!(state.depth, 0);
    assert_eq!(state.heartbeats, 0);
    assert!(state.trace.is_empty());
    assert!(state.cache.is_empty());
}

#[test]
fn test_resolution_state_with_cache() {
    let mut cache = HashMap::new();
    cache.insert(
        "test".to_string(),
        Some(Expr::const_(Name::from_string("x"), vec![])),
    );

    let state = ResolutionState::with_cache(cache);
    assert_eq!(state.cache.len(), 1);
    assert_eq!(state.depth, 0);
}

// ==========================================================================
// Multiple instances, first match wins
// ==========================================================================

#[test]
fn test_resolve_multiple_same_priority() {
    let mut table = InstanceTable::new();
    // Two instances at the same priority for different types
    setup_simple_instance(&mut table, "Show", "Nat", "instShowNat", DEFAULT_PRIORITY);
    setup_simple_instance(&mut table, "Show", "Bool", "instShowBool", DEFAULT_PRIORITY);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    // Resolve Show Bool
    let goal = class_app("Show", "Bool");
    let result = resolve_instance(&goal, &table, &config, &mut state);

    let inst = result.expect("should resolve Show Bool");
    match inst.kind() {
        clean_kernel::expr::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("instShowBool"));
        }
        _ => panic!("expected Const, got {inst:?}"),
    }
}

// ==========================================================================
// Negative cache
// ==========================================================================

#[test]
fn test_resolve_negative_cache() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    setup_simple_instance(&mut table, "Add", "Nat", "instAddNat", DEFAULT_PRIORITY);

    let config = ResolutionConfig::default();
    let mut state = ResolutionState::new();

    // First attempt: Add Bool (fails, gets cached as None)
    let goal = class_app("Add", "Bool");
    let result1 = resolve_instance(&goal, &table, &config, &mut state);
    assert!(result1.is_err());
    let trace_len_after_first = state.trace.len();

    // Second attempt: same goal, should hit negative cache
    let result2 = resolve_instance(&goal, &table, &config, &mut state);
    assert!(result2.is_err());
    // No new trace entries from cached negative result
    assert_eq!(state.trace.len(), trace_len_after_first);
}

// ==========================================================================
// Error Display
// ==========================================================================

#[test]
fn test_resolution_error_display() {
    let err = ResolutionError::NoInstance(Name::from_string("Add"));
    assert_eq!(err.to_string(), "No instance found for class `Add`");

    let err = ResolutionError::MaxDepthExceeded(32);
    assert_eq!(
        err.to_string(),
        "Instance resolution exceeded maximum depth (32)"
    );

    let err = ResolutionError::MaxHeartbeatsExceeded(10000);
    assert_eq!(
        err.to_string(),
        "Instance resolution exceeded maximum heartbeats (10000)"
    );

    let err = ResolutionError::NotClassApplication;
    assert_eq!(err.to_string(), "Goal type is not a class application");

    let err = ResolutionError::UnregisteredClass(Name::from_string("Foo"));
    assert_eq!(err.to_string(), "Class `Foo` is not registered");

    let err = ResolutionError::UnificationFailed {
        class_name: Name::from_string("Add"),
        candidate_count: 3,
    };
    assert_eq!(
        err.to_string(),
        "Unification failed for all 3 candidates of class `Add`"
    );
}
