// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended coercion analysis (coercion_ext2).

use clean_kernel::name::Name;

use crate::coercion::{CoercionEntry, CoercionKind, CoercionPath, CoercionRegistry};
use crate::coercion_ext2::{
    build_compatibility_matrix, compute_stats, default_cost, detect_conflicts, detect_cycles,
    find_optimal_path, find_optimal_path_with, path_cost, path_cost_with, to_dot, validate,
    validate_no_cycle, CoercionAnalysisError, CoercionCost, Compatibility,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_entry(fn_name: &str, source: &str, target: &str, kind: CoercionKind) -> CoercionEntry {
    CoercionEntry {
        fn_name: Name::from_string(fn_name),
        source: Name::from_string(source),
        target: Name::from_string(target),
        kind,
    }
}

fn mk_direct(fn_name: &str, source: &str, target: &str) -> CoercionEntry {
    mk_entry(fn_name, source, target, CoercionKind::Direct)
}

fn mk_builtin(fn_name: &str, source: &str, target: &str) -> CoercionEntry {
    mk_entry(fn_name, source, target, CoercionKind::BuiltinUpcast)
}

// ============================================================================
// CoercionCost
// ============================================================================

#[test]
fn test_cost_zero() {
    assert_eq!(CoercionCost::ZERO.value(), 0);
}

#[test]
fn test_cost_new_and_value() {
    let c = CoercionCost::new(42);
    assert_eq!(c.value(), 42);
}

#[test]
fn test_cost_saturating_add() {
    let a = CoercionCost::new(10);
    let b = CoercionCost::new(20);
    assert_eq!(a.saturating_add(b).value(), 30);
}

#[test]
fn test_cost_saturating_add_overflow() {
    let a = CoercionCost::new(u32::MAX);
    let b = CoercionCost::new(1);
    assert_eq!(a.saturating_add(b).value(), u32::MAX);
}

#[test]
fn test_cost_default_is_zero() {
    let c: CoercionCost = Default::default();
    assert_eq!(c, CoercionCost::ZERO);
}

#[test]
fn test_cost_ordering() {
    let low = CoercionCost::new(1);
    let high = CoercionCost::new(5);
    assert!(low < high);
}

// ============================================================================
// Default cost model
// ============================================================================

#[test]
fn test_default_cost_builtin_upcast() {
    assert_eq!(default_cost(&CoercionKind::BuiltinUpcast).value(), 1);
}

#[test]
fn test_default_cost_direct() {
    assert_eq!(default_cost(&CoercionKind::Direct).value(), 2);
}

#[test]
fn test_default_cost_coe_tc() {
    assert_eq!(default_cost(&CoercionKind::CoeTC).value(), 3);
}

#[test]
fn test_default_cost_coe_htcoe() {
    assert_eq!(default_cost(&CoercionKind::CoeHTCoe).value(), 4);
}

// ============================================================================
// Path cost
// ============================================================================

#[test]
fn test_path_cost_empty() {
    let path = CoercionPath { steps: vec![] };
    assert_eq!(path_cost(&path).value(), 0);
}

#[test]
fn test_path_cost_single_step() {
    let path = CoercionPath {
        steps: vec![mk_direct("f", "A", "B")],
    };
    assert_eq!(path_cost(&path).value(), 2);
}

#[test]
fn test_path_cost_multi_step_same_kind() {
    let path = CoercionPath {
        steps: vec![mk_direct("f", "A", "B"), mk_direct("g", "B", "C")],
    };
    assert_eq!(path_cost(&path).value(), 4);
}

#[test]
fn test_path_cost_mixed_kinds() {
    let path = CoercionPath {
        steps: vec![
            mk_builtin("upcast", "Nat", "Int"),
            mk_direct("toRat", "Int", "Rat"),
        ],
    };
    // builtin=1, direct=2
    assert_eq!(path_cost(&path).value(), 3);
}

#[test]
fn test_path_cost_with_custom_fn() {
    let path = CoercionPath {
        steps: vec![mk_direct("f", "A", "B"), mk_builtin("g", "B", "C")],
    };
    let cost = path_cost_with(&path, |_| CoercionCost::new(10));
    assert_eq!(cost.value(), 20);
}

// ============================================================================
// Statistics
// ============================================================================

#[test]
fn test_stats_empty_registry() {
    let reg = CoercionRegistry::new();
    let stats = compute_stats(&reg);
    assert_eq!(stats.total_coercions, 0);
    assert_eq!(stats.source_types, 0);
    assert_eq!(stats.target_types, 0);
    assert_eq!(stats.max_out_degree, 0);
    assert!(stats.max_out_degree_type.is_none());
    assert_eq!(stats.bidirectional_types, 0);
}

#[test]
fn test_stats_single_coercion() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("register ok");
    let stats = compute_stats(&reg);
    assert_eq!(stats.total_coercions, 1);
    assert_eq!(stats.source_types, 1);
    assert_eq!(stats.target_types, 1);
    assert_eq!(stats.max_out_degree, 1);
    assert_eq!(stats.bidirectional_types, 0);
}

#[test]
fn test_stats_by_kind_counts() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_builtin("f2", "Nat", "Int")).expect("ok");
    reg.register(mk_direct("f3", "B", "C")).expect("ok");
    let stats = compute_stats(&reg);
    assert_eq!(stats.by_kind.get(&CoercionKind::Direct), Some(&2));
    assert_eq!(stats.by_kind.get(&CoercionKind::BuiltinUpcast), Some(&1));
}

#[test]
fn test_stats_max_out_degree() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f3", "A", "D")).expect("ok");
    reg.register(mk_direct("f4", "B", "D")).expect("ok");
    let stats = compute_stats(&reg);
    assert_eq!(stats.max_out_degree, 3);
    assert_eq!(stats.max_out_degree_type, Some(name("A")));
}

#[test]
fn test_stats_bidirectional_types() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "B", "C")).expect("ok");
    let stats = compute_stats(&reg);
    // B is both a source and a target
    assert_eq!(stats.bidirectional_types, 1);
}

// ============================================================================
// Conflict detection
// ============================================================================

#[test]
fn test_no_conflicts_linear_chain() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let conflicts = detect_conflicts(&reg);
    assert!(conflicts.is_empty());
}

#[test]
fn test_conflict_diamond() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f3", "B", "D")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let conflicts = detect_conflicts(&reg);
    // A->D has two paths: A->B->D and A->C->D
    let ad_conflict = conflicts
        .iter()
        .find(|c| c.source == name("A") && c.target == name("D"));
    assert!(ad_conflict.is_some());
    assert_eq!(ad_conflict.expect("conflict exists").paths.len(), 2);
}

#[test]
fn test_conflict_diamond_true_ambiguity() {
    let mut reg = CoercionRegistry::new();
    // Both paths same kind (Direct), same length => same cost => true ambiguity
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f3", "B", "D")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let conflicts = detect_conflicts(&reg);
    let ad_conflict = conflicts
        .iter()
        .find(|c| c.source == name("A") && c.target == name("D"))
        .expect("conflict should exist");
    assert!(ad_conflict.is_true_ambiguity);
}

#[test]
fn test_conflict_resolvable_by_cost() {
    let mut reg = CoercionRegistry::new();
    // Path 1: A->B->D (builtin + builtin = cost 2)
    reg.register(mk_builtin("f1", "A", "B")).expect("ok");
    reg.register(mk_builtin("f3", "B", "D")).expect("ok");
    // Path 2: A->C->D (direct + direct = cost 4)
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let conflicts = detect_conflicts(&reg);
    let ad_conflict = conflicts
        .iter()
        .find(|c| c.source == name("A") && c.target == name("D"))
        .expect("conflict should exist");
    assert!(!ad_conflict.is_true_ambiguity);
}

// ============================================================================
// Optimal path selection
// ============================================================================

#[test]
fn test_optimal_path_single_step() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    let path = find_optimal_path(&reg, &name("A"), &name("B")).expect("should find path");
    assert_eq!(path.len(), 1);
    assert_eq!(path.steps[0].fn_name, name("f"));
}

#[test]
fn test_optimal_path_prefers_lower_cost() {
    let mut reg = CoercionRegistry::new();
    // Path 1: A->B->D via builtin (cost 1+1=2)
    reg.register(mk_builtin("f1", "A", "B")).expect("ok");
    reg.register(mk_builtin("f3", "B", "D")).expect("ok");
    // Path 2: A->C->D via direct (cost 2+2=4)
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let path = find_optimal_path(&reg, &name("A"), &name("D")).expect("should find cheaper path");
    assert_eq!(path.len(), 2);
    // The builtin path should win
    assert_eq!(path_cost(&path).value(), 2);
}

#[test]
fn test_optimal_path_no_path_error() {
    let reg = CoercionRegistry::new();
    let err = find_optimal_path(&reg, &name("A"), &name("B")).unwrap_err();
    assert!(matches!(err, CoercionAnalysisError::NoPath { .. }));
}

#[test]
fn test_optimal_path_ambiguous_error() {
    let mut reg = CoercionRegistry::new();
    // Diamond with equal costs => ambiguity
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f3", "B", "D")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let err = find_optimal_path(&reg, &name("A"), &name("D")).unwrap_err();
    assert!(matches!(
        err,
        CoercionAnalysisError::AmbiguousCoercion { count: 2, .. }
    ));
}

#[test]
fn test_optimal_path_with_custom_cost() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_builtin("f1", "A", "B")).expect("ok");
    reg.register(mk_builtin("f3", "B", "D")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");

    // Custom cost: Direct=1, BuiltinUpcast=10 (reverses preference)
    let path = find_optimal_path_with(&reg, &name("A"), &name("D"), |kind| match kind {
        CoercionKind::Direct => CoercionCost::new(1),
        CoercionKind::BuiltinUpcast => CoercionCost::new(10),
        _ => CoercionCost::new(5),
    })
    .expect("should find path");
    // Direct path (cost 1+1=2) should win over builtin (10+10=20)
    assert_eq!(path.steps[0].kind, CoercionKind::Direct);
}

// ============================================================================
// Cycle detection
// ============================================================================

#[test]
fn test_no_cycles_dag() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let cycles = detect_cycles(&reg);
    assert!(cycles.is_empty());
}

#[test]
fn test_cycle_self_loop() {
    // We need to bypass the registry's duplicate check by using different names
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "A")).expect("ok");
    let cycles = detect_cycles(&reg);
    assert!(!cycles.is_empty());
}

#[test]
fn test_cycle_three_nodes() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    reg.register(mk_direct("h", "C", "A")).expect("ok");
    let cycles = detect_cycles(&reg);
    assert!(!cycles.is_empty());
}

// ============================================================================
// Validate no cycle (pre-registration check)
// ============================================================================

#[test]
fn test_validate_no_cycle_safe() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    validate_no_cycle(&reg, &name("B"), &name("C")).expect("should be safe");
}

#[test]
fn test_validate_no_cycle_would_create_cycle() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let err = validate_no_cycle(&reg, &name("C"), &name("A")).unwrap_err();
    assert!(matches!(
        err,
        CoercionAnalysisError::WouldCreateCycle { .. }
    ));
}

// ============================================================================
// DOT graph visualization
// ============================================================================

#[test]
fn test_dot_empty_registry() {
    let reg = CoercionRegistry::new();
    let dot = to_dot(&reg);
    assert!(dot.contains("digraph coercions"));
    assert!(dot.contains("rankdir=LR"));
    assert!(dot.ends_with("}\n"));
}

#[test]
fn test_dot_single_edge() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    let dot = to_dot(&reg);
    assert!(dot.contains("\"A\" -> \"B\""));
    assert!(dot.contains("label=\"f\""));
    assert!(dot.contains("color=black"));
}

#[test]
fn test_dot_builtin_edge_green() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_builtin("Int.ofNat", "Nat", "Int"))
        .expect("ok");
    let dot = to_dot(&reg);
    assert!(dot.contains("color=green"));
}

#[test]
fn test_dot_multiple_edges() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let dot = to_dot(&reg);
    assert!(dot.contains("\"A\" -> \"B\""));
    assert!(dot.contains("\"B\" -> \"C\""));
}

// ============================================================================
// Compatibility matrix
// ============================================================================

#[test]
fn test_matrix_empty_registry() {
    let reg = CoercionRegistry::new();
    let matrix = build_compatibility_matrix(&reg, &[]);
    assert_eq!(matrix.type_count(), 0);
    assert_eq!(matrix.coercible_count(), 0);
}

#[test]
fn test_matrix_self_is_same() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[name("A"), name("B")]);
    assert_eq!(matrix.get(&name("A"), &name("A")), Compatibility::Same);
    assert_eq!(matrix.get(&name("B"), &name("B")), Compatibility::Same);
}

#[test]
fn test_matrix_direct_coercion() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[name("A"), name("B")]);
    assert!(matches!(
        matrix.get(&name("A"), &name("B")),
        Compatibility::Coercible(_)
    ));
}

#[test]
fn test_matrix_no_reverse_coercion() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[name("A"), name("B")]);
    assert_eq!(
        matrix.get(&name("B"), &name("A")),
        Compatibility::Incompatible
    );
}

#[test]
fn test_matrix_transitive_coercion() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[name("A"), name("B"), name("C")]);
    assert!(matches!(
        matrix.get(&name("A"), &name("C")),
        Compatibility::Coercible(_)
    ));
}

#[test]
fn test_matrix_auto_collect_types() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "X", "Y")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[]);
    assert_eq!(matrix.type_count(), 2);
    assert!(matches!(
        matrix.get(&name("X"), &name("Y")),
        Compatibility::Coercible(_)
    ));
}

#[test]
fn test_matrix_unknown_type_is_incompatible() {
    let reg = CoercionRegistry::new();
    let matrix = build_compatibility_matrix(&reg, &[name("A")]);
    assert_eq!(
        matrix.get(&name("A"), &name("Z")),
        Compatibility::Incompatible
    );
}

#[test]
fn test_matrix_coercible_count() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let matrix = build_compatibility_matrix(&reg, &[name("A"), name("B"), name("C")]);
    // A->B (1), B->C (1), A->C (transitive, 1) = 3 coercible pairs
    assert_eq!(matrix.coercible_count(), 3);
}

// ============================================================================
// Comprehensive validation
// ============================================================================

#[test]
fn test_validate_clean_registry() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "C")).expect("ok");
    let result = validate(&reg);
    assert!(result.is_valid());
    assert!(result.cycles.is_empty());
    assert_eq!(result.true_ambiguity_count(), 0);
    assert_eq!(result.stats.total_coercions, 2);
}

#[test]
fn test_validate_with_cycle_is_invalid() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B")).expect("ok");
    reg.register(mk_direct("g", "B", "A")).expect("ok");
    let result = validate(&reg);
    assert!(!result.cycles.is_empty());
    // Not necessarily invalid if no true ambiguity, but cycles exist.
    // is_valid() only checks cycles + ambiguity
    assert!(!result.is_valid());
}

#[test]
fn test_validate_diamond_with_ambiguity() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B")).expect("ok");
    reg.register(mk_direct("f2", "A", "C")).expect("ok");
    reg.register(mk_direct("f3", "B", "D")).expect("ok");
    reg.register(mk_direct("f4", "C", "D")).expect("ok");
    let result = validate(&reg);
    assert!(result.true_ambiguity_count() > 0);
    assert!(!result.is_valid());
}

#[test]
fn test_validate_empty_is_valid() {
    let reg = CoercionRegistry::new();
    let result = validate(&reg);
    assert!(result.is_valid());
    assert_eq!(result.stats.total_coercions, 0);
}

// ============================================================================
// Error type display
// ============================================================================

#[test]
fn test_error_display_cycle_detected() {
    let err = CoercionAnalysisError::CycleDetected {
        path: "A -> B -> A".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("cycle"));
    assert!(msg.contains("A -> B -> A"));
}

#[test]
fn test_error_display_no_path() {
    let err = CoercionAnalysisError::NoPath {
        from_type: "Nat".to_string(),
        to_type: "String".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("Nat"));
    assert!(msg.contains("String"));
}

#[test]
fn test_error_display_would_create_cycle() {
    let err = CoercionAnalysisError::WouldCreateCycle {
        from_type: "X".to_string(),
        to_type: "Y".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("cycle"));
}
