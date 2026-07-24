// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for coercion insertion module.

use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use super::{
    apply_coercion, apply_coercion_path, head_type_name, try_coerce, CoercionEntry, CoercionKind,
    CoercionPath, CoercionRegistry, MAX_COERCION_CHAIN_LENGTH,
};

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

// ============================================================================
// Registry: construction and registration
// ============================================================================

#[test]
fn test_registry_new_is_empty() {
    let reg = CoercionRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
}

#[test]
fn test_registry_register_single_coercion() {
    let mut reg = CoercionRegistry::new();
    let entry = mk_direct("Nat.toInt", "Nat", "Int");
    reg.register(entry).expect("registration should succeed");
    assert_eq!(reg.len(), 1);
    assert!(!reg.is_empty());
}

#[test]
fn test_registry_register_duplicate_returns_error() {
    let mut reg = CoercionRegistry::new();
    let e1 = mk_direct("Nat.toInt", "Nat", "Int");
    let e2 = mk_direct("Nat.toInt2", "Nat", "Int");
    reg.register(e1).expect("first should succeed");
    let result = reg.register(e2);
    assert!(
        result.is_err(),
        "duplicate (source,target) pair should fail"
    );
}

#[test]
fn test_registry_register_different_pairs_succeeds() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("Nat.toInt", "Nat", "Int"))
        .expect("should succeed");
    reg.register(mk_direct("Int.toRat", "Int", "Rat"))
        .expect("should succeed");
    reg.register(mk_direct("Bool.toNat", "Bool", "Nat"))
        .expect("should succeed");
    assert_eq!(reg.len(), 3);
}

#[test]
fn test_registry_is_coercion_by_name() {
    let mut reg = CoercionRegistry::new();
    let name = Name::from_string("Nat.toInt");
    reg.register(mk_direct("Nat.toInt", "Nat", "Int"))
        .expect("should succeed");
    assert!(reg.is_coercion(&name));
    assert!(!reg.is_coercion(&Name::from_string("nonexistent")));
}

// ============================================================================
// Registry: with_builtins
// ============================================================================

#[test]
fn test_with_builtins_has_nat_to_int() {
    let reg = CoercionRegistry::with_builtins();
    assert!(!reg.is_empty());
    let entry = reg
        .find_direct(&Name::from_string("Nat"), &Name::from_string("Int"))
        .expect("Nat->Int should be registered");
    assert_eq!(entry.kind, CoercionKind::BuiltinUpcast);
    assert_eq!(entry.fn_name, Name::from_string("Int.ofNat"));
}

// ============================================================================
// Registry: direct lookup
// ============================================================================

#[test]
fn test_find_direct_existing() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B"))
        .expect("should succeed");
    let found = reg.find_direct(&Name::from_string("A"), &Name::from_string("B"));
    assert!(found.is_some());
    assert_eq!(found.unwrap().fn_name, Name::from_string("f"));
}

#[test]
fn test_find_direct_missing() {
    let reg = CoercionRegistry::new();
    let found = reg.find_direct(&Name::from_string("X"), &Name::from_string("Y"));
    assert!(found.is_none());
}

// ============================================================================
// Registry: chain resolution (BFS)
// ============================================================================

#[test]
fn test_find_chain_direct_path() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B"))
        .expect("should succeed");
    let path = reg
        .find_chain(&Name::from_string("A"), &Name::from_string("B"))
        .expect("should find direct path");
    assert_eq!(path.len(), 1);
    assert_eq!(path.steps[0].fn_name, Name::from_string("f"));
}

#[test]
fn test_find_chain_two_step() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B"))
        .expect("should succeed");
    reg.register(mk_direct("f_bc", "B", "C"))
        .expect("should succeed");
    let path = reg
        .find_chain(&Name::from_string("A"), &Name::from_string("C"))
        .expect("should find 2-step path");
    assert_eq!(path.len(), 2);
    assert_eq!(path.steps[0].fn_name, Name::from_string("f_ab"));
    assert_eq!(path.steps[1].fn_name, Name::from_string("f_bc"));
}

#[test]
fn test_find_chain_three_step() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B"))
        .expect("should succeed");
    reg.register(mk_direct("f2", "B", "C"))
        .expect("should succeed");
    reg.register(mk_direct("f3", "C", "D"))
        .expect("should succeed");
    let path = reg
        .find_chain(&Name::from_string("A"), &Name::from_string("D"))
        .expect("should find 3-step path");
    assert_eq!(path.len(), 3);
}

#[test]
fn test_find_chain_no_path() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f", "A", "B"))
        .expect("should succeed");
    let result = reg.find_chain(&Name::from_string("B"), &Name::from_string("A"));
    assert!(result.is_none(), "no reverse path should exist");
}

#[test]
fn test_find_chain_cycle_detection() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f_ab", "A", "B"))
        .expect("should succeed");
    reg.register(mk_direct("f_ba", "B", "A"))
        .expect("should succeed");
    // No path from A to C even though there's a cycle A<->B
    let result = reg.find_chain(&Name::from_string("A"), &Name::from_string("C"));
    assert!(result.is_none());
}

#[test]
fn test_find_chain_prefers_shortest_path() {
    let mut reg = CoercionRegistry::new();
    // Direct path A->C
    reg.register(mk_direct("f_ac", "A", "C"))
        .expect("should succeed");
    // Longer path A->B->C
    reg.register(mk_direct("f_ab", "A", "B"))
        .expect("should succeed");
    reg.register(mk_direct("f_bc", "B", "C"))
        .expect("should succeed");
    let path = reg
        .find_chain(&Name::from_string("A"), &Name::from_string("C"))
        .expect("should find path");
    // BFS guarantees shortest path first
    assert_eq!(path.len(), 1);
    assert_eq!(path.steps[0].fn_name, Name::from_string("f_ac"));
}

#[test]
fn test_find_chain_respects_max_length() {
    let mut reg = CoercionRegistry::new();
    // Build a long chain: T0 -> T1 -> T2 -> ... -> T(MAX+1)
    for i in 0..=MAX_COERCION_CHAIN_LENGTH {
        let src = format!("T{i}");
        let tgt = format!("T{}", i + 1);
        let fn_name = format!("coe_{i}_{}", i + 1);
        reg.register(mk_direct(&fn_name, &src, &tgt))
            .expect("should succeed");
    }
    // Path of exactly MAX_COERCION_CHAIN_LENGTH should be found
    let target = format!("T{MAX_COERCION_CHAIN_LENGTH}");
    let path = reg.find_chain(&Name::from_string("T0"), &Name::from_string(&target));
    assert!(path.is_some(), "path of max length should be found");
    assert_eq!(path.unwrap().len(), MAX_COERCION_CHAIN_LENGTH);

    // Path of MAX+1 should NOT be found
    let too_far = format!("T{}", MAX_COERCION_CHAIN_LENGTH + 1);
    let path2 = reg.find_chain(&Name::from_string("T0"), &Name::from_string(&too_far));
    assert!(
        path2.is_none(),
        "path exceeding max length should not be found"
    );
}

// ============================================================================
// CoercionPath
// ============================================================================

#[test]
fn test_coercion_path_empty() {
    let path = CoercionPath { steps: vec![] };
    assert!(path.is_empty());
    assert_eq!(path.len(), 0);
}

#[test]
fn test_coercion_path_nonempty() {
    let path = CoercionPath {
        steps: vec![mk_direct("f", "A", "B")],
    };
    assert!(!path.is_empty());
    assert_eq!(path.len(), 1);
}

// ============================================================================
// Coercion application
// ============================================================================

#[test]
fn test_apply_coercion_wraps_expression() {
    let inner = Expr::const_str("x");
    let coerced = apply_coercion(&Name::from_string("Nat.toInt"), inner);
    assert!(coerced.is_app(), "result should be an application");
    let head = coerced.get_app_fn();
    assert!(head.is_const(), "head should be the coercion constant");
}

#[test]
fn test_apply_coercion_path_empty_is_identity() {
    let expr = Expr::const_str("x");
    let path = CoercionPath { steps: vec![] };
    let result = apply_coercion_path(&path, expr.clone());
    // Empty path should return the same expression structure
    assert_eq!(format!("{result:?}"), format!("{expr:?}"));
}

#[test]
fn test_apply_coercion_path_single_step() {
    let expr = Expr::const_str("n");
    let path = CoercionPath {
        steps: vec![mk_direct("Int.ofNat", "Nat", "Int")],
    };
    let result = apply_coercion_path(&path, expr);
    assert!(result.is_app());
}

#[test]
fn test_apply_coercion_path_multi_step_nesting() {
    let expr = Expr::const_str("n");
    let path = CoercionPath {
        steps: vec![
            mk_direct("Int.ofNat", "Nat", "Int"),
            mk_direct("Rat.ofInt", "Int", "Rat"),
        ],
    };
    let result = apply_coercion_path(&path, expr);
    // Should be Rat.ofInt (Int.ofNat n) — outer app is Rat.ofInt
    assert!(result.is_app());
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    // The argument should itself be an application (Int.ofNat n)
    assert!(args[0].is_app());
}

// ============================================================================
// Head type extraction
// ============================================================================

#[test]
fn test_head_type_name_const() {
    let ty = Expr::const_str("Nat");
    assert_eq!(head_type_name(&ty), Some(Name::from_string("Nat")));
}

#[test]
fn test_head_type_name_app() {
    let ty = Expr::app(Expr::const_str("List"), Expr::const_str("Nat"));
    assert_eq!(head_type_name(&ty), Some(Name::from_string("List")));
}

#[test]
fn test_head_type_name_nested_app() {
    let ty = Expr::app(
        Expr::app(Expr::const_str("Prod"), Expr::const_str("Nat")),
        Expr::const_str("Int"),
    );
    assert_eq!(head_type_name(&ty), Some(Name::from_string("Prod")));
}

#[test]
fn test_head_type_name_bvar_returns_none() {
    let ty = Expr::bvar(0);
    assert_eq!(head_type_name(&ty), None);
}

// ============================================================================
// try_coerce integration
// ============================================================================

#[test]
fn test_try_coerce_direct_success() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("Int.ofNat", "Nat", "Int"))
        .expect("should succeed");
    let expr = Expr::const_str("n");
    let actual = Expr::const_str("Nat");
    let expected = Expr::const_str("Int");
    let result = try_coerce(&reg, expr, &actual, &expected);
    assert!(result.is_ok(), "coercion should succeed");
    assert!(result.unwrap().is_app());
}

#[test]
fn test_try_coerce_no_coercion_returns_error() {
    let reg = CoercionRegistry::new();
    let expr = Expr::const_str("x");
    let actual = Expr::const_str("String");
    let expected = Expr::const_str("Nat");
    let result = try_coerce(&reg, expr, &actual, &expected);
    assert!(result.is_err());
}

#[test]
fn test_try_coerce_non_const_head_returns_error() {
    let reg = CoercionRegistry::new();
    let expr = Expr::const_str("x");
    let actual = Expr::bvar(0);
    let expected = Expr::const_str("Nat");
    let result = try_coerce(&reg, expr, &actual, &expected);
    assert!(result.is_err());
}

#[test]
fn test_try_coerce_chain_success() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("Int.ofNat", "Nat", "Int"))
        .expect("should succeed");
    reg.register(mk_direct("Rat.ofInt", "Int", "Rat"))
        .expect("should succeed");
    let expr = Expr::const_str("n");
    let actual = Expr::const_str("Nat");
    let expected = Expr::const_str("Rat");
    let result = try_coerce(&reg, expr, &actual, &expected);
    assert!(result.is_ok(), "chain coercion should succeed");
}

// ============================================================================
// CoercionKind variants
// ============================================================================

#[test]
fn test_coercion_kind_equality() {
    assert_eq!(CoercionKind::Direct, CoercionKind::Direct);
    assert_eq!(CoercionKind::CoeTC, CoercionKind::CoeTC);
    assert_ne!(CoercionKind::Direct, CoercionKind::CoeTC);
    assert_ne!(CoercionKind::BuiltinUpcast, CoercionKind::CoeHTCoe);
}

// ============================================================================
// Registry iteration
// ============================================================================

#[test]
fn test_registry_iter_yields_all_entries() {
    let mut reg = CoercionRegistry::new();
    reg.register(mk_direct("f1", "A", "B"))
        .expect("should succeed");
    reg.register(mk_direct("f2", "B", "C"))
        .expect("should succeed");
    reg.register(mk_direct("f3", "C", "D"))
        .expect("should succeed");
    let names: Vec<Name> = reg.iter().map(|e| e.fn_name.clone()).collect();
    assert_eq!(names.len(), 3);
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_find_chain_source_equals_target_no_self_coercion() {
    let reg = CoercionRegistry::new();
    // No self-coercion registered, so no path.
    let result = reg.find_chain(&Name::from_string("Nat"), &Name::from_string("Nat"));
    assert!(result.is_none());
}

#[test]
fn test_register_builtin_upcast() {
    let mut reg = CoercionRegistry::new();
    reg.register_builtin_upcast("Float.ofNat", "Nat", "Float")
        .expect("should succeed");
    let entry = reg
        .find_direct(&Name::from_string("Nat"), &Name::from_string("Float"))
        .expect("should exist");
    assert_eq!(entry.kind, CoercionKind::BuiltinUpcast);
}
