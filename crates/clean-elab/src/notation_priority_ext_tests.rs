// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended notation priority resolution.

use super::notation_priority::{Associativity, MixfixPattern, NotationPriority, PriorityEntry};
use super::notation_priority_ext::*;

// ============================================================================
// PriorityResolutionError
// ============================================================================

#[test]
fn test_error_cyclic_order_display() {
    let e = PriorityResolutionError::CyclicOrder(NotationPriority::ADD);
    assert!(e.to_string().contains("cycle"));
    assert!(e.to_string().contains("65"));
}

#[test]
fn test_error_ambiguous_parse_display() {
    let e = PriorityResolutionError::AmbiguousParse {
        token: "+".to_owned(),
        priority: NotationPriority::ADD,
        candidates: vec!["a".to_owned(), "b".to_owned()],
    };
    let s = e.to_string();
    assert!(s.contains("+"));
    assert!(s.contains("a"));
    assert!(s.contains("b"));
}

#[test]
fn test_error_ambiguous_parse_empty_candidates() {
    let e = PriorityResolutionError::AmbiguousParse {
        token: "+".to_owned(),
        priority: NotationPriority::ADD,
        candidates: vec![],
    };
    let s = e.to_string();
    assert!(s.contains("+"));
}

// ============================================================================
// PriorityLattice - basic
// ============================================================================

#[test]
fn test_lattice_empty() {
    let lat = PriorityLattice::new();
    assert!(lat.priorities().is_empty());
}

#[test]
fn test_lattice_insert_and_priorities() {
    let mut lat = PriorityLattice::new();
    lat.insert(NotationPriority::ADD);
    lat.insert(NotationPriority::MUL);
    let priorities = lat.priorities();
    assert_eq!(priorities.len(), 2);
}

#[test]
fn test_lattice_declare_tighter() {
    let mut lat = PriorityLattice::new();
    lat.declare_tighter(NotationPriority::MUL, NotationPriority::ADD)
        .expect("should succeed");
    assert!(lat.is_tighter_than(NotationPriority::MUL, NotationPriority::ADD));
    assert!(!lat.is_tighter_than(NotationPriority::ADD, NotationPriority::MUL));
}

#[test]
fn test_lattice_declare_tighter_self_is_cycle() {
    let mut lat = PriorityLattice::new();
    let err = lat
        .declare_tighter(NotationPriority::ADD, NotationPriority::ADD)
        .unwrap_err();
    assert!(matches!(err, PriorityResolutionError::CyclicOrder(_)));
}

#[test]
fn test_lattice_cycle_detection() {
    let mut lat = PriorityLattice::new();
    let p10 = NotationPriority::new(10);
    let p20 = NotationPriority::new(20);
    let p30 = NotationPriority::new(30);
    lat.declare_tighter(p30, p20).unwrap();
    lat.declare_tighter(p20, p10).unwrap();
    let err = lat.declare_tighter(p10, p30).unwrap_err();
    assert!(matches!(err, PriorityResolutionError::CyclicOrder(_)));
}

#[test]
fn test_lattice_transitive_closure() {
    let mut lat = PriorityLattice::new();
    let p1 = NotationPriority::new(1);
    let p2 = NotationPriority::new(2);
    let p3 = NotationPriority::new(3);
    lat.declare_tighter(p3, p2).unwrap();
    lat.declare_tighter(p2, p1).unwrap();
    // Transitive: 3 > 1
    assert!(lat.is_tighter_than(p3, p1));
}

#[test]
fn test_lattice_compare_equal() {
    let lat = PriorityLattice::new();
    assert_eq!(
        lat.compare(NotationPriority::ADD, NotationPriority::ADD),
        Some(std::cmp::Ordering::Equal)
    );
}

#[test]
fn test_lattice_compare_greater() {
    let mut lat = PriorityLattice::new();
    lat.declare_tighter(NotationPriority::MUL, NotationPriority::ADD)
        .unwrap();
    assert_eq!(
        lat.compare(NotationPriority::MUL, NotationPriority::ADD),
        Some(std::cmp::Ordering::Greater),
    );
}

#[test]
fn test_lattice_compare_less() {
    let mut lat = PriorityLattice::new();
    lat.declare_tighter(NotationPriority::MUL, NotationPriority::ADD)
        .unwrap();
    assert_eq!(
        lat.compare(NotationPriority::ADD, NotationPriority::MUL),
        Some(std::cmp::Ordering::Less),
    );
}

#[test]
fn test_lattice_compare_incomparable() {
    let mut lat = PriorityLattice::new();
    let p10 = NotationPriority::new(10);
    let p20 = NotationPriority::new(20);
    lat.insert(p10);
    lat.insert(p20);
    // No edge declared, so incomparable.
    assert_eq!(lat.compare(p10, p20), None);
}

#[test]
fn test_lattice_from_entries() {
    let entries = vec![
        PriorityEntry::new(
            "add",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Left,
        ),
        PriorityEntry::new(
            "mul",
            MixfixPattern::infix("*"),
            NotationPriority::MUL,
            Associativity::Left,
        ),
    ];
    let lat = PriorityLattice::from_entries(&entries);
    // MUL (70) > ADD (65) since from_entries orders by numeric value.
    assert!(lat.is_tighter_than(NotationPriority::MUL, NotationPriority::ADD));
}

#[test]
fn test_lattice_diamond_no_cycle() {
    let mut lat = PriorityLattice::new();
    let p1 = NotationPriority::new(1);
    let p2 = NotationPriority::new(2);
    let p3 = NotationPriority::new(3);
    let p4 = NotationPriority::new(4);
    lat.declare_tighter(p4, p2).unwrap();
    lat.declare_tighter(p4, p3).unwrap();
    lat.declare_tighter(p2, p1).unwrap();
    lat.declare_tighter(p3, p1).unwrap();
    assert!(lat.is_tighter_than(p4, p1));
    // p2 and p3 are incomparable.
    assert_eq!(lat.compare(p2, p3), None);
}

// ============================================================================
// PriorityConflictKind
// ============================================================================

#[test]
fn test_conflict_kind_equality() {
    assert_eq!(
        PriorityConflictKind::AssociativityMismatch,
        PriorityConflictKind::AssociativityMismatch
    );
    assert_ne!(
        PriorityConflictKind::AssociativityMismatch,
        PriorityConflictKind::PriorityAmbiguity
    );
    assert_ne!(
        PriorityConflictKind::ScopeShadowing,
        PriorityConflictKind::NamespaceOverride
    );
}

#[test]
fn test_conflict_kind_all_variants_distinct() {
    let kinds = [
        PriorityConflictKind::AssociativityMismatch,
        PriorityConflictKind::PriorityAmbiguity,
        PriorityConflictKind::IncomparablePriority,
        PriorityConflictKind::OverlappingPattern,
        PriorityConflictKind::ScopeShadowing,
        PriorityConflictKind::NamespaceOverride,
    ];
    for i in 0..kinds.len() {
        for j in (i + 1)..kinds.len() {
            assert_ne!(kinds[i], kinds[j]);
        }
    }
}

// ============================================================================
// NamespacePriorityOverride
// ============================================================================

#[test]
fn test_ns_override_basic() {
    let ovr = NamespacePriorityOverride::new("Nat");
    assert_eq!(ovr.namespace, "Nat");
    assert!(ovr.default_priority.is_none());
    assert!(ovr.token_priorities.is_empty());
    assert!(ovr.shadow_tokens.is_empty());
}

#[test]
fn test_ns_override_with_default_priority() {
    let ovr =
        NamespacePriorityOverride::new("Nat").with_default_priority(NotationPriority::new(80));
    assert_eq!(ovr.default_priority, Some(NotationPriority::new(80)));
}

#[test]
fn test_ns_override_with_token_priority() {
    let ovr =
        NamespacePriorityOverride::new("Nat").with_token_priority("+", NotationPriority::new(90));
    assert_eq!(
        ovr.token_priorities.get("+"),
        Some(&NotationPriority::new(90))
    );
}

#[test]
fn test_ns_override_with_shadow_token() {
    let ovr = NamespacePriorityOverride::new("Nat").with_shadow_token("+");
    assert!(ovr.shadow_tokens.contains("+"));
}

#[test]
fn test_ns_override_chained_builders() {
    let ovr = NamespacePriorityOverride::new("Nat")
        .with_default_priority(NotationPriority::new(50))
        .with_token_priority("+", NotationPriority::new(80))
        .with_shadow_token("*");
    assert_eq!(ovr.default_priority, Some(NotationPriority::new(50)));
    assert!(ovr.token_priorities.contains_key("+"));
    assert!(ovr.shadow_tokens.contains("*"));
}

// ============================================================================
// patterns_overlap
// ============================================================================

#[test]
fn test_patterns_overlap_same_infix() {
    let a = MixfixPattern::infix("+");
    let b = MixfixPattern::infix("+");
    assert!(patterns_overlap(&a, &b));
}

#[test]
fn test_patterns_overlap_different_token() {
    let a = MixfixPattern::infix("+");
    let b = MixfixPattern::infix("*");
    assert!(!patterns_overlap(&a, &b));
}

#[test]
fn test_patterns_overlap_different_arity() {
    let a = MixfixPattern::infix("+");
    let b = MixfixPattern::prefix("+");
    // infix has arity 2, prefix has arity 1.
    assert!(!patterns_overlap(&a, &b));
}

// ============================================================================
// analyze_priority_conflicts
// ============================================================================

#[test]
fn test_analyze_no_conflicts() {
    let entries = vec![
        PriorityEntry::new(
            "add",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Left,
        ),
        PriorityEntry::new(
            "mul",
            MixfixPattern::infix("*"),
            NotationPriority::MUL,
            Associativity::Left,
        ),
    ];
    let lat = PriorityLattice::from_entries(&entries);
    let conflicts = analyze_priority_conflicts(&entries, &lat);
    assert!(conflicts.is_empty());
}

#[test]
fn test_analyze_assoc_mismatch() {
    let entries = vec![
        PriorityEntry::new(
            "left",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Left,
        ),
        PriorityEntry::new(
            "right",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Right,
        ),
    ];
    let lat = PriorityLattice::from_entries(&entries);
    let conflicts = analyze_priority_conflicts(&entries, &lat);
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::AssociativityMismatch));
}

#[test]
fn test_analyze_priority_ambiguity() {
    let entries = vec![
        PriorityEntry::new(
            "a",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Left,
        ),
        PriorityEntry::new(
            "b",
            MixfixPattern::infix("+"),
            NotationPriority::ADD,
            Associativity::Left,
        ),
    ];
    let lat = PriorityLattice::from_entries(&entries);
    let conflicts = analyze_priority_conflicts(&entries, &lat);
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::PriorityAmbiguity));
}

#[test]
fn test_analyze_incomparable_priority() {
    let entries = vec![
        PriorityEntry::new(
            "a",
            MixfixPattern::infix("+"),
            NotationPriority::new(10),
            Associativity::Left,
        ),
        PriorityEntry::new(
            "b",
            MixfixPattern::infix("+"),
            NotationPriority::new(20),
            Associativity::Left,
        ),
    ];
    // Empty lattice: 10 and 20 are incomparable.
    let lat = PriorityLattice::new();
    let conflicts = analyze_priority_conflicts(&entries, &lat);
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::IncomparablePriority));
}

#[test]
fn test_analyze_overlapping_pattern() {
    let entries = vec![
        PriorityEntry::new(
            "a",
            MixfixPattern::infix("+"),
            NotationPriority::new(10),
            Associativity::Left,
        ),
        PriorityEntry::new(
            "b",
            MixfixPattern::infix("+"),
            NotationPriority::new(20),
            Associativity::Left,
        ),
    ];
    let mut lat = PriorityLattice::new();
    lat.declare_tighter(NotationPriority::new(20), NotationPriority::new(10))
        .unwrap();
    let conflicts = analyze_priority_conflicts(&entries, &lat);
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::OverlappingPattern));
}

// ============================================================================
// disambiguate_by_priority
// ============================================================================

#[test]
fn test_disambiguate_empty() {
    let lat = PriorityLattice::new();
    let result = disambiguate_by_priority("+", &[], &lat);
    assert!(result.unwrap().is_none());
}

#[test]
fn test_disambiguate_single() {
    let entry = PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    );
    let lat = PriorityLattice::new();
    let result = disambiguate_by_priority("+", &[&entry], &lat).unwrap();
    assert_eq!(result.unwrap().name(), "add");
}

#[test]
fn test_disambiguate_clear_winner() {
    let low = PriorityEntry::new(
        "low",
        MixfixPattern::infix("+"),
        NotationPriority::new(10),
        Associativity::Left,
    );
    let high = PriorityEntry::new(
        "high",
        MixfixPattern::infix("+"),
        NotationPriority::new(90),
        Associativity::Left,
    );
    let mut lat = PriorityLattice::new();
    lat.declare_tighter(NotationPriority::new(90), NotationPriority::new(10))
        .unwrap();
    let result = disambiguate_by_priority("+", &[&low, &high], &lat).unwrap();
    assert_eq!(result.unwrap().name(), "high");
}

#[test]
fn test_disambiguate_ambiguous_returns_error() {
    let a = PriorityEntry::new(
        "a",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    );
    let b = PriorityEntry::new(
        "b",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    );
    let lat = PriorityLattice::new();
    let err = disambiguate_by_priority("+", &[&a, &b], &lat).unwrap_err();
    assert!(matches!(
        err,
        PriorityResolutionError::AmbiguousParse { .. }
    ));
}

// ============================================================================
// conflicts_to_diagnostics
// ============================================================================

#[test]
fn test_conflicts_to_diagnostics_empty() {
    assert!(conflicts_to_diagnostics(&[]).is_empty());
}

#[test]
fn test_conflicts_to_diagnostics_with_priority() {
    let conflict = ExtendedConflict {
        kind: PriorityConflictKind::AssociativityMismatch,
        token: "+".to_owned(),
        first: "a".to_owned(),
        second: "b".to_owned(),
        priority: Some(NotationPriority::ADD),
        namespaces: std::collections::BTreeSet::new(),
        suggestions: vec!["fix it".to_owned()],
        base_conflict: None,
    };
    let diags = conflicts_to_diagnostics(&[conflict]);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].kind, PriorityConflictKind::AssociativityMismatch);
    assert!(diags[0].message.contains("65"));
    assert!(diags[0].message.contains("+"));
}

#[test]
fn test_conflicts_to_diagnostics_without_priority() {
    let conflict = ExtendedConflict {
        kind: PriorityConflictKind::IncomparablePriority,
        token: "*".to_owned(),
        first: "x".to_owned(),
        second: "y".to_owned(),
        priority: None,
        namespaces: std::collections::BTreeSet::new(),
        suggestions: vec![],
        base_conflict: None,
    };
    let diags = conflicts_to_diagnostics(&[conflict]);
    assert_eq!(diags.len(), 1);
    assert!(diags[0].message.contains("*"));
}

// ============================================================================
// build_priority_lattice
// ============================================================================

#[test]
fn test_build_priority_lattice() {
    let entries = vec![
        PriorityEntry::new(
            "a",
            MixfixPattern::infix("+"),
            NotationPriority::new(10),
            Associativity::Left,
        ),
        PriorityEntry::new(
            "b",
            MixfixPattern::infix("*"),
            NotationPriority::new(20),
            Associativity::Left,
        ),
        PriorityEntry::new(
            "c",
            MixfixPattern::prefix("-"),
            NotationPriority::new(30),
            Associativity::None,
        ),
    ];
    let lat = build_priority_lattice(&entries);
    assert!(lat.is_tighter_than(NotationPriority::new(30), NotationPriority::new(10)));
    assert!(lat.is_tighter_than(NotationPriority::new(20), NotationPriority::new(10)));
}

// ============================================================================
// ExtendedPriorityResolver - construction
// ============================================================================

#[test]
fn test_ext_resolver_empty() {
    let r = ExtendedPriorityResolver::new();
    assert!(r.diagnostics().is_empty());
}

#[test]
fn test_ext_resolver_with_lattice() {
    let lat = PriorityLattice::new();
    let r = ExtendedPriorityResolver::with_lattice(lat);
    assert!(r.diagnostics().is_empty());
}

// ============================================================================
// ExtendedPriorityResolver - registration
// ============================================================================

#[test]
fn test_ext_resolver_register() {
    let mut r = ExtendedPriorityResolver::new();
    let idx = r.register(PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    assert_eq!(idx, 0);
}

#[test]
fn test_ext_resolver_register_multiple() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    let idx = r.register(PriorityEntry::new(
        "mul",
        MixfixPattern::infix("*"),
        NotationPriority::MUL,
        Associativity::Left,
    ));
    assert_eq!(idx, 1);
}

// ============================================================================
// ExtendedPriorityResolver - namespace
// ============================================================================

#[test]
fn test_ext_resolver_enter_exit_namespace() {
    let mut r = ExtendedPriorityResolver::new();
    r.enter_namespace("Nat", false);
    r.register(PriorityEntry::new(
        "Nat.add",
        MixfixPattern::infix("+"),
        NotationPriority::new(80),
        Associativity::Left,
    ));
    r.exit_namespace();
}

#[test]
fn test_ext_resolver_namespace_override() {
    let mut r = ExtendedPriorityResolver::new();
    r.register_namespace_override(
        NamespacePriorityOverride::new("Nat").with_token_priority("+", NotationPriority::new(90)),
    );
    r.register(PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.enter_namespace("Nat", false);
    let result = r.resolve("+").unwrap();
    assert!(result.is_some());
}

// ============================================================================
// ExtendedPriorityResolver - resolve
// ============================================================================

#[test]
fn test_ext_resolver_resolve_empty() {
    let mut r = ExtendedPriorityResolver::new();
    let result = r.resolve("+").unwrap();
    assert!(result.is_none());
}

#[test]
fn test_ext_resolver_resolve_single() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    let result = r.resolve("+").unwrap();
    assert_eq!(result.unwrap().name(), "add");
}

#[test]
fn test_ext_resolver_resolve_ambiguous() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "a",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.register(PriorityEntry::new(
        "b",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    let result = r.resolve("+");
    assert!(result.is_err());
}

// ============================================================================
// ExtendedPriorityResolver - analyze_conflicts
// ============================================================================

#[test]
fn test_ext_resolver_analyze_conflicts_clean() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.register(PriorityEntry::new(
        "mul",
        MixfixPattern::infix("*"),
        NotationPriority::MUL,
        Associativity::Left,
    ));
    assert!(r.analyze_conflicts().is_empty());
}

#[test]
fn test_ext_resolver_analyze_conflicts_assoc_mismatch() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "left",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.register(PriorityEntry::new(
        "right",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Right,
    ));
    let conflicts = r.analyze_conflicts();
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::AssociativityMismatch));
}

#[test]
fn test_ext_resolver_diagnostics_populated() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "left",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.register(PriorityEntry::new(
        "right",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Right,
    ));
    assert!(!r.diagnostics().is_empty());
}

#[test]
fn test_ext_resolver_scope_shadow_conflict() {
    let mut r = ExtendedPriorityResolver::new();
    r.register(PriorityEntry::new(
        "outer.add",
        MixfixPattern::infix("+"),
        NotationPriority::ADD,
        Associativity::Left,
    ));
    r.register_namespace_override(NamespacePriorityOverride::new("Nat").with_shadow_token("+"));
    r.enter_namespace("Nat", false);
    r.register(PriorityEntry::new(
        "Nat.add",
        MixfixPattern::infix("+"),
        NotationPriority::new(80),
        Associativity::Left,
    ));
    let conflicts = r.analyze_conflicts();
    assert!(conflicts
        .iter()
        .any(|c| c.kind == PriorityConflictKind::ScopeShadowing));
}
