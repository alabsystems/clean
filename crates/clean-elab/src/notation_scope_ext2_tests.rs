// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended notation scope handling (`notation_scope_ext2`).

use clean_kernel::name::Name;

use crate::notation_scope_ext2::{
    NotationScope, NotationScopeError, NotationScopeRegistry2, ScopeStats, ScopedAbbreviation,
    ScopedNotation,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn notation(qname: &str, syntax: &str, expansion: &str, priority: u32) -> ScopedNotation {
    ScopedNotation::new(name(qname), syntax, expansion, priority)
}

fn abbrev(short: &str, expansion: &str, scope_name: &str) -> ScopedAbbreviation {
    ScopedAbbreviation::new(short, expansion, name(scope_name))
}

/// Build a registry with Nat and Int scopes pre-defined.
fn registry_with_nat_int() -> NotationScopeRegistry2 {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    reg.define_scope(name("Int"), None).unwrap();
    reg
}

// ===========================================================================
// 1. Scope definition
// ===========================================================================

#[test]
fn test_define_scope_basic() {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    assert!(reg.is_scope_defined(&name("Nat")));
    assert!(!reg.is_scope_defined(&name("Int")));
}

#[test]
fn test_define_scope_with_parent() {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    reg.define_scope(name("Nat.Lemma"), Some(name("Nat")))
        .unwrap();
    assert!(reg.is_scope_defined(&name("Nat.Lemma")));
    let scope = reg.get_scope(&name("Nat.Lemma")).unwrap();
    assert_eq!(scope.parent(), Some(&name("Nat")));
}

#[test]
fn test_define_scope_duplicate_rejected() {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    let err = reg.define_scope(name("Nat"), None);
    assert!(matches!(err, Err(NotationScopeError::DuplicateScope(_))));
}

#[test]
fn test_scope_count() {
    let mut reg = NotationScopeRegistry2::new();
    assert_eq!(reg.scope_count(), 0);
    reg.define_scope(name("A"), None).unwrap();
    reg.define_scope(name("B"), None).unwrap();
    assert_eq!(reg.scope_count(), 2);
}

// ===========================================================================
// 2. Scope activation / deactivation
// ===========================================================================

#[test]
fn test_activate_scope_basic() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    assert!(reg.is_scope_active(&name("Nat")));
    assert!(!reg.is_scope_active(&name("Int")));
}

#[test]
fn test_activate_nonexistent_scope_errors() {
    let mut reg = NotationScopeRegistry2::new();
    let err = reg.activate_scope(&name("Ghost"));
    assert!(matches!(err, Err(NotationScopeError::ScopeNotFound(_))));
}

#[test]
fn test_deactivate_scope_basic() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.deactivate_scope(&name("Nat")).unwrap();
    assert!(!reg.is_scope_active(&name("Nat")));
}

#[test]
fn test_deactivate_nonexistent_scope_errors() {
    let mut reg = NotationScopeRegistry2::new();
    let err = reg.deactivate_scope(&name("Ghost"));
    assert!(matches!(err, Err(NotationScopeError::ScopeNotFound(_))));
}

#[test]
fn test_deactivate_inactive_scope_is_noop() {
    let mut reg = registry_with_nat_int();
    // Not yet activated — deactivate should still succeed.
    reg.deactivate_scope(&name("Nat")).unwrap();
    assert!(!reg.is_scope_active(&name("Nat")));
}

#[test]
fn test_activate_scope_twice_moves_to_top() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    // Re-activate Nat: should move to top.
    reg.activate_scope(&name("Nat")).unwrap();
    let active = reg.active_scopes();
    assert_eq!(active.len(), 2);
    assert_eq!(active[1], name("Nat")); // top of stack
}

// ===========================================================================
// 3. Scope stacking (inner shadows outer)
// ===========================================================================

#[test]
fn test_scope_stacking_order() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    let active = reg.active_scopes();
    assert_eq!(active[0], name("Nat"));
    assert_eq!(active[1], name("Int"));
}

#[test]
fn test_scope_stacking_inner_shadows_outer() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    // Int is on top, should shadow Nat.
    let found = reg.lookup_notation("+").unwrap();
    assert_eq!(found.expansion, "Int.add");
}

// ===========================================================================
// 4. Notation lookup with scope resolution
// ===========================================================================

#[test]
fn test_lookup_notation_no_active_scopes() {
    let reg = registry_with_nat_int();
    assert!(reg.lookup_notation("+").is_none());
}

#[test]
fn test_lookup_notation_single_scope() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    let found = reg.lookup_notation("+").unwrap();
    assert_eq!(found.qualified_name, name("Nat.add"));
}

#[test]
fn test_lookup_notation_nonexistent_syntax() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    assert!(reg.lookup_notation("@#$").is_none());
}

#[test]
fn test_lookup_all_notations_multiple_scopes() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 70))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    let all = reg.lookup_all_notations("+");
    assert_eq!(all.len(), 2);
    // Sorted by priority descending.
    assert_eq!(all[0].priority, 70);
    assert_eq!(all[1].priority, 65);
}

// ===========================================================================
// 5. Scope-qualified notation names
// ===========================================================================

#[test]
fn test_qualified_name_nat_add_vs_int_add() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 70))
        .unwrap();
    let nat_notations = reg.scope_notations(&name("Nat"));
    assert_eq!(nat_notations.len(), 1);
    assert_eq!(nat_notations[0].qualified_name, name("Nat.add"));
    let int_notations = reg.scope_notations(&name("Int"));
    assert_eq!(int_notations[0].qualified_name, name("Int.add"));
}

// ===========================================================================
// 6. Default scope configuration
// ===========================================================================

#[test]
fn test_default_scopes_empty() {
    let reg = NotationScopeRegistry2::new();
    assert!(reg.default_scopes().is_empty());
}

#[test]
fn test_set_and_activate_defaults() {
    let mut reg = registry_with_nat_int();
    reg.set_default_scopes(vec![name("Nat")]);
    reg.activate_defaults();
    assert!(reg.is_scope_active(&name("Nat")));
    assert!(!reg.is_scope_active(&name("Int")));
}

#[test]
fn test_activate_defaults_skips_undefined() {
    let mut reg = registry_with_nat_int();
    reg.set_default_scopes(vec![name("Nat"), name("Ghost")]);
    reg.activate_defaults();
    assert!(reg.is_scope_active(&name("Nat")));
    // Ghost is undefined — silently skipped.
    assert!(!reg.is_scope_active(&name("Ghost")));
}

#[test]
fn test_activate_defaults_idempotent() {
    let mut reg = registry_with_nat_int();
    reg.set_default_scopes(vec![name("Nat")]);
    reg.activate_defaults();
    reg.activate_defaults();
    // Nat should appear only once in the stack.
    assert_eq!(
        reg.active_scopes()
            .iter()
            .filter(|n| **n == name("Nat"))
            .count(),
        1
    );
}

// ===========================================================================
// 7. Scope inheritance (child inherits parent notations)
// ===========================================================================

#[test]
fn test_inheritance_child_finds_parent_notation() {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    reg.define_scope(name("Nat.Lemma"), Some(name("Nat")))
        .unwrap();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.activate_scope(&name("Nat.Lemma")).unwrap();
    let found = reg.lookup_notation("+").unwrap();
    assert_eq!(found.expansion, "Nat.add");
}

#[test]
fn test_inheritance_child_overrides_parent() {
    let mut reg = NotationScopeRegistry2::new();
    reg.define_scope(name("Nat"), None).unwrap();
    reg.define_scope(name("Nat.Lemma"), Some(name("Nat")))
        .unwrap();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(
        &name("Nat.Lemma"),
        notation("Nat.Lemma.add", "+", "Nat.Lemma.add", 65),
    )
    .unwrap();
    reg.activate_scope(&name("Nat.Lemma")).unwrap();
    let found = reg.lookup_notation("+").unwrap();
    // Child's own notation takes precedence over inherited.
    assert_eq!(found.expansion, "Nat.Lemma.add");
}

#[test]
fn test_inheritance_cycle_does_not_loop() {
    let mut reg = NotationScopeRegistry2::new();
    // Create a cycle: A -> B -> A. Should not infinite-loop.
    reg.define_scope(name("A"), Some(name("B"))).unwrap();
    reg.define_scope(name("B"), Some(name("A"))).unwrap();
    reg.register_notation(&name("A"), notation("A.op", "~", "A.op", 10))
        .unwrap();
    reg.activate_scope(&name("B")).unwrap();
    // Should find A.op via B -> A, but not loop.
    let found = reg.lookup_notation("~");
    assert!(found.is_some());
}

// ===========================================================================
// 8. Scope conflict detection
// ===========================================================================

#[test]
fn test_no_conflicts_disjoint_syntax() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.sub", "-", "Int.sub", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    assert!(reg.detect_active_conflicts().is_empty());
}

#[test]
fn test_conflict_same_syntax_same_priority_different_names() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    let conflicts = reg.detect_active_conflicts();
    assert_eq!(conflicts.len(), 1);
    match &conflicts[0] {
        NotationScopeError::Conflict { syntax, .. } => assert_eq!(syntax, "+"),
        other => panic!("expected Conflict, got: {other:?}"),
    }
}

#[test]
fn test_no_conflict_same_syntax_different_priority() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 70))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    assert!(reg.detect_active_conflicts().is_empty());
}

#[test]
fn test_no_conflict_same_qualified_name() {
    let mut reg = registry_with_nat_int();
    // Both scopes define the same qualified name — not a conflict.
    reg.register_notation(&name("Nat"), notation("HAdd.hAdd", "+", "HAdd.hAdd", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("HAdd.hAdd", "+", "HAdd.hAdd", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    assert!(reg.detect_active_conflicts().is_empty());
}

// ===========================================================================
// 9. Scope export / import
// ===========================================================================

#[test]
fn test_export_scope_basic() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Nat"), notation("Nat.sub", "-", "Nat.sub", 65))
        .unwrap();
    let count = reg.export_scope(&name("Nat"), &name("Int")).unwrap();
    assert_eq!(count, 2);
    // Int should now have Nat's notations.
    let int_notations = reg.scope_notations(&name("Int"));
    assert_eq!(int_notations.len(), 2);
}

#[test]
fn test_export_nonexistent_source_errors() {
    let mut reg = registry_with_nat_int();
    let err = reg.export_scope(&name("Ghost"), &name("Int"));
    assert!(matches!(
        err,
        Err(NotationScopeError::ImportSourceNotFound(_))
    ));
}

#[test]
fn test_export_nonexistent_target_errors() {
    let mut reg = registry_with_nat_int();
    let err = reg.export_scope(&name("Nat"), &name("Ghost"));
    assert!(matches!(
        err,
        Err(NotationScopeError::ExportTargetNotFound(_))
    ));
}

#[test]
fn test_import_scope_alias() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.mul", "*", "Nat.mul", 70))
        .unwrap();
    let count = reg.import_scope(&name("Int"), &name("Nat")).unwrap();
    assert_eq!(count, 1);
    let int_notations = reg.scope_notations(&name("Int"));
    assert_eq!(int_notations.len(), 1);
}

#[test]
fn test_export_overwrites_existing_syntax() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 50))
        .unwrap();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.export_scope(&name("Nat"), &name("Int")).unwrap();
    // Int's "+" should now be Nat.add (overwritten).
    let int_notations = reg.scope_notations(&name("Int"));
    let plus = int_notations.iter().find(|n| n.syntax == "+").unwrap();
    assert_eq!(plus.expansion, "Nat.add");
}

// ===========================================================================
// 10. Scoped abbreviation support
// ===========================================================================

#[test]
fn test_abbreviation_registration_and_lookup() {
    let mut reg = registry_with_nat_int();
    reg.register_abbreviation(&name("Nat"), abbrev("N", "Nat", "Nat"))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    let found = reg.lookup_abbreviation("N").unwrap();
    assert_eq!(found.expansion, "Nat");
}

#[test]
fn test_abbreviation_not_visible_in_wrong_scope() {
    let mut reg = registry_with_nat_int();
    reg.register_abbreviation(&name("Nat"), abbrev("N", "Nat", "Nat"))
        .unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    assert!(reg.lookup_abbreviation("N").is_none());
}

#[test]
fn test_abbreviation_inner_scope_shadows() {
    let mut reg = registry_with_nat_int();
    reg.register_abbreviation(&name("Nat"), abbrev("T", "NatType", "Nat"))
        .unwrap();
    reg.register_abbreviation(&name("Int"), abbrev("T", "IntType", "Int"))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    // Int is on top, should shadow Nat's "T".
    let found = reg.lookup_abbreviation("T").unwrap();
    assert_eq!(found.expansion, "IntType");
}

#[test]
fn test_abbreviation_register_to_nonexistent_scope_errors() {
    let mut reg = NotationScopeRegistry2::new();
    let err = reg.register_abbreviation(&name("Ghost"), abbrev("G", "ghost", "Ghost"));
    assert!(matches!(err, Err(NotationScopeError::ScopeNotFound(_))));
}

// ===========================================================================
// 11. Statistics
// ===========================================================================

#[test]
fn test_stats_initial() {
    let reg = NotationScopeRegistry2::new();
    let stats = reg.stats();
    assert_eq!(stats.scopes_defined, 0);
    assert_eq!(stats.scopes_active, 0);
    assert_eq!(stats.lookups, 0);
    assert_eq!(stats.conflicts, 0);
    assert_eq!(stats.exports, 0);
}

#[test]
fn test_stats_scopes_defined() {
    let reg = registry_with_nat_int();
    assert_eq!(reg.stats().scopes_defined, 2);
}

#[test]
fn test_stats_scopes_active() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    assert_eq!(reg.stats().scopes_active, 1);
    reg.activate_scope(&name("Int")).unwrap();
    assert_eq!(reg.stats().scopes_active, 2);
}

#[test]
fn test_stats_lookups_incremented() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    let _ = reg.lookup_notation("+");
    let _ = reg.lookup_notation("-");
    assert_eq!(reg.stats().lookups, 2);
}

#[test]
fn test_stats_conflicts_incremented() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.register_notation(&name("Int"), notation("Int.add", "+", "Int.add", 65))
        .unwrap();
    reg.activate_scope(&name("Nat")).unwrap();
    reg.activate_scope(&name("Int")).unwrap();
    let _ = reg.detect_active_conflicts();
    assert!(reg.stats().conflicts >= 1);
}

#[test]
fn test_stats_exports_incremented() {
    let mut reg = registry_with_nat_int();
    reg.register_notation(&name("Nat"), notation("Nat.add", "+", "Nat.add", 65))
        .unwrap();
    reg.export_scope(&name("Nat"), &name("Int")).unwrap();
    assert_eq!(reg.stats().exports, 1);
}

#[test]
fn test_stats_lookup_all_also_increments() {
    let mut reg = registry_with_nat_int();
    reg.activate_scope(&name("Nat")).unwrap();
    let _ = reg.lookup_all_notations("+");
    assert_eq!(reg.stats().lookups, 1);
}

// ===========================================================================
// 12. Edge cases and integration
// ===========================================================================

#[test]
fn test_default_trait_impl() {
    let reg = NotationScopeRegistry2::default();
    assert_eq!(reg.scope_count(), 0);
}

#[test]
fn test_notation_scope_struct_accessors() {
    let scope = NotationScope::new(name("Foo"), Some(name("Bar")));
    assert_eq!(scope.name(), &name("Foo"));
    assert_eq!(scope.parent(), Some(&name("Bar")));
    assert_eq!(scope.notation_count(), 0);
    assert_eq!(scope.abbreviation_count(), 0);
}

#[test]
fn test_scoped_notation_fields() {
    let n = notation("Nat.add", "+", "Nat.add", 65);
    assert_eq!(n.qualified_name, name("Nat.add"));
    assert_eq!(n.syntax, "+");
    assert_eq!(n.expansion, "Nat.add");
    assert_eq!(n.priority, 65);
}

#[test]
fn test_scoped_abbreviation_fields() {
    let a = abbrev("N", "Nat", "Nat");
    assert_eq!(a.short_name, "N");
    assert_eq!(a.expansion, "Nat");
    assert_eq!(a.scope, name("Nat"));
}

#[test]
fn test_register_notation_to_nonexistent_scope() {
    let mut reg = NotationScopeRegistry2::new();
    let err = reg.register_notation(&name("Ghost"), notation("G.x", "x", "x", 10));
    assert!(matches!(err, Err(NotationScopeError::ScopeNotFound(_))));
}

#[test]
fn test_scope_stats_default() {
    let stats = ScopeStats::default();
    assert_eq!(stats.scopes_defined, 0);
    assert_eq!(stats.lookups, 0);
}

#[test]
fn test_debug_format() {
    let reg = NotationScopeRegistry2::new();
    let dbg = format!("{reg:?}");
    assert!(dbg.contains("NotationScopeRegistry2"));
}
