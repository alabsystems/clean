// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for notation scoping and precedence-aware resolution.

use super::*;
use std::collections::HashSet;

// ============================================================================
// Entry construction tests
// ============================================================================

#[test]
fn test_entry_global_is_always_visible() {
    let entry = NotationScopeEntry::global("+", ScopedNotationKind::Infix, 65, "HAdd.hAdd");
    assert!(entry.is_global());
    assert!(!entry.is_local());
    assert_eq!(entry.namespace(), None);
    assert!(entry.is_visible(&HashSet::new()));
}

#[test]
fn test_entry_scoped_visibility_depends_on_open_namespaces() {
    let entry = NotationScopeEntry::scoped("+", ScopedNotationKind::Infix, 70, "Nat", "Nat.add");
    assert!(!entry.is_global());
    assert!(!entry.is_local());
    assert_eq!(entry.namespace(), Some("Nat"));

    // Not visible when namespace is closed
    assert!(!entry.is_visible(&HashSet::new()));

    // Visible when namespace is open
    let mut open = HashSet::new();
    open.insert("Nat".to_owned());
    assert!(entry.is_visible(&open));

    // Not visible with a different namespace
    let mut other = HashSet::new();
    other.insert("Int".to_owned());
    assert!(!entry.is_visible(&other));
}

#[test]
fn test_entry_local_is_always_visible() {
    let entry = NotationScopeEntry::local("~", ScopedNotationKind::Prefix, 100, "BNot");
    assert!(!entry.is_global());
    assert!(entry.is_local());
    assert_eq!(entry.namespace(), None);
    // Local entries have no namespace, so is_visible is true for any ns set
    assert!(entry.is_visible(&HashSet::new()));
}

#[test]
fn test_entry_accessors() {
    let entry = NotationScopeEntry::new(
        "++",
        ScopedNotationKind::Infix,
        55,
        Some("List"),
        "List.append",
        false,
    );
    assert_eq!(entry.name(), "++");
    assert_eq!(entry.kind(), ScopedNotationKind::Infix);
    assert_eq!(entry.priority(), 55);
    assert_eq!(entry.namespace(), Some("List"));
    assert_eq!(entry.expansion(), "List.append");
    assert!(!entry.is_local());
}

// ============================================================================
// Registry: registration and basic lookup
// ============================================================================

#[test]
fn test_registry_empty() {
    let reg = NotationScopeRegistry::new();
    assert_eq!(reg.token_count(), 0);
    assert_eq!(reg.entry_count(), 0);
    assert!(!reg.has_notation("+"));
    assert!(reg.resolve("+").is_none());
    assert!(reg.resolve_all("+").is_empty());
}

#[test]
fn test_registry_default() {
    let reg = NotationScopeRegistry::default();
    assert_eq!(reg.token_count(), 0);
    assert_eq!(reg.entry_count(), 0);
}

#[test]
fn test_register_single_global() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));

    assert_eq!(reg.token_count(), 1);
    assert_eq!(reg.entry_count(), 1);
    assert!(reg.has_notation("+"));
    assert!(reg.has_visible_notation("+"));

    let resolved = reg.resolve("+").expect("should resolve global entry");
    assert_eq!(resolved.expansion(), "HAdd.hAdd");
    assert_eq!(resolved.priority(), 65);
}

#[test]
fn test_register_multiple_tokens() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::global(
        "*",
        ScopedNotationKind::Infix,
        70,
        "HMul.hMul",
    ));
    reg.register(NotationScopeEntry::global(
        "-",
        ScopedNotationKind::Prefix,
        100,
        "Neg.neg",
    ));

    assert_eq!(reg.token_count(), 3);
    assert_eq!(reg.entry_count(), 3);
    assert_eq!(
        reg.resolve("+").expect("should find +").expansion(),
        "HAdd.hAdd"
    );
    assert_eq!(
        reg.resolve("*").expect("should find *").expansion(),
        "HMul.hMul"
    );
    assert_eq!(
        reg.resolve("-").expect("should find -").expansion(),
        "Neg.neg"
    );
}

// ============================================================================
// Priority ordering
// ============================================================================

#[test]
fn test_priority_ordering_highest_wins() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        50,
        "Nat.add",
    ));
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        60,
        "Int.add",
    ));

    // resolve returns highest priority
    let best = reg.resolve("+").expect("should resolve");
    assert_eq!(best.expansion(), "HAdd.hAdd");
    assert_eq!(best.priority(), 65);

    // resolve_all returns all in descending priority
    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 3);
    assert_eq!(all[0].priority(), 65);
    assert_eq!(all[1].priority(), 60);
    assert_eq!(all[2].priority(), 50);
}

#[test]
fn test_same_priority_preserves_insertion_order() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "first",
    ));
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "second",
    ));

    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 2);
    assert_eq!(all[0].expansion(), "first");
    assert_eq!(all[1].expansion(), "second");
}

// ============================================================================
// Namespace scoping
// ============================================================================

#[test]
fn test_scoped_notation_invisible_when_namespace_closed() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    // Not visible by default (Nat not open)
    assert!(reg.resolve("+").is_none());
    assert!(reg.resolve_all("+").is_empty());
    assert!(reg.has_notation("+"));
    assert!(!reg.has_visible_notation("+"));
}

#[test]
fn test_scoped_notation_visible_when_namespace_open() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    reg.open_namespace("Nat");
    assert!(reg.is_namespace_open("Nat"));

    let resolved = reg.resolve("+").expect("should resolve after open");
    assert_eq!(resolved.expansion(), "Nat.add");
}

#[test]
fn test_scoped_notation_hidden_after_namespace_close() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    reg.open_namespace("Nat");
    assert!(reg.resolve("+").is_some());

    reg.close_namespace("Nat");
    assert!(!reg.is_namespace_open("Nat"));
    assert!(reg.resolve("+").is_none());
}

#[test]
fn test_global_vs_scoped_priority_resolution() {
    let mut reg = NotationScopeRegistry::new();

    // Global entry with lower priority
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    // Scoped entry with higher priority
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    // Before opening Nat: only global visible
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "HAdd.hAdd");

    // After opening Nat: scoped entry wins (higher priority)
    reg.open_namespace("Nat");
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "Nat.add");

    // resolve_all returns both, scoped first (higher priority)
    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 2);
    assert_eq!(all[0].expansion(), "Nat.add");
    assert_eq!(all[1].expansion(), "HAdd.hAdd");
}

#[test]
fn test_global_higher_priority_than_scoped() {
    let mut reg = NotationScopeRegistry::new();

    // Global entry with HIGHER priority
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        80,
        "HAdd.hAdd",
    ));
    // Scoped entry with LOWER priority
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    reg.open_namespace("Nat");

    // Global wins because it has higher priority
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "HAdd.hAdd");
}

#[test]
fn test_multiple_scoped_namespaces() {
    let mut reg = NotationScopeRegistry::new();

    reg.register(NotationScopeEntry::scoped(
        "++",
        ScopedNotationKind::Infix,
        55,
        "List",
        "List.append",
    ));
    reg.register(NotationScopeEntry::scoped(
        "++",
        ScopedNotationKind::Infix,
        60,
        "String",
        "String.append",
    ));

    // Neither open: no match
    assert!(reg.resolve("++").is_none());

    // Open List: List.append visible
    reg.open_namespace("List");
    assert_eq!(
        reg.resolve("++").expect("List open").expansion(),
        "List.append"
    );

    // Open String too: String.append wins (higher priority)
    reg.open_namespace("String");
    assert_eq!(
        reg.resolve("++").expect("both open").expansion(),
        "String.append"
    );

    // Close String: back to List.append
    reg.close_namespace("String");
    assert_eq!(
        reg.resolve("++").expect("List only").expansion(),
        "List.append"
    );
}

// ============================================================================
// resolve_with_namespaces (explicit namespace set)
// ============================================================================

#[test]
fn test_resolve_with_namespaces_explicit() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    // Explicit namespaces override registry state
    let ns = vec!["Nat".to_owned()];
    let resolved = reg
        .resolve_with_namespaces("+", &ns)
        .expect("should resolve with explicit ns");
    assert_eq!(resolved.expansion(), "Nat.add");

    // Without explicit ns, registry state applies (Nat not open)
    assert_eq!(
        reg.resolve("+").expect("global fallback").expansion(),
        "HAdd.hAdd"
    );
}

#[test]
fn test_resolve_all_with_namespaces_explicit() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));

    let ns = vec!["Nat".to_owned()];
    let all = reg.resolve_all_with_namespaces("+", &ns);
    assert_eq!(all.len(), 2);
    assert_eq!(all[0].expansion(), "Nat.add");
    assert_eq!(all[1].expansion(), "HAdd.hAdd");

    // Without Nat in explicit ns
    let all_empty = reg.resolve_all_with_namespaces("+", &[]);
    assert_eq!(all_empty.len(), 1);
    assert_eq!(all_empty[0].expansion(), "HAdd.hAdd");
}

// ============================================================================
// Local notations
// ============================================================================

#[test]
fn test_local_notation_always_visible() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::local(
        "~",
        ScopedNotationKind::Prefix,
        100,
        "BNot",
    ));

    assert!(reg.has_visible_notation("~"));
    let resolved = reg.resolve("~").expect("local always visible");
    assert_eq!(resolved.expansion(), "BNot");
    assert!(resolved.is_local());
}

#[test]
fn test_clear_local_entries() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::local(
        "+",
        ScopedNotationKind::Infix,
        80,
        "LocalPlus",
    ));
    reg.register(NotationScopeEntry::local(
        "~",
        ScopedNotationKind::Prefix,
        100,
        "BNot",
    ));

    assert_eq!(reg.entry_count(), 3);
    assert_eq!(reg.local_entries().len(), 2);

    // Local + for "+" has higher priority, so it resolves first
    assert_eq!(
        reg.resolve("+").expect("should resolve").expansion(),
        "LocalPlus"
    );

    reg.clear_local_entries();

    assert_eq!(reg.entry_count(), 1);
    assert_eq!(reg.local_entries().len(), 0);
    assert!(!reg.has_notation("~")); // bucket removed entirely

    // Global + survives
    assert_eq!(
        reg.resolve("+").expect("global survives").expansion(),
        "HAdd.hAdd"
    );
}

// ============================================================================
// scoped_entries / global_entries / local_entries
// ============================================================================

#[test]
fn test_scoped_entries_by_namespace() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));
    reg.register(NotationScopeEntry::scoped(
        "*",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.mul",
    ));
    reg.register(NotationScopeEntry::scoped(
        "++",
        ScopedNotationKind::Infix,
        55,
        "List",
        "List.append",
    ));

    let nat_entries = reg.scoped_entries("Nat");
    assert_eq!(nat_entries.len(), 2);
    let nat_expansions: Vec<&str> = nat_entries.iter().map(|e| e.expansion()).collect();
    assert!(nat_expansions.contains(&"Nat.add"));
    assert!(nat_expansions.contains(&"Nat.mul"));

    let list_entries = reg.scoped_entries("List");
    assert_eq!(list_entries.len(), 1);
    assert_eq!(list_entries[0].expansion(), "List.append");

    let empty_entries = reg.scoped_entries("Int");
    assert!(empty_entries.is_empty());
}

#[test]
fn test_global_entries() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.add",
    ));
    reg.register(NotationScopeEntry::local(
        "~",
        ScopedNotationKind::Prefix,
        100,
        "BNot",
    ));

    let globals = reg.global_entries();
    assert_eq!(globals.len(), 1);
    assert_eq!(globals[0].expansion(), "HAdd.hAdd");
}

// ============================================================================
// Namespace operations
// ============================================================================

#[test]
fn test_open_namespace_idempotent() {
    let mut reg = NotationScopeRegistry::new();
    reg.open_namespace("Nat");
    reg.open_namespace("Nat");
    assert_eq!(reg.open_namespaces().len(), 1);
}

#[test]
fn test_close_namespace_idempotent() {
    let mut reg = NotationScopeRegistry::new();
    // Close a namespace that was never opened: no panic
    reg.close_namespace("Nat");
    assert_eq!(reg.open_namespaces().len(), 0);
}

#[test]
fn test_multiple_namespaces_open() {
    let mut reg = NotationScopeRegistry::new();
    reg.open_namespace("Nat");
    reg.open_namespace("List");
    reg.open_namespace("String");
    assert_eq!(reg.open_namespaces().len(), 3);
    assert!(reg.is_namespace_open("Nat"));
    assert!(reg.is_namespace_open("List"));
    assert!(reg.is_namespace_open("String"));
    assert!(!reg.is_namespace_open("Int"));
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_resolve_nonexistent_token() {
    let reg = NotationScopeRegistry::new();
    assert!(reg.resolve("nonexistent").is_none());
    assert!(reg.resolve_all("nonexistent").is_empty());
}

#[test]
fn test_resolve_empty_token() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "",
        ScopedNotationKind::Notation,
        0,
        "EmptyToken",
    ));
    let resolved = reg.resolve("").expect("should resolve empty token");
    assert_eq!(resolved.expansion(), "EmptyToken");
}

#[test]
fn test_all_entries_iterator() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        65,
        "HAdd.hAdd",
    ));
    reg.register(NotationScopeEntry::scoped(
        "*",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "Nat.mul",
    ));
    reg.register(NotationScopeEntry::local(
        "~",
        ScopedNotationKind::Prefix,
        100,
        "BNot",
    ));

    let all: Vec<&NotationScopeEntry> = reg.all_entries().collect();
    assert_eq!(all.len(), 3);
}

#[test]
fn test_notation_kind_display() {
    assert_eq!(ScopedNotationKind::Prefix.to_string(), "prefix");
    assert_eq!(ScopedNotationKind::Infix.to_string(), "infix");
    assert_eq!(ScopedNotationKind::Postfix.to_string(), "postfix");
    assert_eq!(ScopedNotationKind::Notation.to_string(), "notation");
    assert_eq!(ScopedNotationKind::Macro.to_string(), "macro");
}

#[test]
fn test_debug_output() {
    let reg = NotationScopeRegistry::new();
    let debug = format!("{:?}", reg);
    assert!(debug.contains("NotationScopeRegistry"));
    assert!(debug.contains("token_count"));
}

// ============================================================================
// Mixed scenario: global + scoped + local priority interactions
// ============================================================================

#[test]
fn test_mixed_global_scoped_local_resolution() {
    let mut reg = NotationScopeRegistry::new();

    // Global with low priority
    reg.register(NotationScopeEntry::global(
        "+",
        ScopedNotationKind::Infix,
        50,
        "global_plus",
    ));
    // Scoped with medium priority
    reg.register(NotationScopeEntry::scoped(
        "+",
        ScopedNotationKind::Infix,
        70,
        "Nat",
        "nat_plus",
    ));
    // Local with highest priority
    reg.register(NotationScopeEntry::local(
        "+",
        ScopedNotationKind::Infix,
        90,
        "local_plus",
    ));

    // Without Nat open: local wins (90 > 50)
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "local_plus");

    // With Nat open: local still wins (90 > 70 > 50)
    reg.open_namespace("Nat");
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "local_plus");

    // resolve_all shows all 3
    let all = reg.resolve_all("+");
    assert_eq!(all.len(), 3);
    assert_eq!(all[0].expansion(), "local_plus"); // 90
    assert_eq!(all[1].expansion(), "nat_plus"); // 70
    assert_eq!(all[2].expansion(), "global_plus"); // 50

    // Clear local: scoped wins
    reg.clear_local_entries();
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "nat_plus");

    // Close Nat: global wins
    reg.close_namespace("Nat");
    let resolved = reg.resolve("+").expect("should resolve");
    assert_eq!(resolved.expansion(), "global_plus");
}

#[test]
fn test_postfix_and_macro_kinds() {
    let mut reg = NotationScopeRegistry::new();
    reg.register(NotationScopeEntry::global(
        "?",
        ScopedNotationKind::Postfix,
        100,
        "Decidable.decide",
    ));
    reg.register(NotationScopeEntry::global(
        "do",
        ScopedNotationKind::Macro,
        0,
        "DoNotation.expand",
    ));

    let postfix = reg.resolve("?").expect("postfix");
    assert_eq!(postfix.kind(), ScopedNotationKind::Postfix);

    let macro_ = reg.resolve("do").expect("macro");
    assert_eq!(macro_.kind(), ScopedNotationKind::Macro);
}
