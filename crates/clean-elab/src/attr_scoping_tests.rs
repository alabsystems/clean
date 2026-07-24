// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for attribute scoping (`@[scoped]`, `@[local]`, `@[export]`).

use super::attr_scoping::{is_visible, AttributeScope, ScopedAttrEntry, ScopedAttrRegistry};
use super::attr_scoping_integration::{
    apply_scoped_instance, apply_scoped_simp, resolve_scoped_attrs,
};
use clean_kernel::name::Name;
use std::collections::HashSet;

/// Helper: create an entry with the given parameters.
fn make_entry(decl: &str, attr: &str, scope: AttributeScope, ns: &str) -> ScopedAttrEntry {
    ScopedAttrEntry {
        decl_name: Name::from_string(decl),
        attr_name: attr.to_string(),
        scope,
        namespace: Name::from_string(ns),
    }
}

#[test]
fn test_registry_default_empty() {
    let reg = ScopedAttrRegistry::new();
    assert!(reg.is_empty());
    assert_eq!(reg.len(), 0);
    assert!(reg.get_all("simp").is_empty());
    assert!(reg.get_active("simp").is_empty());
    assert!(reg.open_namespaces().is_empty());
}

#[test]
fn test_global_attrs_always_visible() {
    let mut reg = ScopedAttrRegistry::new();
    reg.register(make_entry(
        "Nat.add_comm",
        "simp",
        AttributeScope::Global,
        "Nat",
    ));

    // Visible even with no namespaces open
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].decl_name, Name::from_string("Nat.add_comm"));

    // Still visible after opening an unrelated namespace
    reg.open_namespace(&Name::from_string("List"));
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
}

#[test]
fn test_scoped_attrs_visible_when_namespace_opened() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");
    reg.register(make_entry(
        "Nat.add_zero",
        "simp",
        AttributeScope::Scoped(nat.clone()),
        "Nat",
    ));

    // Not visible when Nat is not open
    assert!(reg.get_active("simp").is_empty());

    // Visible after opening Nat
    reg.open_namespace(&nat);
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].decl_name, Name::from_string("Nat.add_zero"));
}

#[test]
fn test_local_attrs_always_visible() {
    let mut reg = ScopedAttrRegistry::new();
    reg.register(make_entry(
        "my_local_lemma",
        "simp",
        AttributeScope::Local,
        "MySection",
    ));

    // Visible with no namespaces open
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].decl_name, Name::from_string("my_local_lemma"));

    // Still visible after opening a namespace
    reg.open_namespace(&Name::from_string("Unrelated"));
    assert_eq!(reg.get_active("simp").len(), 1);
}

#[test]
fn test_open_close_namespace() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");
    reg.register(make_entry(
        "Nat.succ_pos",
        "simp",
        AttributeScope::Scoped(nat.clone()),
        "Nat",
    ));

    // Initially not visible
    assert!(reg.get_active("simp").is_empty());

    // Open: becomes visible
    reg.open_namespace(&nat);
    assert_eq!(reg.get_active("simp").len(), 1);

    // Close: no longer visible
    reg.close_namespace(&nat);
    assert!(reg.get_active("simp").is_empty());
}

#[test]
fn test_multiple_namespaces() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");
    let list = Name::from_string("List");

    reg.register(make_entry(
        "Nat.add_comm",
        "simp",
        AttributeScope::Scoped(nat.clone()),
        "Nat",
    ));
    reg.register(make_entry(
        "List.length_nil",
        "simp",
        AttributeScope::Scoped(list.clone()),
        "List",
    ));

    // Open only Nat
    reg.open_namespace(&nat);
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].decl_name, Name::from_string("Nat.add_comm"));

    // Open List too
    reg.open_namespace(&list);
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 2);

    // Close Nat, only List remains
    reg.close_namespace(&nat);
    let active = reg.get_active("simp");
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].decl_name, Name::from_string("List.length_nil"));
}

#[test]
fn test_get_all_ignores_scope() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");

    reg.register(make_entry(
        "global_lemma",
        "simp",
        AttributeScope::Global,
        "Root",
    ));
    reg.register(make_entry(
        "scoped_lemma",
        "simp",
        AttributeScope::Scoped(nat),
        "Nat",
    ));
    reg.register(make_entry(
        "local_lemma",
        "simp",
        AttributeScope::Local,
        "Section",
    ));

    // get_all returns all 3 regardless of scope
    let all = reg.get_all("simp");
    assert_eq!(all.len(), 3);
}

#[test]
fn test_is_visible_function() {
    let nat = Name::from_string("Nat");
    let list = Name::from_string("List");

    let global_entry = make_entry("g", "simp", AttributeScope::Global, "Root");
    let scoped_entry = make_entry("s", "simp", AttributeScope::Scoped(nat.clone()), "Nat");
    let local_entry = make_entry("l", "simp", AttributeScope::Local, "Section");

    let empty: HashSet<Name> = HashSet::new();
    let with_nat: HashSet<Name> = [nat.clone()].into_iter().collect();
    let with_list: HashSet<Name> = [list].into_iter().collect();

    // Global: always visible
    assert!(is_visible(&global_entry, &empty));
    assert!(is_visible(&global_entry, &with_nat));

    // Scoped: only when namespace is open
    assert!(!is_visible(&scoped_entry, &empty));
    assert!(is_visible(&scoped_entry, &with_nat));
    assert!(!is_visible(&scoped_entry, &with_list));

    // Local: always visible
    assert!(is_visible(&local_entry, &empty));
    assert!(is_visible(&local_entry, &with_nat));
}

#[test]
fn test_scoped_simp_registration() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");
    let lemma = Name::from_string("Nat.add_comm");

    apply_scoped_simp(&lemma, &AttributeScope::Scoped(nat.clone()), &mut reg);

    assert_eq!(reg.len(), 1);
    let all = reg.get_all("simp");
    assert_eq!(all.len(), 1);
    assert_eq!(all[0].decl_name, lemma);
    assert_eq!(all[0].scope, AttributeScope::Scoped(nat));
}

#[test]
fn test_scoped_instance_registration() {
    let mut reg = ScopedAttrRegistry::new();
    let inst = Name::from_string("instHAddNat");

    apply_scoped_instance(&inst, &AttributeScope::Global, 100, &mut reg);

    assert_eq!(reg.len(), 1);
    let all = reg.get_all("instance");
    assert_eq!(all.len(), 1);
    assert_eq!(all[0].decl_name, inst);
    assert_eq!(all[0].scope, AttributeScope::Global);
}

#[test]
fn test_resolve_scoped_attrs() {
    let mut reg = ScopedAttrRegistry::new();
    let nat = Name::from_string("Nat");
    let list = Name::from_string("List");

    // Register entries with different scopes
    reg.register(make_entry(
        "Nat.add_comm",
        "simp",
        AttributeScope::Scoped(nat.clone()),
        "Nat",
    ));
    reg.register(make_entry(
        "List.length",
        "simp",
        AttributeScope::Scoped(list.clone()),
        "List",
    ));
    reg.register(make_entry(
        "global_lemma",
        "simp",
        AttributeScope::Global,
        "Root",
    ));
    reg.register(make_entry(
        "local_lemma",
        "simp",
        AttributeScope::Local,
        "Section",
    ));

    // Resolve with only Nat open: should return only the Nat-scoped entry
    let resolved = resolve_scoped_attrs(std::slice::from_ref(&nat), &reg);
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].decl_name, Name::from_string("Nat.add_comm"));

    // Resolve with both: should return both scoped entries
    let resolved = resolve_scoped_attrs(&[nat, list], &reg);
    assert_eq!(resolved.len(), 2);

    // Resolve with empty: no scoped entries
    let resolved = resolve_scoped_attrs(&[], &reg);
    assert!(resolved.is_empty());
}

#[test]
fn test_different_attr_names() {
    let mut reg = ScopedAttrRegistry::new();
    reg.register(make_entry("lem1", "simp", AttributeScope::Global, "Root"));
    reg.register(make_entry(
        "inst1",
        "instance",
        AttributeScope::Global,
        "Root",
    ));

    assert_eq!(reg.get_active("simp").len(), 1);
    assert_eq!(reg.get_active("instance").len(), 1);
    assert!(reg.get_active("inline").is_empty());
    assert_eq!(reg.len(), 2);
}
