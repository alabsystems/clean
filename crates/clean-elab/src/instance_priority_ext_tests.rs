// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended instance priority resolution.

use crate::instance_priority_ext::*;
use clean_kernel::name::Name;

// ===========================================================================
// Helpers
// ===========================================================================

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn make_entry(
    name: &str,
    class: &str,
    rule: PriorityRule,
    is_default: bool,
    is_local: bool,
) -> InstanceEntry {
    InstanceEntry {
        name: n(name),
        class: n(class),
        priority: rule,
        is_default,
        is_local,
        added_in: None,
    }
}

fn make_entry_in(
    name: &str,
    class: &str,
    rule: PriorityRule,
    is_default: bool,
    is_local: bool,
    module: &str,
) -> InstanceEntry {
    InstanceEntry {
        name: n(name),
        class: n(class),
        priority: rule,
        is_default,
        is_local,
        added_in: Some(n(module)),
    }
}

// ===========================================================================
// compute_effective_priority
// ===========================================================================

#[test]
fn test_compute_explicit() {
    assert_eq!(
        compute_effective_priority(&PriorityRule::Explicit(500), 100),
        500
    );
}

#[test]
fn test_compute_explicit_zero() {
    assert_eq!(
        compute_effective_priority(&PriorityRule::Explicit(0), 100),
        0
    );
}

#[test]
fn test_compute_default() {
    assert_eq!(compute_effective_priority(&PriorityRule::Default, 100), 0);
}

#[test]
fn test_compute_local() {
    assert_eq!(compute_effective_priority(&PriorityRule::Local, 200), 200);
}

#[test]
fn test_compute_scoped() {
    assert_eq!(
        compute_effective_priority(&PriorityRule::Scoped(n("Mathlib")), 100),
        100
    );
}

#[test]
fn test_compute_derived() {
    assert_eq!(
        compute_effective_priority(&PriorityRule::DerivedFrom(n("Parent")), 300),
        300
    );
}

// ===========================================================================
// Registration
// ===========================================================================

#[test]
fn test_register_instance_basic() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);
    assert_eq!(ext.total_entries(), 1);
    assert_eq!(ext.class_count(), 1);
}

#[test]
fn test_register_multiple_classes() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);
    ext.register_instance(&n("Mul"), &n("instMulNat"), 100, false, false);
    assert_eq!(ext.total_entries(), 2);
    assert_eq!(ext.class_count(), 2);
}

#[test]
fn test_register_multiple_same_class() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);
    ext.register_instance(&n("Add"), &n("instAddInt"), 200, false, false);
    assert_eq!(ext.total_entries(), 2);
    assert_eq!(ext.class_count(), 1);
    assert_eq!(ext.get_entries(&n("Add")).len(), 2);
}

#[test]
fn test_register_default_instance() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 0, true, false);
    let entries = ext.get_entries(&n("Add"));
    assert_eq!(entries.len(), 1);
    assert!(entries[0].is_default);
    assert_eq!(entries[0].priority, PriorityRule::Default);
}

#[test]
fn test_register_local_instance() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddLocal"), 100, false, true);
    let entries = ext.get_entries(&n("Add"));
    assert_eq!(entries.len(), 1);
    assert!(entries[0].is_local);
    assert_eq!(entries[0].priority, PriorityRule::Local);
}

#[test]
fn test_register_entry_with_module() {
    let mut ext = InstancePriorityExt::new();
    let entry = make_entry_in(
        "instAddNat",
        "Add",
        PriorityRule::Explicit(100),
        false,
        false,
        "Mathlib.Algebra",
    );
    ext.register_entry(entry);
    assert_eq!(ext.total_entries(), 1);
    let e = &ext.get_entries(&n("Add"))[0];
    assert_eq!(e.added_in, Some(n("Mathlib.Algebra")));
}

// ===========================================================================
// resolve_priority
// ===========================================================================

#[test]
fn test_resolve_priority_basic_ordering() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("low"), 50, false, false);
    ext.register_instance(&n("Add"), &n("high"), 500, false, false);
    ext.register_instance(&n("Add"), &n("mid"), 100, false, false);

    let candidates = vec![n("low"), n("high"), n("mid")];
    let result = ext.resolve_priority(&n("Add"), &candidates);

    assert_eq!(result.len(), 3);
    assert_eq!(result[0], (n("high"), 500));
    assert_eq!(result[1], (n("mid"), 100));
    assert_eq!(result[2], (n("low"), 50));
}

#[test]
fn test_resolve_priority_filters_unknown_candidates() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("known"), 100, false, false);

    let candidates = vec![n("known"), n("unknown")];
    let result = ext.resolve_priority(&n("Add"), &candidates);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].0, n("known"));
}

#[test]
fn test_resolve_priority_empty_candidates() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);

    let result = ext.resolve_priority(&n("Add"), &[]);
    assert!(result.is_empty());
}

#[test]
fn test_resolve_priority_unknown_class() {
    let ext = InstancePriorityExt::new();
    let candidates = vec![n("instAddNat")];
    let result = ext.resolve_priority(&n("Add"), &candidates);
    assert!(result.is_empty());
}

#[test]
fn test_resolve_priority_default_instance_last() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("regular"), 100, false, false);
    ext.register_instance(&n("Add"), &n("fallback"), 0, true, false);

    let candidates = vec![n("regular"), n("fallback")];
    let result = ext.resolve_priority(&n("Add"), &candidates);

    assert_eq!(result.len(), 2);
    assert_eq!(result[0], (n("regular"), 100));
    assert_eq!(result[1], (n("fallback"), 0));
}

// ===========================================================================
// get_default_instance
// ===========================================================================

#[test]
fn test_get_default_instance_present() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);
    ext.register_instance(&n("Add"), &n("defaultAdd"), 0, true, false);

    assert_eq!(ext.get_default_instance(&n("Add")), Some(n("defaultAdd")));
}

#[test]
fn test_get_default_instance_absent() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);

    assert_eq!(ext.get_default_instance(&n("Add")), None);
}

#[test]
fn test_get_default_instance_unknown_class() {
    let ext = InstancePriorityExt::new();
    assert_eq!(ext.get_default_instance(&n("Add")), None);
}

#[test]
fn test_get_default_instance_multiple_defaults() {
    let mut ext = InstancePriorityExt::new();
    // Both marked default; the one with Explicit(50) should win over Default(0).
    let e1 = InstanceEntry {
        name: n("defaultLow"),
        class: n("Add"),
        priority: PriorityRule::Default,
        is_default: true,
        is_local: false,
        added_in: None,
    };
    let e2 = InstanceEntry {
        name: n("defaultHigh"),
        class: n("Add"),
        priority: PriorityRule::Explicit(50),
        is_default: true,
        is_local: false,
        added_in: None,
    };
    ext.register_entry(e1);
    ext.register_entry(e2);

    assert_eq!(ext.get_default_instance(&n("Add")), Some(n("defaultHigh")));
}

// ===========================================================================
// check_orphan
// ===========================================================================

#[test]
fn test_orphan_class_local() {
    let ext = InstancePriorityExt::new();
    let result = ext.check_orphan(
        &n("instAddNat"),
        &n("MyModule.Add"),
        &n("External.Nat"),
        &n("MyModule"),
    );
    assert!(result.is_ok());
}

#[test]
fn test_orphan_type_local() {
    let ext = InstancePriorityExt::new();
    let result = ext.check_orphan(
        &n("instAddMyType"),
        &n("External.Add"),
        &n("MyModule.MyType"),
        &n("MyModule"),
    );
    assert!(result.is_ok());
}

#[test]
fn test_orphan_both_local() {
    let ext = InstancePriorityExt::new();
    let result = ext.check_orphan(
        &n("instAddMyType"),
        &n("MyModule.Add"),
        &n("MyModule.MyType"),
        &n("MyModule"),
    );
    assert!(result.is_ok());
}

#[test]
fn test_orphan_both_foreign() {
    let ext = InstancePriorityExt::new();
    let result = ext.check_orphan(
        &n("instAddNat"),
        &n("External.Add"),
        &n("Other.Nat"),
        &n("MyModule"),
    );
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert_eq!(err.reason, OrphanReason::BothNotLocal);
    assert_eq!(err.instance, n("instAddNat"));
    assert_eq!(err.class, n("External.Add"));
    assert_eq!(err.type_, n("Other.Nat"));
}

#[test]
fn test_orphan_error_display() {
    let err = OrphanError {
        instance: n("instBadOrphan"),
        class: n("ForeignClass"),
        type_: n("ForeignType"),
        reason: OrphanReason::BothNotLocal,
    };
    let msg = err.to_string();
    assert!(msg.contains("instBadOrphan"));
    assert!(msg.contains("ForeignClass"));
    assert!(msg.contains("ForeignType"));
}

#[test]
fn test_orphan_empty_module_always_local() {
    // Empty module name means anonymous root — everything is local.
    let ext = InstancePriorityExt::new();
    let result = ext.check_orphan(
        &n("inst"),
        &n("Foreign.Class"),
        &n("Foreign.Type"),
        &Name::anon(),
    );
    assert!(result.is_ok());
}

// ===========================================================================
// filter_by_scope
// ===========================================================================

#[test]
fn test_filter_scope_global_always_visible() {
    let entries = vec![make_entry(
        "inst",
        "Add",
        PriorityRule::Explicit(100),
        false,
        false,
    )];
    let visible = filter_by_scope(&entries, &n("AnyScope"));
    assert_eq!(visible.len(), 1);
}

#[test]
fn test_filter_scope_local_always_visible() {
    let entries = vec![make_entry("inst", "Add", PriorityRule::Local, false, true)];
    let visible = filter_by_scope(&entries, &n("AnyScope"));
    assert_eq!(visible.len(), 1);
}

#[test]
fn test_filter_scope_scoped_matching() {
    let entries = vec![make_entry(
        "inst",
        "Add",
        PriorityRule::Scoped(n("Mathlib")),
        false,
        false,
    )];

    // current_scope is child of "Mathlib" → visible
    let visible = filter_by_scope(&entries, &n("Mathlib.Algebra"));
    assert_eq!(visible.len(), 1);

    // exact match → visible
    let visible = filter_by_scope(&entries, &n("Mathlib"));
    assert_eq!(visible.len(), 1);
}

#[test]
fn test_filter_scope_scoped_not_matching() {
    let entries = vec![make_entry(
        "inst",
        "Add",
        PriorityRule::Scoped(n("Mathlib")),
        false,
        false,
    )];

    let visible = filter_by_scope(&entries, &n("Std.Data"));
    assert_eq!(visible.len(), 0);
}

#[test]
fn test_filter_scope_mixed() {
    let entries = vec![
        make_entry("global", "Add", PriorityRule::Explicit(100), false, false),
        make_entry(
            "scoped",
            "Add",
            PriorityRule::Scoped(n("Mathlib")),
            false,
            false,
        ),
        make_entry("local", "Add", PriorityRule::Local, false, true),
    ];

    // In Std scope: scoped(Mathlib) is not visible
    let visible = filter_by_scope(&entries, &n("Std"));
    assert_eq!(visible.len(), 2);
    assert_eq!(visible[0].name, n("global"));
    assert_eq!(visible[1].name, n("local"));

    // In Mathlib scope: all visible
    let visible = filter_by_scope(&entries, &n("Mathlib"));
    assert_eq!(visible.len(), 3);
}

// ===========================================================================
// merge_instance_tables
// ===========================================================================

#[test]
fn test_merge_empty_tables() {
    let t1 = InstancePriorityExt::new();
    let t2 = InstancePriorityExt::new();
    let merged = merge_instance_tables(&[&t1, &t2]);
    assert_eq!(merged.total_entries(), 0);
}

#[test]
fn test_merge_disjoint_tables() {
    let mut t1 = InstancePriorityExt::new();
    t1.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);

    let mut t2 = InstancePriorityExt::new();
    t2.register_instance(&n("Mul"), &n("instMulNat"), 100, false, false);

    let merged = merge_instance_tables(&[&t1, &t2]);
    assert_eq!(merged.total_entries(), 2);
    assert_eq!(merged.class_count(), 2);
}

#[test]
fn test_merge_overlapping_tables() {
    let mut t1 = InstancePriorityExt::new();
    t1.register_instance(&n("Add"), &n("instAddNat"), 100, false, false);

    let mut t2 = InstancePriorityExt::new();
    t2.register_instance(&n("Add"), &n("instAddInt"), 200, false, false);

    let merged = merge_instance_tables(&[&t1, &t2]);
    assert_eq!(merged.total_entries(), 2);
    assert_eq!(merged.class_count(), 1);
    assert_eq!(merged.get_entries(&n("Add")).len(), 2);
}

#[test]
fn test_merge_preserves_entries() {
    let mut t1 = InstancePriorityExt::new();
    t1.register_instance(&n("Add"), &n("inst1"), 50, false, false);

    let mut t2 = InstancePriorityExt::new();
    t2.register_instance(&n("Add"), &n("inst2"), 500, false, false);

    let merged = merge_instance_tables(&[&t1, &t2]);
    let candidates = vec![n("inst1"), n("inst2")];
    let resolved = merged.resolve_priority(&n("Add"), &candidates);

    assert_eq!(resolved[0], (n("inst2"), 500));
    assert_eq!(resolved[1], (n("inst1"), 50));
}

// ===========================================================================
// detect_priority_conflicts
// ===========================================================================

#[test]
fn test_no_conflicts() {
    let entries = vec![
        make_entry("inst1", "Add", PriorityRule::Explicit(100), false, false),
        make_entry("inst2", "Add", PriorityRule::Explicit(200), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    assert!(conflicts.is_empty());
}

#[test]
fn test_same_priority_conflict() {
    let entries = vec![
        make_entry("inst1", "Add", PriorityRule::Explicit(100), false, false),
        make_entry("inst2", "Add", PriorityRule::Explicit(100), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    assert_eq!(conflicts.len(), 1);
    // Canonical order
    assert!(conflicts[0].0.to_string() <= conflicts[0].1.to_string());
}

#[test]
fn test_different_classes_no_conflict() {
    let entries = vec![
        make_entry("inst1", "Add", PriorityRule::Explicit(100), false, false),
        make_entry("inst2", "Mul", PriorityRule::Explicit(100), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    assert!(conflicts.is_empty());
}

#[test]
fn test_three_way_conflict() {
    let entries = vec![
        make_entry("a", "Add", PriorityRule::Explicit(100), false, false),
        make_entry("b", "Add", PriorityRule::Explicit(100), false, false),
        make_entry("c", "Add", PriorityRule::Explicit(100), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    // (a,b), (a,c), (b,c) = 3 pairs
    assert_eq!(conflicts.len(), 3);
}

#[test]
fn test_conflict_local_vs_explicit_same_priority() {
    // Local resolves to base=100, Explicit(100) is also 100 → conflict
    let entries = vec![
        make_entry("inst1", "Add", PriorityRule::Local, false, true),
        make_entry("inst2", "Add", PriorityRule::Explicit(100), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_no_conflict_default_vs_explicit() {
    // Default resolves to 0, Explicit(100) → different
    let entries = vec![
        make_entry("inst1", "Add", PriorityRule::Default, true, false),
        make_entry("inst2", "Add", PriorityRule::Explicit(100), false, false),
    ];
    let conflicts = detect_priority_conflicts(&entries);
    assert!(conflicts.is_empty());
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_empty_registry_operations() {
    let ext = InstancePriorityExt::new();
    assert_eq!(ext.total_entries(), 0);
    assert_eq!(ext.class_count(), 0);
    assert!(ext.get_entries(&n("Add")).is_empty());
    assert_eq!(ext.get_default_instance(&n("Add")), None);
    assert!(ext.resolve_priority(&n("Add"), &[n("inst")]).is_empty());
}

#[test]
fn test_priority_rule_equality() {
    assert_eq!(PriorityRule::Explicit(42), PriorityRule::Explicit(42));
    assert_ne!(PriorityRule::Explicit(42), PriorityRule::Explicit(43));
    assert_eq!(PriorityRule::Default, PriorityRule::Default);
    assert_ne!(PriorityRule::Local, PriorityRule::Default);
}

#[test]
fn test_orphan_reason_display() {
    assert_eq!(
        OrphanReason::ClassNotLocal.to_string(),
        "class is not defined in current module"
    );
    assert_eq!(
        OrphanReason::TypeNotLocal.to_string(),
        "type is not defined in current module"
    );
    assert_eq!(
        OrphanReason::BothNotLocal.to_string(),
        "neither class nor type is defined in current module"
    );
}

#[test]
fn test_resolve_priority_stable_sort_equal_priorities() {
    let mut ext = InstancePriorityExt::new();
    ext.register_instance(&n("Add"), &n("first"), 100, false, false);
    ext.register_instance(&n("Add"), &n("second"), 100, false, false);

    let candidates = vec![n("first"), n("second")];
    let result = ext.resolve_priority(&n("Add"), &candidates);

    // Both have priority 100; stable sort preserves the order from filter_map
    // which follows candidates order (first finds first entry, second finds second).
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].1, 100);
    assert_eq!(result[1].1, 100);
}

#[test]
fn test_merge_single_table() {
    let mut t1 = InstancePriorityExt::new();
    t1.register_instance(&n("Add"), &n("inst1"), 100, false, false);

    let merged = merge_instance_tables(&[&t1]);
    assert_eq!(merged.total_entries(), 1);
}

#[test]
fn test_merge_no_tables() {
    let merged = merge_instance_tables(&[]);
    assert_eq!(merged.total_entries(), 0);
}

#[test]
fn test_filter_scope_derived_always_visible() {
    let entries = vec![make_entry(
        "inst",
        "Add",
        PriorityRule::DerivedFrom(n("Parent")),
        false,
        false,
    )];
    let visible = filter_by_scope(&entries, &n("AnyScope"));
    assert_eq!(visible.len(), 1);
}

#[test]
fn test_filter_scope_empty_entries() {
    let entries: Vec<InstanceEntry> = vec![];
    let visible = filter_by_scope(&entries, &n("Scope"));
    assert!(visible.is_empty());
}

#[test]
fn test_detect_conflicts_empty() {
    let conflicts = detect_priority_conflicts(&[]);
    assert!(conflicts.is_empty());
}

#[test]
fn test_detect_conflicts_single_entry() {
    let entries = vec![make_entry(
        "inst1",
        "Add",
        PriorityRule::Explicit(100),
        false,
        false,
    )];
    let conflicts = detect_priority_conflicts(&entries);
    assert!(conflicts.is_empty());
}
