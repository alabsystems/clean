// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for instance priority management, scoping, and backtracking.

use super::*;
use crate::instances::{InstanceInfo, InstanceTable, DEFAULT_PRIORITY};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

// ===========================================================================
// Helper constructors
// ===========================================================================

/// Create a simple class-type expression `ClassName ArgName`.
fn class_app(class: &str, arg: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(class), vec![]),
        Expr::const_(Name::from_string(arg), vec![]),
    )
}

/// Create a bare constant expression.
fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Create an InstanceInfo for testing.
fn make_instance(name: &str, class: &str, arg: &str, priority: u32) -> InstanceInfo {
    InstanceInfo {
        name: Name::from_string(name),
        class_name: Name::from_string(class),
        expr: const_expr(name),
        type_: class_app(class, arg),
        priority,
        synth_order: None,
    }
}

// ===========================================================================
// InstancePriority struct tests
// ===========================================================================

#[test]
fn test_priority_struct_construction() {
    let p = InstancePriority::new(42);
    assert_eq!(p.value(), 42);
    assert!(!p.is_default_instance());

    let default = InstancePriority::DEFAULT;
    assert_eq!(default.value(), 100);
    assert!(!default.is_default_instance());

    let fallback = InstancePriority::DEFAULT_INSTANCE;
    assert_eq!(fallback.value(), 0);
    assert!(fallback.is_default_instance());
}

#[test]
fn test_priority_ordering() {
    let low = InstancePriority::LOW;
    let default = InstancePriority::DEFAULT;
    let high = InstancePriority::HIGH;
    let override_ = InstancePriority::OVERRIDE;
    let fallback = InstancePriority::DEFAULT_INSTANCE;

    // Higher value = higher priority = Greater
    assert!(override_ > high);
    assert!(high > default);
    assert!(default > low);
    assert!(low > fallback);

    // Equality
    assert_eq!(InstancePriority::new(100), InstancePriority::DEFAULT);

    // Specific numeric values
    assert_eq!(fallback.value(), 0);
    assert_eq!(low.value(), 50);
    assert_eq!(default.value(), 100);
    assert_eq!(high.value(), 500);
    assert_eq!(override_.value(), 1000);
}

#[test]
fn test_priority_default_trait() {
    let p: InstancePriority = Default::default();
    assert_eq!(p, InstancePriority::DEFAULT);
    assert_eq!(p.value(), 100);
}

#[test]
fn test_priority_from_conversions() {
    // u32 -> InstancePriority
    let p: InstancePriority = 42u32.into();
    assert_eq!(p.value(), 42);

    // InstancePriority -> u32
    let v: u32 = InstancePriority::HIGH.into();
    assert_eq!(v, 500);
}

// ===========================================================================
// PriorityQueue tests
// ===========================================================================

#[test]
fn test_priority_queue_ordering() {
    let mut queue = PriorityQueue::new();
    assert!(queue.is_empty());
    assert_eq!(queue.len(), 0);

    // Insert in non-sorted order
    queue.insert(make_instance("inst_low", "Add", "Nat", 50), false);
    queue.insert(make_instance("inst_high", "Add", "Nat", 200), false);
    queue.insert(make_instance("inst_default", "Add", "Nat", 100), false);

    assert_eq!(queue.len(), 3);
    assert_eq!(queue.regular_count(), 3);
    assert_eq!(queue.default_count(), 0);

    // Iteration should yield highest priority first
    let names: Vec<String> = queue.iter().map(|p| p.info.name.to_string()).collect();
    assert_eq!(names[0], "inst_high");
    assert_eq!(names[1], "inst_default");
    assert_eq!(names[2], "inst_low");
}

#[test]
fn test_priority_queue_defaults_after_regular() {
    let mut queue = PriorityQueue::new();

    // Default instance with high numeric priority
    queue.insert(make_instance("default_inst", "Add", "Nat", 500), true);
    // Regular instance with lower priority
    queue.insert(make_instance("regular_inst", "Add", "Nat", 100), false);

    assert_eq!(queue.len(), 2);
    assert_eq!(queue.regular_count(), 1);
    assert_eq!(queue.default_count(), 1);

    // Regular instances come before defaults regardless of numeric priority
    let names: Vec<String> = queue.iter().map(|p| p.info.name.to_string()).collect();
    assert_eq!(names[0], "regular_inst");
    assert_eq!(names[1], "default_inst");
}

#[test]
fn test_default_instance_fallback() {
    let mut fallback = DefaultInstanceFallback::new();
    let class = Name::from_string("Show");

    assert!(!fallback.has_defaults(&class));
    assert_eq!(fallback.total_defaults(), 0);

    fallback.register(
        class.clone(),
        Name::from_string("defaultShowString"),
        const_expr("defaultShowString"),
        class_app("Show", "String"),
        InstancePriority::DEFAULT_INSTANCE,
    );

    assert!(fallback.has_defaults(&class));
    assert_eq!(fallback.total_defaults(), 1);

    let defaults = fallback.get_defaults(&class);
    assert_eq!(defaults.len(), 1);
    assert_eq!(defaults[0].name, Name::from_string("defaultShowString"));
}

#[test]
fn test_multiple_matching_instances() {
    let mut queue = PriorityQueue::new();

    // Three instances for the same class+arg at different priorities
    queue.insert(make_instance("inst_p50", "Show", "Nat", 50), false);
    queue.insert(make_instance("inst_p200", "Show", "Nat", 200), false);
    queue.insert(make_instance("inst_p100", "Show", "Nat", 100), false);

    // Default fallback
    queue.insert(make_instance("inst_default", "Show", "Nat", 0), true);

    assert_eq!(queue.len(), 4);

    // Resolution order: p200, p100, p50, then default
    let priorities: Vec<u32> = queue.iter().map(|p| p.priority.value()).collect();
    assert_eq!(priorities, vec![200, 100, 50, 0]);

    // First candidate should be the highest-priority regular instance
    let first = queue.iter().next().expect("queue should not be empty");
    assert_eq!(first.info.name, Name::from_string("inst_p200"));
    assert!(!first.is_default);
}

// ===========================================================================
// ScopedInstances tests
// ===========================================================================

#[test]
fn test_local_instance_scoping() {
    let mut scoped = ScopedInstances::new();
    let class = Name::from_string("Add");

    assert_eq!(scoped.depth(), 0);
    assert_eq!(scoped.total_instances(), 0);
    assert!(!scoped.has_instances(&class));

    // Push a scope and register an instance
    scoped.push_scope();
    assert_eq!(scoped.depth(), 1);

    scoped.register_local(
        Name::from_string("localAddNat"),
        class.clone(),
        const_expr("localAddNat"),
        class_app("Add", "Nat"),
        InstancePriority::DEFAULT,
    );

    assert!(scoped.has_instances(&class));
    assert_eq!(scoped.total_instances(), 1);
    assert_eq!(scoped.get_instances(&class).len(), 1);

    // Pop scope - instance should no longer be visible
    assert!(scoped.pop_scope());
    assert!(!scoped.has_instances(&class));
    assert_eq!(scoped.total_instances(), 0);
    assert_eq!(scoped.get_instances(&class).len(), 0);
}

#[test]
fn test_scoped_instance_registration() {
    let mut scoped = ScopedInstances::new();
    let class = Name::from_string("Mul");

    // Register in nested scopes
    scoped.push_scope();
    scoped.register_local(
        Name::from_string("outerMulNat"),
        class.clone(),
        const_expr("outerMulNat"),
        class_app("Mul", "Nat"),
        InstancePriority::LOW,
    );

    scoped.push_scope();
    scoped.register_local(
        Name::from_string("innerMulNat"),
        class.clone(),
        const_expr("innerMulNat"),
        class_app("Mul", "Nat"),
        InstancePriority::HIGH,
    );

    assert_eq!(scoped.depth(), 2);
    assert_eq!(scoped.total_instances(), 2);

    // Both instances visible, sorted by priority
    let visible = scoped.get_instances(&class);
    assert_eq!(visible.len(), 2);
    assert_eq!(visible[0].name, Name::from_string("innerMulNat")); // HIGH
    assert_eq!(visible[1].name, Name::from_string("outerMulNat")); // LOW

    // Pop inner scope
    scoped.pop_scope();
    let visible = scoped.get_instances(&class);
    assert_eq!(visible.len(), 1);
    assert_eq!(visible[0].name, Name::from_string("outerMulNat"));

    // Pop outer scope
    scoped.pop_scope();
    assert!(scoped.get_instances(&class).is_empty());
}

#[test]
fn test_scoped_instances_no_scope_silently_drops() {
    let mut scoped = ScopedInstances::new();

    // Register without pushing a scope - should be silently dropped
    scoped.register_local(
        Name::from_string("orphan"),
        Name::from_string("Add"),
        const_expr("orphan"),
        class_app("Add", "Nat"),
        InstancePriority::DEFAULT,
    );

    assert_eq!(scoped.total_instances(), 0);
    assert!(!scoped.has_instances(&Name::from_string("Add")));
}

#[test]
fn test_scoped_instances_pop_empty_returns_false() {
    let mut scoped = ScopedInstances::new();
    assert!(!scoped.pop_scope());
}

#[test]
fn test_scoped_instances_different_classes() {
    let mut scoped = ScopedInstances::new();
    let add = Name::from_string("Add");
    let mul = Name::from_string("Mul");

    scoped.push_scope();
    scoped.register_local(
        Name::from_string("addNat"),
        add.clone(),
        const_expr("addNat"),
        class_app("Add", "Nat"),
        InstancePriority::DEFAULT,
    );
    scoped.register_local(
        Name::from_string("mulNat"),
        mul.clone(),
        const_expr("mulNat"),
        class_app("Mul", "Nat"),
        InstancePriority::DEFAULT,
    );

    assert_eq!(scoped.get_instances(&add).len(), 1);
    assert_eq!(scoped.get_instances(&mul).len(), 1);
    assert!(!scoped.has_instances(&Name::from_string("Sub")));
}

// ===========================================================================
// DefaultInstanceFallback tests
// ===========================================================================

#[test]
fn test_default_instance_priority_ordering() {
    let mut fallback = DefaultInstanceFallback::new();
    let class = Name::from_string("ToString");

    fallback.register(
        class.clone(),
        Name::from_string("defaultToStringLow"),
        const_expr("defaultToStringLow"),
        class_app("ToString", "Alpha"),
        InstancePriority::new(10),
    );

    fallback.register(
        class.clone(),
        Name::from_string("defaultToStringHigh"),
        const_expr("defaultToStringHigh"),
        class_app("ToString", "Alpha"),
        InstancePriority::new(50),
    );

    let defaults = fallback.get_defaults(&class);
    assert_eq!(defaults.len(), 2);
    // Higher priority first
    assert_eq!(defaults[0].name, Name::from_string("defaultToStringHigh"));
    assert_eq!(defaults[1].name, Name::from_string("defaultToStringLow"));
}

#[test]
fn test_default_instance_no_class() {
    let fallback = DefaultInstanceFallback::new();
    let class = Name::from_string("Nonexistent");

    assert!(!fallback.has_defaults(&class));
    assert!(fallback.get_defaults(&class).is_empty());
}

// ===========================================================================
// build_priority_queue integration tests
// ===========================================================================

#[test]
fn test_build_priority_queue_merges_sources() {
    let mut table = InstanceTable::new();
    let class = Name::from_string("Repr");
    table.register_class(class.clone(), 1, vec![]);

    table.add_instance(
        Name::from_string("reprNat"),
        class.clone(),
        const_expr("reprNat"),
        class_app("Repr", "Nat"),
        DEFAULT_PRIORITY,
    );

    let mut defaults = DefaultInstanceFallback::new();
    defaults.register(
        class.clone(),
        Name::from_string("reprDefault"),
        const_expr("reprDefault"),
        class_app("Repr", "Alpha"),
        InstancePriority::DEFAULT_INSTANCE,
    );

    let queue = build_priority_queue(&class, &table, &defaults);
    assert_eq!(queue.len(), 2);
    assert_eq!(queue.regular_count(), 1);
    assert_eq!(queue.default_count(), 1);

    // Regular instance first, then default
    let names: Vec<String> = queue.iter().map(|p| p.info.name.to_string()).collect();
    assert_eq!(names[0], "reprNat");
    assert_eq!(names[1], "reprDefault");
}

#[test]
fn test_build_priority_queue_empty_table() {
    let table = InstanceTable::new();
    let defaults = DefaultInstanceFallback::new();
    let class = Name::from_string("Empty");

    let queue = build_priority_queue(&class, &table, &defaults);
    assert!(queue.is_empty());
}

#[test]
fn test_backtrack_on_failure() {
    // Test that the PriorityQueue provides candidates in order for backtracking.
    // The actual backtracking logic is in instance_resolution.rs/infer/instance.rs;
    // here we verify the queue yields candidates in the correct order so that
    // the resolution engine can try the next one when a higher-priority instance fails.
    let mut queue = PriorityQueue::new();

    // Instance that might fail unification (wrong arg type)
    queue.insert(make_instance("inst_wrong", "Add", "Bool", 200), false);
    // Instance that should succeed
    queue.insert(make_instance("inst_right", "Add", "Nat", 100), false);
    // Default fallback
    queue.insert(make_instance("inst_fallback", "Add", "Any", 0), true);

    let candidates: Vec<&PrioritizedInstance> = queue.iter().collect();
    assert_eq!(candidates.len(), 3);

    // Resolution engine tries inst_wrong first (highest priority)
    assert_eq!(candidates[0].info.name, Name::from_string("inst_wrong"));
    assert_eq!(candidates[0].priority, InstancePriority::new(200));
    assert!(!candidates[0].is_default);

    // After inst_wrong fails unification, tries inst_right
    assert_eq!(candidates[1].info.name, Name::from_string("inst_right"));
    assert_eq!(candidates[1].priority, InstancePriority::new(100));
    assert!(!candidates[1].is_default);

    // After all regular instances fail, tries default
    assert_eq!(candidates[2].info.name, Name::from_string("inst_fallback"));
    assert!(candidates[2].is_default);
}

#[test]
fn test_priority_queue_same_priority_insertion_order() {
    // When two instances have the same priority, insertion order is preserved
    // (partition_point finds the first position where priority < new, so
    // equal-priority items end up in insertion order).
    let mut queue = PriorityQueue::new();

    queue.insert(make_instance("first", "Add", "Nat", 100), false);
    queue.insert(make_instance("second", "Add", "Nat", 100), false);
    queue.insert(make_instance("third", "Add", "Nat", 100), false);

    let names: Vec<String> = queue.iter().map(|p| p.info.name.to_string()).collect();
    assert_eq!(names, vec!["first", "second", "third"]);
}
