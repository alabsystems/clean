// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended instance management module (`instances_ext`).

use crate::instances::InstanceTable;
use crate::instances_ext::*;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_class_expr(class: &str) -> Expr {
    Expr::const_(Name::from_string(class), vec![])
}

fn mk_inst_type(class: &str, arg: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(class), vec![]),
        Expr::const_(Name::from_string(arg), vec![]),
    )
}

/// Build a simple table with one class and N instances at given priorities.
fn table_with_instances(class: &str, instances: &[(&str, u32)]) -> InstanceTable {
    let mut table = InstanceTable::new();
    let class_name = Name::from_string(class);
    table.register_class(class_name.clone(), 1, vec![]);
    for (inst_name, priority) in instances {
        table.add_instance(
            Name::from_string(inst_name),
            class_name.clone(),
            Expr::const_(Name::from_string(inst_name), vec![]),
            mk_inst_type(class, "Nat"),
            *priority,
        );
    }
    table
}

// ===========================================================================
// Priority conflict tests
// ===========================================================================

#[test]
fn test_priority_conflict_none_when_distinct() {
    let table = table_with_instances("Add", &[("instA", 100), ("instB", 200)]);
    let conflicts = find_priority_conflicts(&table);
    assert!(conflicts.is_empty(), "no conflict when priorities differ");
}

#[test]
fn test_priority_conflict_detected_at_same_priority() {
    let table = table_with_instances("Add", &[("instA", 100), ("instB", 100)]);
    let conflicts = find_priority_conflicts(&table);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].priority, 100);
    assert_eq!(conflicts[0].instances.len(), 2);
}

#[test]
fn test_priority_conflict_multiple_groups() {
    let table = table_with_instances(
        "Show",
        &[("a", 50), ("b", 50), ("c", 100), ("d", 100), ("e", 200)],
    );
    let conflicts = find_priority_conflicts(&table);
    assert_eq!(conflicts.len(), 2);
}

#[test]
fn test_priority_conflict_empty_table() {
    let table = InstanceTable::new();
    let conflicts = find_priority_conflicts(&table);
    assert!(conflicts.is_empty());
}

#[test]
fn test_priority_conflict_single_instance_no_conflict() {
    let table = table_with_instances("Add", &[("only", 100)]);
    let conflicts = find_priority_conflicts(&table);
    assert!(conflicts.is_empty());
}

#[test]
fn test_priority_conflict_class_with_no_instances() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Empty"), 0, vec![]);
    let conflicts = find_priority_conflicts(&table);
    assert!(conflicts.is_empty());
}

#[test]
fn test_priority_conflict_three_at_same() {
    let table = table_with_instances("Ord", &[("a", 100), ("b", 100), ("c", 100)]);
    let conflicts = find_priority_conflicts(&table);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].instances.len(), 3);
}

// ===========================================================================
// Instance chain tests
// ===========================================================================

fn table_with_chain() -> InstanceTable {
    // A -> B -> C chain via instance type arguments
    let mut table = InstanceTable::new();
    let a = Name::from_string("A");
    let b = Name::from_string("B");
    let c = Name::from_string("C");
    table.register_class(a.clone(), 1, vec![]);
    table.register_class(b.clone(), 1, vec![]);
    table.register_class(c.clone(), 0, vec![]);

    // Instance for A with type arg referencing B
    let a_type = Expr::app(
        Expr::const_(a.clone(), vec![]),
        Expr::const_(b.clone(), vec![]),
    );
    table.add_instance(
        Name::from_string("instAB"),
        a.clone(),
        mk_class_expr("instAB"),
        a_type,
        100,
    );

    // Instance for B with type arg referencing C
    let b_type = Expr::app(
        Expr::const_(b.clone(), vec![]),
        Expr::const_(c.clone(), vec![]),
    );
    table.add_instance(
        Name::from_string("instBC"),
        b.clone(),
        mk_class_expr("instBC"),
        b_type,
        100,
    );

    table
}

#[test]
fn test_chain_detection_min_depth_1() {
    let table = table_with_chain();
    let chains = find_instance_chains(&table, 1);
    assert!(
        !chains.is_empty(),
        "should find at least one chain of depth >= 1"
    );
}

#[test]
fn test_chain_detection_min_depth_2() {
    let table = table_with_chain();
    let chains = find_instance_chains(&table, 2);
    // A -> B -> C is depth 2
    let deep = chains.iter().any(|c| c.depth() >= 2);
    assert!(deep, "should find chain of depth >= 2 (A->B->C)");
}

#[test]
fn test_chain_detection_empty_table() {
    let table = InstanceTable::new();
    let chains = find_instance_chains(&table, 1);
    assert!(chains.is_empty());
}

#[test]
fn test_chain_detection_no_deps() {
    let table = table_with_instances("Add", &[("instAddNat", 100)]);
    let chains = find_instance_chains(&table, 1);
    // The instance type is `Add Nat` — Nat is not a class, so no chain
    assert!(chains.is_empty());
}

#[test]
fn test_chain_depth_method() {
    let chain = InstanceChain {
        chain: vec![
            Name::from_string("A"),
            Name::from_string("B"),
            Name::from_string("C"),
        ],
        instance_names: vec![Name::from_string("i1"), Name::from_string("i2")],
    };
    assert_eq!(chain.depth(), 2);
}

#[test]
fn test_chain_depth_single_node() {
    let chain = InstanceChain {
        chain: vec![Name::from_string("A")],
        instance_names: vec![],
    };
    assert_eq!(chain.depth(), 0);
}

// ===========================================================================
// Orphan detection tests
// ===========================================================================

#[test]
fn test_orphan_detection_no_orphans_when_class_local() {
    let table = table_with_instances("Add", &[("instAddNat", 100)]);
    let mut local = HashSet::new();
    local.insert(Name::from_string("Add"));
    let orphans = find_orphan_instances(&table, &local);
    assert!(orphans.is_empty(), "class is local → no orphan");
}

#[test]
fn test_orphan_detection_orphan_when_nothing_local() {
    let table = table_with_instances("Add", &[("instAddNat", 100)]);
    let local = HashSet::new();
    let orphans = find_orphan_instances(&table, &local);
    assert_eq!(orphans.len(), 1, "neither class nor type arg is local");
    assert_eq!(orphans[0].instance_name, Name::from_string("instAddNat"));
}

#[test]
fn test_orphan_detection_empty_table() {
    let table = InstanceTable::new();
    let local = HashSet::new();
    let orphans = find_orphan_instances(&table, &local);
    assert!(orphans.is_empty());
}

#[test]
fn test_orphan_detection_type_arg_local() {
    // Build table where type arg is a class-application with a local name
    let mut table = InstanceTable::new();
    let class = Name::from_string("Show");
    let my_type = Name::from_string("MyType");
    table.register_class(class.clone(), 1, vec![]);
    // Register MyType as a class too so extract_class_app finds it
    table.register_class(my_type.clone(), 0, vec![]);
    let inst_type = Expr::app(
        Expr::const_(class.clone(), vec![]),
        Expr::const_(my_type.clone(), vec![]),
    );
    table.add_instance(
        Name::from_string("instShowMyType"),
        class.clone(),
        mk_class_expr("instShowMyType"),
        inst_type,
        100,
    );

    let mut local = HashSet::new();
    local.insert(my_type);
    let orphans = find_orphan_instances(&table, &local);
    assert!(orphans.is_empty(), "type arg is local → not an orphan");
}

#[test]
fn test_orphan_multiple_instances_mixed() {
    let mut table = InstanceTable::new();
    let class = Name::from_string("Repr");
    table.register_class(class.clone(), 1, vec![]);

    // Instance 1: orphan (Nat is not local)
    table.add_instance(
        Name::from_string("instReprNat"),
        class.clone(),
        mk_class_expr("instReprNat"),
        mk_inst_type("Repr", "Nat"),
        100,
    );
    // Instance 2: also orphan
    table.add_instance(
        Name::from_string("instReprBool"),
        class.clone(),
        mk_class_expr("instReprBool"),
        mk_inst_type("Repr", "Bool"),
        100,
    );

    let local = HashSet::new();
    let orphans = find_orphan_instances(&table, &local);
    assert_eq!(orphans.len(), 2);
}

// ===========================================================================
// Statistics tests
// ===========================================================================

#[test]
fn test_statistics_empty_table() {
    let table = InstanceTable::new();
    let stats = collect_statistics(&table);
    assert_eq!(stats.total_classes, 0);
    assert_eq!(stats.total_instances, 0);
    assert!(stats.per_class.is_empty());
}

#[test]
fn test_statistics_single_class_single_instance() {
    let table = table_with_instances("Add", &[("inst", 100)]);
    let stats = collect_statistics(&table);
    assert_eq!(stats.total_classes, 1);
    assert_eq!(stats.total_instances, 1);
    assert_eq!(stats.per_class.len(), 1);
    assert_eq!(stats.per_class[0].instance_count, 1);
    assert!((stats.per_class[0].avg_priority - 100.0).abs() < f64::EPSILON);
    assert_eq!(stats.per_class[0].min_priority, 100);
    assert_eq!(stats.per_class[0].max_priority, 100);
}

#[test]
fn test_statistics_multiple_instances() {
    let table = table_with_instances("Show", &[("a", 50), ("b", 100), ("c", 150)]);
    let stats = collect_statistics(&table);
    assert_eq!(stats.total_instances, 3);
    let cs = &stats.per_class[0];
    assert_eq!(cs.min_priority, 50);
    assert_eq!(cs.max_priority, 150);
    assert!((cs.avg_priority - 100.0).abs() < f64::EPSILON);
}

#[test]
fn test_statistics_depth_distribution() {
    let mut table = InstanceTable::new();
    // Class with 0 instances
    table.register_class(Name::from_string("Empty"), 0, vec![]);
    // Class with 2 instances
    let two = Name::from_string("Two");
    table.register_class(two.clone(), 1, vec![]);
    table.add_instance(
        Name::from_string("t1"),
        two.clone(),
        mk_class_expr("t1"),
        mk_inst_type("Two", "X"),
        100,
    );
    table.add_instance(
        Name::from_string("t2"),
        two.clone(),
        mk_class_expr("t2"),
        mk_inst_type("Two", "Y"),
        100,
    );

    let stats = collect_statistics(&table);
    assert_eq!(*stats.depth_distribution.get(&0).unwrap_or(&0), 1); // Empty: 0 instances
    assert_eq!(*stats.depth_distribution.get(&2).unwrap_or(&0), 1); // Two: 2 instances
}

#[test]
fn test_statistics_out_params_reported() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Functor"), 1, vec![0]);
    let stats = collect_statistics(&table);
    assert!(stats.per_class[0].has_out_params);
}

#[test]
fn test_statistics_no_out_params() {
    let table = table_with_instances("Add", &[("inst", 100)]);
    let stats = collect_statistics(&table);
    assert!(!stats.per_class[0].has_out_params);
}

// ===========================================================================
// Diamond detection tests
// ===========================================================================

#[test]
fn test_diamond_empty_table() {
    let table = InstanceTable::new();
    let diamonds = detect_diamonds(&table);
    assert!(diamonds.is_empty());
}

#[test]
fn test_diamond_no_deps() {
    let table = table_with_instances("Add", &[("inst", 100)]);
    let diamonds = detect_diamonds(&table);
    assert!(diamonds.is_empty());
}

#[test]
fn test_diamond_detected_two_paths() {
    // Setup: A depends on C via two paths (through B1 and B2)
    let mut table = InstanceTable::new();
    let a = Name::from_string("A");
    let b1 = Name::from_string("B1");
    let b2 = Name::from_string("B2");
    let c = Name::from_string("C");
    table.register_class(a.clone(), 1, vec![]);
    table.register_class(b1.clone(), 1, vec![]);
    table.register_class(b2.clone(), 1, vec![]);
    table.register_class(c.clone(), 0, vec![]);

    // A -> B1 (instance type arg references B1)
    table.add_instance(
        Name::from_string("instAB1"),
        a.clone(),
        mk_class_expr("instAB1"),
        Expr::app(
            Expr::const_(a.clone(), vec![]),
            Expr::const_(b1.clone(), vec![]),
        ),
        100,
    );
    // A -> B2
    table.add_instance(
        Name::from_string("instAB2"),
        a.clone(),
        mk_class_expr("instAB2"),
        Expr::app(
            Expr::const_(a.clone(), vec![]),
            Expr::const_(b2.clone(), vec![]),
        ),
        100,
    );
    // B1 -> C
    table.add_instance(
        Name::from_string("instB1C"),
        b1.clone(),
        mk_class_expr("instB1C"),
        Expr::app(
            Expr::const_(b1.clone(), vec![]),
            Expr::const_(c.clone(), vec![]),
        ),
        100,
    );
    // B2 -> C
    table.add_instance(
        Name::from_string("instB2C"),
        b2.clone(),
        mk_class_expr("instB2C"),
        Expr::app(
            Expr::const_(b2.clone(), vec![]),
            Expr::const_(c.clone(), vec![]),
        ),
        100,
    );

    let diamonds = detect_diamonds(&table);
    let c_diamond = diamonds.iter().find(|d| d.target_class == c);
    assert!(
        c_diamond.is_some(),
        "should detect diamond to C through B1 and B2"
    );
    assert!(c_diamond.expect("just checked").paths.len() >= 2);
}

// ===========================================================================
// Search log tests
// ===========================================================================

#[test]
fn test_search_log_empty() {
    let log = SearchLog::new();
    assert_eq!(log.total(), 0);
    assert_eq!(log.success_count(), 0);
    assert_eq!(log.failure_count(), 0);
    assert_eq!(log.backtrack_count(), 0);
}

#[test]
fn test_search_log_record_success() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("Add"),
        Name::from_string("instAddNat"),
        SearchOutcome::Success,
    );
    assert_eq!(log.total(), 1);
    assert_eq!(log.success_count(), 1);
}

#[test]
fn test_search_log_record_failure() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("Show"),
        Name::from_string("instShowFoo"),
        SearchOutcome::Failure,
    );
    assert_eq!(log.failure_count(), 1);
    assert_eq!(log.success_count(), 0);
}

#[test]
fn test_search_log_record_backtrack() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("Ord"),
        Name::from_string("instOrdA"),
        SearchOutcome::Backtrack,
    );
    assert_eq!(log.backtrack_count(), 1);
}

#[test]
fn test_search_log_summary() {
    let mut log = SearchLog::new();
    let cls = Name::from_string("X");
    log.record(cls.clone(), Name::from_string("i1"), SearchOutcome::Failure);
    log.record(
        cls.clone(),
        Name::from_string("i2"),
        SearchOutcome::Backtrack,
    );
    log.record(cls.clone(), Name::from_string("i3"), SearchOutcome::Success);
    let (s, f, b) = log.summary();
    assert_eq!(s, 1);
    assert_eq!(f, 1);
    assert_eq!(b, 1);
    assert_eq!(log.total(), 3);
}

#[test]
fn test_search_log_clear() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("A"),
        Name::from_string("i"),
        SearchOutcome::Success,
    );
    assert_eq!(log.total(), 1);
    log.clear();
    assert_eq!(log.total(), 0);
}

#[test]
fn test_search_log_entries_access() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("A"),
        Name::from_string("i1"),
        SearchOutcome::Success,
    );
    log.record(
        Name::from_string("B"),
        Name::from_string("i2"),
        SearchOutcome::Failure,
    );
    let entries = log.entries();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].class, Name::from_string("A"));
    assert_eq!(entries[1].outcome, SearchOutcome::Failure);
}

// ===========================================================================
// Batch operations tests
// ===========================================================================

fn mk_spec(name: &str, class: &str, priority: u32) -> InstanceSpec {
    InstanceSpec {
        name: Name::from_string(name),
        class_name: Name::from_string(class),
        expr: Expr::const_(Name::from_string(name), vec![]),
        type_: mk_inst_type(class, "T"),
        priority,
    }
}

#[test]
fn test_batch_add_success() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    let specs = vec![mk_spec("i1", "Add", 100), mk_spec("i2", "Add", 200)];
    let result = batch_add(&mut table, &specs);
    assert_eq!(result.added, 2);
    assert!(result.conflicts.is_empty());
    assert_eq!(table.get_instances(&Name::from_string("Add")).len(), 2);
}

#[test]
fn test_batch_add_duplicate_detected() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    table.add_instance(
        Name::from_string("existing"),
        Name::from_string("Add"),
        mk_class_expr("existing"),
        mk_inst_type("Add", "T"),
        100,
    );
    let specs = vec![mk_spec("existing", "Add", 200)];
    let result = batch_add(&mut table, &specs);
    assert_eq!(result.added, 0);
    assert_eq!(result.conflicts.len(), 1);
}

#[test]
fn test_batch_add_empty() {
    let mut table = InstanceTable::new();
    let result = batch_add(&mut table, &[]);
    assert_eq!(result.added, 0);
    assert!(result.conflicts.is_empty());
}

#[test]
fn test_batch_add_partial_success() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Show"), 1, vec![]);
    table.add_instance(
        Name::from_string("dup"),
        Name::from_string("Show"),
        mk_class_expr("dup"),
        mk_inst_type("Show", "T"),
        100,
    );
    let specs = vec![
        mk_spec("dup", "Show", 100),  // will conflict
        mk_spec("new1", "Show", 200), // will succeed
    ];
    let result = batch_add(&mut table, &specs);
    assert_eq!(result.added, 1);
    assert_eq!(result.conflicts.len(), 1);
}

#[test]
fn test_batch_remove_counts() {
    let table = table_with_instances("Add", &[("a", 100), ("b", 200)]);
    let mut to_remove = HashSet::new();
    to_remove.insert(Name::from_string("a"));
    let removed = batch_remove(&mut table.clone(), &to_remove);
    assert_eq!(removed, 1);
}

#[test]
fn test_batch_remove_nonexistent() {
    let table = table_with_instances("Add", &[("a", 100)]);
    let mut to_remove = HashSet::new();
    to_remove.insert(Name::from_string("nonexistent"));
    let removed = batch_remove(&mut table.clone(), &to_remove);
    assert_eq!(removed, 0);
}

#[test]
fn test_batch_remove_empty_set() {
    let table = table_with_instances("Add", &[("a", 100)]);
    let to_remove = HashSet::new();
    let removed = batch_remove(&mut table.clone(), &to_remove);
    assert_eq!(removed, 0);
}

// ===========================================================================
// Replace instance tests
// ===========================================================================

#[test]
fn test_replace_instance_success() {
    let mut table = table_with_instances("Add", &[("old", 100)]);
    let new_spec = mk_spec("new", "Add", 200);
    let result = replace_instance(&mut table, &Name::from_string("old"), &new_spec);
    assert!(result.is_ok());
    // Both old and new exist (replace adds new; see doc)
    let instances = table.get_instances(&Name::from_string("Add"));
    assert!(instances.iter().any(|i| i.name == Name::from_string("new")));
}

#[test]
fn test_replace_instance_not_found() {
    let mut table = table_with_instances("Add", &[("a", 100)]);
    let new_spec = mk_spec("b", "Add", 200);
    let result = replace_instance(&mut table, &Name::from_string("missing"), &new_spec);
    assert!(result.is_err());
    match result {
        Err(InstanceExtError::InstanceNotFound(_)) => {}
        other => panic!("expected InstanceNotFound, got {other:?}"),
    }
}

// ===========================================================================
// Error variant tests
// ===========================================================================

#[test]
fn test_error_display_priority_conflict() {
    let err = InstanceExtError::PriorityConflict {
        class: "Add".into(),
        priority: 100,
        count: 2,
    };
    let msg = format!("{err}");
    assert!(msg.contains("priority conflict"));
    assert!(msg.contains("Add"));
}

#[test]
fn test_error_display_orphan() {
    let err = InstanceExtError::OrphanInstance {
        instance: "inst".into(),
        class: "Cls".into(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("orphan"));
}

#[test]
fn test_error_display_class_not_found() {
    let err = InstanceExtError::ClassNotFound("Missing".into());
    assert!(format!("{err}").contains("not found"));
}

#[test]
fn test_error_display_duplicate() {
    let err = InstanceExtError::DuplicateInstance {
        name: "dup".into(),
        class: "Cls".into(),
    };
    assert!(format!("{err}").contains("duplicate"));
}

#[test]
fn test_error_display_diamond() {
    let err = InstanceExtError::DiamondDetected {
        target: "C".into(),
        path_count: 3,
    };
    assert!(format!("{err}").contains("diamond"));
}

#[test]
fn test_error_display_instance_not_found() {
    let err = InstanceExtError::InstanceNotFound("x".into());
    assert!(format!("{err}").contains("not found"));
}

// ===========================================================================
// Edge case and integration tests
// ===========================================================================

#[test]
fn test_statistics_class_with_zero_instances() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Zero"), 0, vec![]);
    let stats = collect_statistics(&table);
    assert_eq!(stats.per_class[0].instance_count, 0);
    assert_eq!(stats.per_class[0].min_priority, 0);
    assert_eq!(stats.per_class[0].max_priority, 0);
    assert!((stats.per_class[0].avg_priority - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_priority_conflict_across_multiple_classes() {
    let mut table = InstanceTable::new();
    let add = Name::from_string("Add");
    let mul = Name::from_string("Mul");
    table.register_class(add.clone(), 1, vec![]);
    table.register_class(mul.clone(), 1, vec![]);

    // Conflict in Add
    table.add_instance(
        Name::from_string("a1"),
        add.clone(),
        mk_class_expr("a1"),
        mk_inst_type("Add", "X"),
        100,
    );
    table.add_instance(
        Name::from_string("a2"),
        add.clone(),
        mk_class_expr("a2"),
        mk_inst_type("Add", "Y"),
        100,
    );

    // No conflict in Mul
    table.add_instance(
        Name::from_string("m1"),
        mul.clone(),
        mk_class_expr("m1"),
        mk_inst_type("Mul", "X"),
        50,
    );
    table.add_instance(
        Name::from_string("m2"),
        mul.clone(),
        mk_class_expr("m2"),
        mk_inst_type("Mul", "Y"),
        100,
    );

    let conflicts = find_priority_conflicts(&table);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].class, add);
}

#[test]
fn test_search_log_multiple_classes() {
    let mut log = SearchLog::new();
    log.record(
        Name::from_string("A"),
        Name::from_string("i1"),
        SearchOutcome::Failure,
    );
    log.record(
        Name::from_string("B"),
        Name::from_string("i2"),
        SearchOutcome::Success,
    );
    log.record(
        Name::from_string("A"),
        Name::from_string("i3"),
        SearchOutcome::Success,
    );
    assert_eq!(log.success_count(), 2);
    assert_eq!(log.failure_count(), 1);
}

#[test]
fn test_batch_add_multiple_classes() {
    let mut table = InstanceTable::new();
    table.register_class(Name::from_string("Add"), 1, vec![]);
    table.register_class(Name::from_string("Mul"), 1, vec![]);
    let specs = vec![mk_spec("iAdd", "Add", 100), mk_spec("iMul", "Mul", 200)];
    let result = batch_add(&mut table, &specs);
    assert_eq!(result.added, 2);
    assert_eq!(table.get_instances(&Name::from_string("Add")).len(), 1);
    assert_eq!(table.get_instances(&Name::from_string("Mul")).len(), 1);
}
