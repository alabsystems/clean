// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;
use std::time::Duration;

use crate::command_elab_registry::{CommandElabEntry, CommandElabRegistry};
use crate::command_elab_registry_ext::*;

// =============================================================================
// Override tracking tests
// =============================================================================

#[test]
fn test_override_tracker_empty() {
    let tracker = OverrideTracker::new();
    assert!(tracker.records().is_empty());
    assert_eq!(tracker.overridden_count(), 0);
    assert!(!tracker.is_overridden("anything"));
}

#[test]
fn test_override_tracker_record_and_query() {
    let mut tracker = OverrideTracker::new();
    tracker.record("simp", 1000, 2000);
    assert!(tracker.is_overridden("simp"));
    assert!(!tracker.is_overridden("inline"));
    assert_eq!(tracker.overridden_count(), 1);
    assert_eq!(tracker.records().len(), 1);
    assert_eq!(tracker.records()[0].command_name, "simp");
    assert_eq!(tracker.records()[0].original_priority, 1000);
    assert_eq!(tracker.records()[0].replacement_priority, 2000);
}

#[test]
fn test_override_tracker_multiple_records_same_command() {
    let mut tracker = OverrideTracker::new();
    tracker.record("simp", 500, 2000);
    tracker.record("simp", 1000, 2000);
    assert_eq!(tracker.records().len(), 2);
    // Distinct overridden commands is still 1.
    assert_eq!(tracker.overridden_count(), 1);
}

#[test]
fn test_override_tracker_multiple_distinct_commands() {
    let mut tracker = OverrideTracker::new();
    tracker.record("simp", 1000, 2000);
    tracker.record("inline", 1000, 1500);
    assert_eq!(tracker.overridden_count(), 2);
}

#[test]
fn test_detect_overrides_no_overrides() {
    let registry = CommandElabRegistry::new();
    let tracker = detect_overrides(&registry);
    // Builtins each have exactly one handler, so no overrides.
    assert_eq!(tracker.overridden_count(), 0);
}

#[test]
fn test_detect_overrides_with_override() {
    let mut registry = CommandElabRegistry::new();
    registry.register(
        "simp",
        CommandElabEntry {
            command_name: "simp".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 5000,
        },
    );
    let tracker = detect_overrides(&registry);
    assert!(tracker.is_overridden("simp"));
    assert_eq!(tracker.overridden_count(), 1);
}

// =============================================================================
// Usage statistics tests
// =============================================================================

#[test]
fn test_usage_collector_empty() {
    let collector = UsageCollector::new();
    assert_eq!(collector.total_invocations(), 0);
    assert_eq!(collector.active_command_count(), 0);
    assert!(collector.get("anything").is_none());
}

#[test]
fn test_usage_collector_record_success() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::from_micros(100));
    let stats = collector.get("simp").unwrap();
    assert_eq!(stats.invocations, 1);
    assert_eq!(stats.successes, 1);
    assert_eq!(stats.failures, 0);
    assert_eq!(stats.total_duration, Duration::from_micros(100));
}

#[test]
fn test_usage_collector_record_failure() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", false, Duration::from_micros(50));
    let stats = collector.get("simp").unwrap();
    assert_eq!(stats.invocations, 1);
    assert_eq!(stats.successes, 0);
    assert_eq!(stats.failures, 1);
}

#[test]
fn test_usage_collector_multiple_invocations() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::from_micros(100));
    collector.record_invocation("simp", true, Duration::from_micros(200));
    collector.record_invocation("simp", false, Duration::from_micros(50));
    let stats = collector.get("simp").unwrap();
    assert_eq!(stats.invocations, 3);
    assert_eq!(stats.successes, 2);
    assert_eq!(stats.failures, 1);
    assert_eq!(stats.total_duration, Duration::from_micros(350));
}

#[test]
fn test_usage_stats_avg_duration() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::from_micros(100));
    collector.record_invocation("simp", true, Duration::from_micros(300));
    let stats = collector.get("simp").unwrap();
    assert_eq!(stats.avg_duration(), Some(Duration::from_micros(200)));
}

#[test]
fn test_usage_stats_avg_duration_none_on_zero() {
    let stats = CommandUsageStats::default();
    assert!(stats.avg_duration().is_none());
}

#[test]
fn test_usage_stats_failure_rate() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::from_micros(10));
    collector.record_invocation("simp", false, Duration::from_micros(10));
    collector.record_invocation("simp", false, Duration::from_micros(10));
    let stats = collector.get("simp").unwrap();
    let rate = stats.failure_rate().unwrap();
    assert!((rate - 2.0 / 3.0).abs() < 1e-10);
}

#[test]
fn test_usage_stats_failure_rate_none_on_zero() {
    let stats = CommandUsageStats::default();
    assert!(stats.failure_rate().is_none());
}

#[test]
fn test_usage_collector_total_invocations_multiple_commands() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::ZERO);
    collector.record_invocation("inline", true, Duration::ZERO);
    collector.record_invocation("simp", true, Duration::ZERO);
    assert_eq!(collector.total_invocations(), 3);
    assert_eq!(collector.active_command_count(), 2);
}

#[test]
fn test_usage_collector_reset() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("simp", true, Duration::ZERO);
    collector.reset();
    assert_eq!(collector.total_invocations(), 0);
    assert_eq!(collector.active_command_count(), 0);
}

#[test]
fn test_usage_collector_commands_iterator() {
    let mut collector = UsageCollector::new();
    collector.record_invocation("alpha", true, Duration::ZERO);
    collector.record_invocation("beta", true, Duration::ZERO);
    let mut cmds: Vec<&str> = collector.commands().collect();
    cmds.sort();
    assert_eq!(cmds, vec!["alpha", "beta"]);
}

// =============================================================================
// Dependency analysis tests
// =============================================================================

#[test]
fn test_validate_dependencies_all_satisfied() {
    let registry = CommandElabRegistry::new();
    let deps = vec![CommandDependency {
        command: "myCmd".to_owned(),
        depends_on: "simp".to_owned(),
    }];
    assert!(validate_dependencies(&registry, &deps).is_ok());
}

#[test]
fn test_validate_dependencies_missing() {
    let registry = CommandElabRegistry::new();
    let deps = vec![CommandDependency {
        command: "myCmd".to_owned(),
        depends_on: "nonexistent".to_owned(),
    }];
    let err = validate_dependencies(&registry, &deps).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("nonexistent"));
    assert!(msg.contains("myCmd"));
}

#[test]
fn test_validate_dependencies_empty() {
    let registry = CommandElabRegistry::new();
    assert!(validate_dependencies(&registry, &[]).is_ok());
}

#[test]
fn test_detect_circular_dependencies_no_cycle() {
    let deps = vec![
        CommandDependency {
            command: "a".to_owned(),
            depends_on: "b".to_owned(),
        },
        CommandDependency {
            command: "b".to_owned(),
            depends_on: "c".to_owned(),
        },
    ];
    assert!(detect_circular_dependencies(&deps).is_ok());
}

#[test]
fn test_detect_circular_dependencies_direct_cycle() {
    let deps = vec![
        CommandDependency {
            command: "a".to_owned(),
            depends_on: "b".to_owned(),
        },
        CommandDependency {
            command: "b".to_owned(),
            depends_on: "a".to_owned(),
        },
    ];
    let err = detect_circular_dependencies(&deps).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("circular"));
}

#[test]
fn test_detect_circular_dependencies_self_cycle() {
    let deps = vec![CommandDependency {
        command: "a".to_owned(),
        depends_on: "a".to_owned(),
    }];
    let err = detect_circular_dependencies(&deps).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("circular"));
}

#[test]
fn test_detect_circular_dependencies_empty() {
    assert!(detect_circular_dependencies(&[]).is_ok());
}

// =============================================================================
// Namespace filtering tests
// =============================================================================

#[test]
fn test_filter_by_namespace_all() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_namespace(&registry, "");
    // Empty prefix matches everything.
    assert_eq!(result.len(), registry.kind_count());
}

#[test]
fn test_filter_by_namespace_prefix_match() {
    let mut registry = CommandElabRegistry::new();
    registry.register(
        "Lean.simp",
        CommandElabEntry {
            command_name: "Lean.simp".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 1000,
        },
    );
    registry.register(
        "Lean.inline",
        CommandElabEntry {
            command_name: "Lean.inline".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 1000,
        },
    );
    let result = filter_by_namespace(&registry, "Lean.");
    assert_eq!(result.len(), 2);
    assert!(result.contains(&"Lean.simp".to_owned()));
    assert!(result.contains(&"Lean.inline".to_owned()));
}

#[test]
fn test_filter_by_namespace_no_match() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_namespace(&registry, "Nonexistent.");
    assert!(result.is_empty());
}

#[test]
fn test_filter_by_wildcard_star() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_wildcard(&registry, "*");
    assert_eq!(result.len(), registry.kind_count());
}

#[test]
fn test_filter_by_wildcard_prefix() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_wildcard(&registry, "sim*");
    assert!(result.contains(&"simp".to_owned()));
    assert!(result.iter().all(|n| n.starts_with("sim")));
}

#[test]
fn test_filter_by_wildcard_suffix() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_wildcard(&registry, "*ible");
    // Should match reducible, irreducible, semireducible.
    assert!(result.iter().all(|n| n.ends_with("ible")));
    assert!(result.len() >= 2); // At least reducible and irreducible.
}

#[test]
fn test_filter_by_wildcard_exact() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_wildcard(&registry, "simp");
    assert_eq!(result, vec!["simp".to_owned()]);
}

#[test]
fn test_filter_by_wildcard_no_match() {
    let registry = CommandElabRegistry::new();
    let result = filter_by_wildcard(&registry, "zzz*");
    assert!(result.is_empty());
}

#[test]
fn test_filter_results_are_sorted() {
    let mut registry = CommandElabRegistry::new();
    registry.register(
        "z_cmd",
        CommandElabEntry {
            command_name: "z_cmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 1000,
        },
    );
    registry.register(
        "a_cmd",
        CommandElabEntry {
            command_name: "a_cmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 1000,
        },
    );
    let result = filter_by_namespace(&registry, "");
    for pair in result.windows(2) {
        assert!(pair[0] <= pair[1], "results should be sorted");
    }
}

// =============================================================================
// Batch registration tests
// =============================================================================

fn make_batch_entry(name: &str, priority: u32) -> BatchEntry {
    BatchEntry {
        name: name.to_owned(),
        handler: Arc::new(|_ctx, _args| Ok(())),
        priority,
    }
}

#[test]
fn test_batch_register_allow_mode() {
    let mut registry = CommandElabRegistry::new();
    let entries = vec![
        make_batch_entry("cmdA", 1000),
        make_batch_entry("cmdB", 2000),
    ];
    let count = batch_register(&mut registry, &entries, BatchConflictMode::Allow).unwrap();
    assert_eq!(count, 2);
    assert!(registry.is_registered("cmdA"));
    assert!(registry.is_registered("cmdB"));
}

#[test]
fn test_batch_register_reject_no_conflict() {
    let mut registry = CommandElabRegistry::new();
    let entries = vec![make_batch_entry("newCmd", 1000)];
    let count = batch_register(&mut registry, &entries, BatchConflictMode::Reject).unwrap();
    assert_eq!(count, 1);
}

#[test]
fn test_batch_register_reject_with_conflict() {
    let mut registry = CommandElabRegistry::new();
    // "simp" is already registered as a builtin.
    let entries = vec![make_batch_entry("simp", 5000)];
    let err = batch_register(&mut registry, &entries, BatchConflictMode::Reject).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("simp"));
    assert!(msg.contains("conflict"));
}

#[test]
fn test_batch_register_reject_rollback() {
    let mut registry = CommandElabRegistry::new();
    let initial_count = registry.kind_count();
    // Mix of new + conflicting entries.
    let entries = vec![
        make_batch_entry("brandNew", 1000),
        make_batch_entry("simp", 5000), // conflict
    ];
    let result = batch_register(&mut registry, &entries, BatchConflictMode::Reject);
    assert!(result.is_err());
    // "brandNew" should NOT have been registered (rollback).
    assert_eq!(registry.kind_count(), initial_count);
}

#[test]
fn test_batch_register_skip_existing() {
    let mut registry = CommandElabRegistry::new();
    let simp_handlers_before = registry.get_handlers("simp").unwrap().len();
    let entries = vec![
        make_batch_entry("simp", 5000),
        make_batch_entry("brandNew", 1000),
    ];
    let count = batch_register(&mut registry, &entries, BatchConflictMode::Skip).unwrap();
    assert_eq!(count, 1); // Only brandNew registered.
    assert!(registry.is_registered("brandNew"));
    // "simp" handlers unchanged.
    assert_eq!(
        registry.get_handlers("simp").unwrap().len(),
        simp_handlers_before
    );
}

#[test]
fn test_batch_register_duplicate_in_batch() {
    let mut registry = CommandElabRegistry::new();
    let entries = vec![make_batch_entry("dup", 1000), make_batch_entry("dup", 2000)];
    let err = batch_register(&mut registry, &entries, BatchConflictMode::Allow).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("duplicate"));
    assert!(msg.contains("dup"));
}

#[test]
fn test_batch_register_empty() {
    let mut registry = CommandElabRegistry::new();
    let count = batch_register(&mut registry, &[], BatchConflictMode::Allow).unwrap();
    assert_eq!(count, 0);
}

// =============================================================================
// Snapshot and diff tests
// =============================================================================

#[test]
fn test_snapshot_captures_all_commands() {
    let registry = CommandElabRegistry::new();
    let snap = snapshot(&registry);
    assert_eq!(snap.entries.len(), registry.kind_count());
    for kind in registry.kinds() {
        assert!(snap.entries.contains_key(kind));
    }
}

#[test]
fn test_snapshot_records_handler_count_and_priority() {
    let registry = CommandElabRegistry::new();
    let snap = snapshot(&registry);
    let (count, priority) = snap.entries.get("simp").unwrap();
    assert_eq!(*count, 1);
    assert_eq!(*priority, 1000);
}

#[test]
fn test_diff_identical_snapshots() {
    let registry = CommandElabRegistry::new();
    let snap = snapshot(&registry);
    let d = diff_snapshots(&snap, &snap);
    assert!(d.is_empty());
    assert_eq!(d.total_changes(), 0);
}

#[test]
fn test_diff_added_command() {
    let registry = CommandElabRegistry::new();
    let before = snapshot(&registry);
    let mut registry2 = CommandElabRegistry::new();
    registry2.register(
        "newCmd",
        CommandElabEntry {
            command_name: "newCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 1000,
        },
    );
    let after = snapshot(&registry2);
    let d = diff_snapshots(&before, &after);
    assert!(d.added.contains("newCmd"));
    assert!(d.removed.is_empty());
}

#[test]
fn test_diff_changed_command() {
    let registry = CommandElabRegistry::new();
    let before = snapshot(&registry);
    let mut registry2 = CommandElabRegistry::new();
    registry2.register(
        "simp",
        CommandElabEntry {
            command_name: "simp".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 5000,
        },
    );
    let after = snapshot(&registry2);
    let d = diff_snapshots(&before, &after);
    assert!(d.changed.contains("simp"));
}

#[test]
fn test_diff_total_changes() {
    let before = RegistrySnapshot {
        entries: [("a".to_owned(), (1, 100)), ("b".to_owned(), (1, 200))]
            .into_iter()
            .collect(),
    };
    let after = RegistrySnapshot {
        entries: [("b".to_owned(), (2, 300)), ("c".to_owned(), (1, 100))]
            .into_iter()
            .collect(),
    };
    let d = diff_snapshots(&before, &after);
    assert!(d.removed.contains("a"));
    assert!(d.added.contains("c"));
    assert!(d.changed.contains("b"));
    assert_eq!(d.total_changes(), 3);
}

// =============================================================================
// Validation tests
// =============================================================================

#[test]
fn test_check_duplicates_no_dups() {
    assert!(check_duplicates(&["a", "b", "c"]).is_ok());
}

#[test]
fn test_check_duplicates_with_dup() {
    let err = check_duplicates(&["a", "b", "a"]).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("duplicate"));
    assert!(msg.contains("a"));
}

#[test]
fn test_check_duplicates_empty() {
    assert!(check_duplicates(&[]).is_ok());
}

#[test]
fn test_validate_registry_clean() {
    let registry = CommandElabRegistry::new();
    let deps = vec![CommandDependency {
        command: "simp".to_owned(),
        depends_on: "reducible".to_owned(),
    }];
    let errors = validate_registry(&registry, &deps);
    assert!(errors.is_empty());
}

#[test]
fn test_validate_registry_missing_dep() {
    let registry = CommandElabRegistry::new();
    let deps = vec![CommandDependency {
        command: "myCmd".to_owned(),
        depends_on: "nonexistent".to_owned(),
    }];
    let errors = validate_registry(&registry, &deps);
    assert!(!errors.is_empty());
    let msg = format!("{}", errors[0]);
    assert!(msg.contains("nonexistent"));
}

#[test]
fn test_validate_registry_circular() {
    let registry = CommandElabRegistry::new();
    let deps = vec![
        CommandDependency {
            command: "a".to_owned(),
            depends_on: "b".to_owned(),
        },
        CommandDependency {
            command: "b".to_owned(),
            depends_on: "a".to_owned(),
        },
    ];
    let errors = validate_registry(&registry, &deps);
    // Should have both missing deps (a, b not registered) and circular.
    assert!(errors.len() >= 2);
}

// =============================================================================
// Error type tests
// =============================================================================

#[test]
fn test_error_display_duplicate() {
    let err = RegistryExtError::DuplicateRegistration {
        name: "foo".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("duplicate"));
    assert!(msg.contains("foo"));
}

#[test]
fn test_error_display_missing_dependency() {
    let err = RegistryExtError::MissingDependency {
        command: "a".to_owned(),
        dependency: "b".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("a"));
    assert!(msg.contains("b"));
    assert!(msg.contains("depends on"));
}

#[test]
fn test_error_display_circular() {
    let err = RegistryExtError::CircularDependency {
        cycle: "x".to_owned(),
    };
    let msg = format!("{err}");
    assert!(msg.contains("circular"));
}

#[test]
fn test_error_display_batch_conflict() {
    let err = RegistryExtError::BatchConflict {
        name: "cmd".to_owned(),
        existing_priority: 1000,
    };
    let msg = format!("{err}");
    assert!(msg.contains("cmd"));
    assert!(msg.contains("1000"));
}
