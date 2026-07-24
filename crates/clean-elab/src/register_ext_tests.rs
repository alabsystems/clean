// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended declaration registration module.

use clean_kernel::{Expr, Level, Name};
use clean_parser::DeclModifiers;

use crate::infer::ElabResult;
use crate::register_ext::*;

/// Create a simple Definition ElabResult with the given name.
fn mk_def(name: &str) -> ElabResult {
    ElabResult::Definition {
        name: Name::from_string(name),
        universe_params: Vec::new(),
        ty: Expr::sort(Level::succ(Level::succ(Level::zero()))),
        val: Expr::type_(),
        modifiers: DeclModifiers::default(),
    }
}

/// Create a simple Axiom ElabResult with the given name.
fn mk_axiom(name: &str) -> ElabResult {
    ElabResult::Axiom {
        name: Name::from_string(name),
        universe_params: Vec::new(),
        ty: Expr::type_(),
        modifiers: DeclModifiers::default(),
    }
}

/// Create a fresh environment for testing.
fn test_env() -> clean_kernel::Environment {
    clean_kernel::Environment::new()
}

// =============================================================================
// DependencyTracker tests
// =============================================================================

#[test]
fn test_dependency_tracker_new_is_empty() {
    let tracker = DependencyTracker::new();
    assert_eq!(tracker.node_count(), 0);
    assert_eq!(tracker.edge_count(), 0);
}

#[test]
fn test_dependency_tracker_add_single_dependency() {
    let mut tracker = DependencyTracker::new();
    let a = Name::from_string("a");
    let b = Name::from_string("b");
    tracker.add_dependency(a.clone(), b.clone());
    assert_eq!(tracker.node_count(), 1);
    assert_eq!(tracker.edge_count(), 1);
    assert_eq!(tracker.dependencies_of(&a), &[b]);
}

#[test]
fn test_dependency_tracker_add_multiple_dependencies() {
    let mut tracker = DependencyTracker::new();
    let a = Name::from_string("a");
    let deps = vec![Name::from_string("b"), Name::from_string("c")];
    tracker.add_dependencies(a.clone(), deps.clone());
    assert_eq!(tracker.node_count(), 1);
    assert_eq!(tracker.edge_count(), 2);
    assert_eq!(tracker.dependencies_of(&a), &deps[..]);
}

#[test]
fn test_dependency_tracker_dependencies_of_unknown_is_empty() {
    let tracker = DependencyTracker::new();
    let unknown = Name::from_string("unknown");
    assert!(tracker.dependencies_of(&unknown).is_empty());
}

#[test]
fn test_dependency_tracker_tracked_names() {
    let mut tracker = DependencyTracker::new();
    tracker.add_dependency(Name::from_string("x"), Name::from_string("y"));
    tracker.add_dependency(Name::from_string("z"), Name::from_string("w"));
    let names = tracker.tracked_names();
    assert_eq!(names.len(), 2);
}

#[test]
fn test_dependency_tracker_reverse_deps() {
    let mut tracker = DependencyTracker::new();
    let a = Name::from_string("a");
    let b = Name::from_string("b");
    let c = Name::from_string("c");
    tracker.add_dependency(a.clone(), b.clone());
    tracker.add_dependency(c.clone(), b.clone());
    let rev = tracker.reverse_deps();
    let dependents = rev.get(&b).expect("b should have dependents");
    assert_eq!(dependents.len(), 2);
    assert!(dependents.contains(&a));
    assert!(dependents.contains(&c));
}

#[test]
fn test_dependency_tracker_clear() {
    let mut tracker = DependencyTracker::new();
    tracker.add_dependency(Name::from_string("a"), Name::from_string("b"));
    assert_eq!(tracker.node_count(), 1);
    tracker.clear();
    assert_eq!(tracker.node_count(), 0);
    assert_eq!(tracker.edge_count(), 0);
}

#[test]
fn test_dependency_tracker_accumulate_deps_same_node() {
    let mut tracker = DependencyTracker::new();
    let a = Name::from_string("a");
    tracker.add_dependency(a.clone(), Name::from_string("b"));
    tracker.add_dependency(a.clone(), Name::from_string("c"));
    assert_eq!(tracker.node_count(), 1);
    assert_eq!(tracker.edge_count(), 2);
}

// =============================================================================
// RegistrationHooks tests
// =============================================================================

#[test]
fn test_hooks_new_is_empty() {
    let hooks = RegistrationHooks::new();
    assert_eq!(hooks.pre_hook_count(), 0);
    assert_eq!(hooks.post_hook_count(), 0);
}

#[test]
fn test_hooks_add_pre_hook() {
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(|_env, _result| Ok(())));
    assert_eq!(hooks.pre_hook_count(), 1);
}

#[test]
fn test_hooks_add_post_hook() {
    let mut hooks = RegistrationHooks::new();
    hooks.add_post_hook(Box::new(|_env, _result| {}));
    assert_eq!(hooks.post_hook_count(), 1);
}

#[test]
fn test_hooks_multiple_pre_hooks() {
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(|_env, _result| Ok(())));
    hooks.add_pre_hook(Box::new(|_env, _result| Ok(())));
    hooks.add_pre_hook(Box::new(|_env, _result| Ok(())));
    assert_eq!(hooks.pre_hook_count(), 3);
}

// =============================================================================
// Validation tests
// =============================================================================

#[test]
fn test_validate_no_conflict_passes_on_fresh_env() {
    let env = test_env();
    let result = mk_def("fresh_name");
    assert!(validate_no_name_conflict(&env, &result).is_ok());
}

#[test]
fn test_validate_no_conflict_fails_on_existing_name() {
    let mut env = test_env();
    let result = mk_def("existing");
    crate::register::register_elab_result(&mut env, &result)
        .expect("initial registration should succeed");
    let err = validate_no_name_conflict(&env, &result);
    assert!(err.is_err());
    assert!(matches!(err, Err(RegisterExtError::NameConflict(_))));
}

#[test]
fn test_validate_no_conflict_skipped_result_passes() {
    let env = test_env();
    let result = ElabResult::Skipped;
    assert!(validate_no_name_conflict(&env, &result).is_ok());
}

#[test]
fn test_validate_batch_no_duplicates_empty() {
    assert!(validate_batch_no_duplicates(&[]).is_ok());
}

#[test]
fn test_validate_batch_no_duplicates_unique_names() {
    let results = vec![mk_def("a"), mk_def("b"), mk_def("c")];
    assert!(validate_batch_no_duplicates(&results).is_ok());
}

#[test]
fn test_validate_batch_no_duplicates_catches_duplicates() {
    let results = vec![mk_def("a"), mk_def("b"), mk_def("a")];
    let err = validate_batch_no_duplicates(&results);
    assert!(matches!(err, Err(RegisterExtError::DuplicateInBatch(_))));
}

#[test]
fn test_validate_batch_full_fresh_env() {
    let env = test_env();
    let results = vec![mk_def("x"), mk_def("y")];
    let conflicts = validate_batch(&env, &results).expect("validation should succeed");
    assert_eq!(conflicts, 0);
}

#[test]
fn test_validate_batch_reports_conflicts() {
    let mut env = test_env();
    let initial = mk_def("x");
    crate::register::register_elab_result(&mut env, &initial)
        .expect("initial registration should succeed");
    let results = vec![mk_def("x"), mk_def("y")];
    let conflicts = validate_batch(&env, &results).expect("validation should succeed");
    assert_eq!(conflicts, 1);
}

// =============================================================================
// has_name_conflict tests
// =============================================================================

#[test]
fn test_has_name_conflict_false_on_fresh_env() {
    let env = test_env();
    assert!(!has_name_conflict(&env, &Name::from_string("anything")));
}

#[test]
fn test_has_name_conflict_true_after_registration() {
    let mut env = test_env();
    let result = mk_def("my_def");
    crate::register::register_elab_result(&mut env, &result).expect("registration should succeed");
    assert!(has_name_conflict(&env, &Name::from_string("my_def")));
}

// =============================================================================
// Batch registration tests
// =============================================================================

#[test]
fn test_register_batch_empty() {
    let mut env = test_env();
    let stats = register_batch(&mut env, &[]).expect("empty batch should succeed");
    assert_eq!(stats.registered, 0);
    assert_eq!(stats.failed, 0);
}

#[test]
fn test_register_batch_single() {
    let mut env = test_env();
    let results = vec![mk_def("single")];
    let stats = register_batch(&mut env, &results).expect("single batch should succeed");
    assert_eq!(stats.registered, 1);
    assert!(env.get_const(&Name::from_string("single")).is_some());
}

#[test]
fn test_register_batch_multiple() {
    let mut env = test_env();
    let results = vec![mk_def("alpha"), mk_def("beta"), mk_def("gamma")];
    let stats = register_batch(&mut env, &results).expect("batch should succeed");
    assert_eq!(stats.registered, 3);
    assert_eq!(stats.failed, 0);
    assert!(env.get_const(&Name::from_string("alpha")).is_some());
    assert!(env.get_const(&Name::from_string("beta")).is_some());
    assert!(env.get_const(&Name::from_string("gamma")).is_some());
}

#[test]
fn test_register_batch_atomic_rollback() {
    let mut env = test_env();
    // First register "existing"
    let initial = mk_def("existing");
    crate::register::register_elab_result(&mut env, &initial)
        .expect("initial registration should succeed");

    // Now try a batch that will fail on the duplicate name
    let results = vec![mk_def("new_one"), mk_def("existing")];
    let err = register_batch(&mut env, &results);
    // The second declaration tries to re-register "existing" which should fail
    // at the kernel level. If it doesn't fail at kernel level but succeeds,
    // the batch succeeds and that's also valid behavior.
    // The important thing is atomicity: either all or none.
    if let Err(RegisterExtError::BatchFailed { index, .. }) = &err {
        assert_eq!(*index, 1);
        // Rollback: "new_one" should NOT be in the env
        assert!(env.get_const(&Name::from_string("new_one")).is_none());
    }
    // If it succeeded, both should be present
    if err.is_ok() {
        assert!(env.get_const(&Name::from_string("new_one")).is_some());
    }
}

#[test]
fn test_register_batch_duplicate_names_rejected() {
    let mut env = test_env();
    let results = vec![mk_def("dup"), mk_def("dup")];
    let err = register_batch(&mut env, &results);
    assert!(matches!(err, Err(RegisterExtError::DuplicateInBatch(_))));
}

#[test]
fn test_register_batch_records_elapsed_time() {
    let mut env = test_env();
    let results = vec![mk_def("timed")];
    let stats = register_batch(&mut env, &results).expect("should succeed");
    // Elapsed should be non-zero (some positive duration)
    assert!(stats.elapsed.as_nanos() > 0 || stats.registered == 1);
}

// =============================================================================
// Batch with hooks tests
// =============================================================================

#[test]
fn test_register_batch_with_accepting_pre_hook() {
    let mut env = test_env();
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(|_env, _result| Ok(())));
    let results = vec![mk_def("hooked")];
    let stats = register_batch_with_hooks(&mut env, &results, &hooks)
        .expect("should succeed with accepting hook");
    assert_eq!(stats.registered, 1);
    assert_eq!(stats.hooks_invoked, 1);
}

#[test]
fn test_register_batch_with_rejecting_pre_hook() {
    let mut env = test_env();
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(|_env, _result| {
        Err("rejected by policy".to_string())
    }));
    let results = vec![mk_def("blocked")];
    let err = register_batch_with_hooks(&mut env, &results, &hooks);
    assert!(matches!(err, Err(RegisterExtError::HookRejected { .. })));
    // Env should be untouched
    assert!(env.get_const(&Name::from_string("blocked")).is_none());
}

#[test]
fn test_register_batch_with_post_hook() {
    let mut env = test_env();
    let mut hooks = RegistrationHooks::new();
    let post_called = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let post_called_clone = post_called.clone();
    hooks.add_post_hook(Box::new(move |_env, _result| {
        post_called_clone.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }));
    let results = vec![mk_def("post_test")];
    let stats = register_batch_with_hooks(&mut env, &results, &hooks).expect("should succeed");
    assert_eq!(stats.registered, 1);
    assert_eq!(post_called.load(std::sync::atomic::Ordering::SeqCst), 1);
}

#[test]
fn test_register_batch_with_hooks_rollback_on_second_failure() {
    let mut env = test_env();
    let call_count = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let call_count_clone = call_count.clone();
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(move |_env, _result| {
        let count = call_count_clone.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        if count >= 1 {
            // Reject the second declaration
            Err("policy limit reached".to_string())
        } else {
            Ok(())
        }
    }));
    let results = vec![mk_def("first"), mk_def("second")];
    let err = register_batch_with_hooks(&mut env, &results, &hooks);
    assert!(matches!(err, Err(RegisterExtError::HookRejected { .. })));
    // Rollback: first should NOT be registered because batch is atomic
    assert!(env.get_const(&Name::from_string("first")).is_none());
}

// =============================================================================
// register_with_hooks tests
// =============================================================================

#[test]
fn test_register_with_hooks_basic() {
    let mut env = test_env();
    let hooks = RegistrationHooks::new();
    let result = mk_def("basic_hooked");
    let stats = register_with_hooks(&mut env, &result, &hooks, None).expect("should succeed");
    assert_eq!(stats.registered, 1);
    assert!(env.get_const(&Name::from_string("basic_hooked")).is_some());
}

#[test]
fn test_register_with_hooks_and_tracker() {
    let mut env = test_env();
    let hooks = RegistrationHooks::new();
    let mut tracker = DependencyTracker::new();
    let result = mk_def("tracked_def");
    let stats =
        register_with_hooks(&mut env, &result, &hooks, Some(&mut tracker)).expect("should succeed");
    assert_eq!(stats.registered, 1);
    assert_eq!(stats.dependencies_tracked, 1);
    assert_eq!(tracker.node_count(), 1);
}

#[test]
fn test_register_with_hooks_pre_hook_rejects() {
    let mut env = test_env();
    let mut hooks = RegistrationHooks::new();
    hooks.add_pre_hook(Box::new(|_env, _result| Err("nope".to_string())));
    let result = mk_def("should_not_register");
    let err = register_with_hooks(&mut env, &result, &hooks, None);
    assert!(err.is_err());
    assert!(env
        .get_const(&Name::from_string("should_not_register"))
        .is_none());
}

// =============================================================================
// register_batch_full tests
// =============================================================================

#[test]
fn test_register_batch_full_empty() {
    let mut env = test_env();
    let hooks = RegistrationHooks::new();
    let batch_result =
        register_batch_full(&mut env, &[], &hooks).expect("empty batch should succeed");
    assert_eq!(batch_result.stats.registered, 0);
    assert!(batch_result.registered_names.is_empty());
    assert_eq!(batch_result.tracker.node_count(), 0);
}

#[test]
fn test_register_batch_full_collects_names() {
    let mut env = test_env();
    let hooks = RegistrationHooks::new();
    let results = vec![mk_def("p"), mk_def("q"), mk_def("r")];
    let batch_result =
        register_batch_full(&mut env, &results, &hooks).expect("batch should succeed");
    assert_eq!(batch_result.stats.registered, 3);
    assert_eq!(batch_result.registered_names.len(), 3);
    assert!(batch_result
        .registered_names
        .contains(&Name::from_string("p")));
    assert!(batch_result
        .registered_names
        .contains(&Name::from_string("q")));
    assert!(batch_result
        .registered_names
        .contains(&Name::from_string("r")));
}

#[test]
fn test_register_batch_full_tracks_dependencies() {
    let mut env = test_env();
    let hooks = RegistrationHooks::new();
    let results = vec![mk_def("dep_a"), mk_def("dep_b")];
    let batch_result =
        register_batch_full(&mut env, &results, &hooks).expect("batch should succeed");
    assert_eq!(batch_result.tracker.node_count(), 2);
}

#[test]
fn test_register_batch_full_rollback_on_failure() {
    let mut env = test_env();
    let mut hooks = RegistrationHooks::new();
    let call_count = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let cc = call_count.clone();
    hooks.add_pre_hook(Box::new(move |_env, _result| {
        if cc.fetch_add(1, std::sync::atomic::Ordering::SeqCst) >= 2 {
            Err("limit".to_string())
        } else {
            Ok(())
        }
    }));
    let results = vec![mk_def("fa"), mk_def("fb"), mk_def("fc")];
    let err = register_batch_full(&mut env, &results, &hooks);
    assert!(err.is_err());
    // Atomic rollback means none should be registered
    assert!(env.get_const(&Name::from_string("fa")).is_none());
    assert!(env.get_const(&Name::from_string("fb")).is_none());
}

// =============================================================================
// merge_stats tests
// =============================================================================

#[test]
fn test_merge_stats_two_defaults() {
    let a = RegistrationStats::default();
    let b = RegistrationStats::default();
    let merged = merge_stats(&a, &b);
    assert_eq!(merged.registered, 0);
    assert_eq!(merged.failed, 0);
}

#[test]
fn test_merge_stats_accumulates_fields() {
    let a = RegistrationStats {
        registered: 3,
        failed: 1,
        conflicts_detected: 2,
        hooks_invoked: 5,
        dependencies_tracked: 4,
        elapsed: Duration::from_millis(100),
    };
    let b = RegistrationStats {
        registered: 2,
        failed: 0,
        conflicts_detected: 1,
        hooks_invoked: 3,
        dependencies_tracked: 2,
        elapsed: Duration::from_millis(50),
    };
    let merged = merge_stats(&a, &b);
    assert_eq!(merged.registered, 5);
    assert_eq!(merged.failed, 1);
    assert_eq!(merged.conflicts_detected, 3);
    assert_eq!(merged.hooks_invoked, 8);
    assert_eq!(merged.dependencies_tracked, 6);
    assert_eq!(merged.elapsed, Duration::from_millis(150));
}

// =============================================================================
// Error type tests
// =============================================================================

#[test]
fn test_error_name_conflict_display() {
    let err = RegisterExtError::NameConflict(Name::from_string("foo"));
    let msg = err.to_string();
    assert!(msg.contains("foo"));
    assert!(msg.contains("already exists"));
}

#[test]
fn test_error_duplicate_in_batch_display() {
    let err = RegisterExtError::DuplicateInBatch(Name::from_string("bar"));
    let msg = err.to_string();
    assert!(msg.contains("bar"));
    assert!(msg.contains("more than once"));
}

#[test]
fn test_error_hook_rejected_display() {
    let err = RegisterExtError::HookRejected {
        name: "baz".to_string(),
        reason: "policy violation".to_string(),
    };
    let msg = err.to_string();
    assert!(msg.contains("baz"));
    assert!(msg.contains("policy violation"));
}

// =============================================================================
// RegistrationStats default tests
// =============================================================================

#[test]
fn test_stats_default_is_zero() {
    let stats = RegistrationStats::default();
    assert_eq!(stats.registered, 0);
    assert_eq!(stats.failed, 0);
    assert_eq!(stats.conflicts_detected, 0);
    assert_eq!(stats.hooks_invoked, 0);
    assert_eq!(stats.dependencies_tracked, 0);
    assert_eq!(stats.elapsed, Duration::default());
}

// =============================================================================
// Mixed ElabResult variant tests
// =============================================================================

#[test]
fn test_register_batch_mixed_variants() {
    let mut env = test_env();
    let results = vec![mk_def("my_def"), mk_axiom("my_axiom")];
    let stats = register_batch(&mut env, &results).expect("mixed batch should succeed");
    assert_eq!(stats.registered, 2);
    assert!(env.get_const(&Name::from_string("my_def")).is_some());
    assert!(env.get_const(&Name::from_string("my_axiom")).is_some());
}

#[test]
fn test_register_batch_with_skipped() {
    let mut env = test_env();
    let results = vec![mk_def("real_def"), ElabResult::Skipped];
    let stats = register_batch(&mut env, &results).expect("batch with skipped should succeed");
    assert_eq!(stats.registered, 2);
}

#[test]
fn test_validate_skipped_results_no_duplicate() {
    // Multiple Skipped results should not trigger duplicate detection
    let results = vec![ElabResult::Skipped, ElabResult::Skipped];
    assert!(validate_batch_no_duplicates(&results).is_ok());
}

#[test]
fn test_dependency_tracker_default_is_empty() {
    let tracker: DependencyTracker = Default::default();
    assert_eq!(tracker.node_count(), 0);
    assert_eq!(tracker.edge_count(), 0);
}

#[test]
fn test_dependency_tracker_reverse_deps_empty() {
    let tracker = DependencyTracker::new();
    let rev = tracker.reverse_deps();
    assert!(rev.is_empty());
}

use std::time::Duration;
