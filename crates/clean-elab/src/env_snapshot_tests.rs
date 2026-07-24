// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`env_snapshot`] — environment snapshotting and rollback.

use std::collections::HashSet;

use crate::env_snapshot::{EnvSnapshot, EnvSnapshotManager, SpeculativeResult};
use crate::error::ElabError;
use clean_kernel::Environment;

/// Helper: build a fresh environment for testing.
fn test_env() -> Environment {
    Environment::new()
}

// ---------------------------------------------------------------------------
// EnvSnapshot tests
// ---------------------------------------------------------------------------

#[test]
fn test_take_snapshot_captures_state() {
    let env = test_env();
    let snap = EnvSnapshot::take(&env);
    assert_eq!(snap.decl_count(), env.num_constants());
    assert_eq!(snap.instance_count(), env.num_instances());
    assert_eq!(snap.simp_lemma_count(), env.get_simp_lemmas().count());
    assert_eq!(snap.aesop_rule_count(), 0);
    assert!(snap.option_keys().is_empty());
}

#[test]
fn test_take_with_options_preserves_keys() {
    let env = test_env();
    let mut keys = HashSet::new();
    keys.insert("pp.all".to_string());
    keys.insert("pp.notation".to_string());
    let snap = EnvSnapshot::take_with_options(&env, keys.clone());
    assert_eq!(snap.option_keys(), &keys);
    assert_eq!(snap.option_keys().len(), 2);
}

#[test]
fn test_snapshot_age_increases_over_time() {
    let env = test_env();
    let snap = EnvSnapshot::take(&env);
    // Spin briefly to ensure some time passes.
    let start = std::time::Instant::now();
    while start.elapsed().as_nanos() < 100 {
        std::hint::spin_loop();
    }
    let age = snap.age();
    // Age should be at least 100ns (practically always true).
    assert!(age.as_nanos() > 0, "age should be positive");
}

// ---------------------------------------------------------------------------
// EnvSnapshotManager basic operations
// ---------------------------------------------------------------------------

#[test]
fn test_manager_new_starts_empty() {
    let mgr = EnvSnapshotManager::new(4);
    assert_eq!(mgr.snapshot_count(), 0);
    assert!(mgr.peek_snapshot().is_none());
}

#[test]
fn test_push_and_pop_snapshots_lifo() {
    let mut env = test_env();
    env.set_option("a".to_string(), None);
    let mut mgr = EnvSnapshotManager::new(8);

    let snap_a = EnvSnapshot::take_with_options(&env, ["a".to_string()].into_iter().collect());
    env.set_option("b".to_string(), None);
    let snap_b = EnvSnapshot::take_with_options(
        &env,
        ["a".to_string(), "b".to_string()].into_iter().collect(),
    );

    mgr.push_snapshot(snap_a);
    mgr.push_snapshot(snap_b);
    assert_eq!(mgr.snapshot_count(), 2);

    // Pop should return snap_b first (most recent).
    let popped_b = mgr.pop_snapshot().expect("should have snapshot");
    assert_eq!(popped_b.option_keys().len(), 2);

    // Then snap_a.
    let popped_a = mgr.pop_snapshot().expect("should have snapshot");
    assert_eq!(popped_a.option_keys().len(), 1);

    assert_eq!(mgr.snapshot_count(), 0);
}

#[test]
fn test_max_snapshots_limit() {
    let env = test_env();
    let mut mgr = EnvSnapshotManager::new(2);

    let snap1 = EnvSnapshot::take_with_options(&env, ["first".to_string()].into_iter().collect());
    let snap2 = EnvSnapshot::take_with_options(&env, ["second".to_string()].into_iter().collect());
    let snap3 = EnvSnapshot::take_with_options(&env, ["third".to_string()].into_iter().collect());

    mgr.push_snapshot(snap1);
    mgr.push_snapshot(snap2);
    assert_eq!(mgr.snapshot_count(), 2);

    // Pushing a third should evict the oldest (snap1 with "first").
    mgr.push_snapshot(snap3);
    assert_eq!(mgr.snapshot_count(), 2);

    // Pop order: snap3 (third), snap2 (second). snap1 was evicted.
    let p1 = mgr.pop_snapshot().expect("should have snapshot");
    assert!(p1.option_keys().contains("third"));

    let p2 = mgr.pop_snapshot().expect("should have snapshot");
    assert!(p2.option_keys().contains("second"));

    assert!(mgr.pop_snapshot().is_none());
}

// ---------------------------------------------------------------------------
// Speculative execution tests
// ---------------------------------------------------------------------------

#[test]
fn test_speculative_success_keeps_changes() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);

    let result = mgr.speculative(&mut env, |e| {
        e.set_option("spec.key".to_string(), Some("value".to_string()));
        Ok(42)
    });

    match result {
        SpeculativeResult::Success(v) => assert_eq!(v, 42),
        _ => panic!("expected SpeculativeResult::Success"),
    }

    // Change should be kept.
    assert_eq!(env.get_option("spec.key"), Some(&Some("value".to_string())));
    // No snapshot pushed on success.
    assert_eq!(mgr.snapshot_count(), 0);
}

#[test]
fn test_speculative_failure_rolls_back() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);

    // Set baseline option.
    env.set_option("baseline".to_string(), Some("yes".to_string()));

    let result: SpeculativeResult<()> = mgr.speculative(&mut env, |e| {
        e.set_option("transient".to_string(), Some("oops".to_string()));
        Err(ElabError::CannotInfer)
    });

    match result {
        SpeculativeResult::Failure { error, snapshot } => {
            assert!(matches!(error, ElabError::CannotInfer));
            // Snapshot decl_count should match the pre-speculation state.
            assert_eq!(snapshot.decl_count(), env.num_constants());
        }
        _ => panic!("expected SpeculativeResult::Failure"),
    }

    // Rolled back: "transient" should be gone.
    assert!(env.get_option("transient").is_none());
    // "baseline" should still be present.
    assert_eq!(env.get_option("baseline"), Some(&Some("yes".to_string())));
    // Failure pushes one snapshot.
    assert_eq!(mgr.snapshot_count(), 1);
}

#[test]
fn test_peek_without_consuming() {
    let env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);
    mgr.push_snapshot(EnvSnapshot::take(&env));

    // Peek twice — should not consume.
    let p1 = mgr.peek_snapshot();
    assert!(p1.is_some());
    let p2 = mgr.peek_snapshot();
    assert!(p2.is_some());
    assert_eq!(mgr.snapshot_count(), 1);
}

#[test]
fn test_clear_all_snapshots() {
    let env = test_env();
    let mut mgr = EnvSnapshotManager::new(8);
    for _ in 0..5 {
        mgr.push_snapshot(EnvSnapshot::take(&env));
    }
    assert_eq!(mgr.snapshot_count(), 5);

    mgr.clear();
    assert_eq!(mgr.snapshot_count(), 0);
    assert!(mgr.peek_snapshot().is_none());
    assert!(mgr.pop_snapshot().is_none());
}

#[test]
fn test_snapshot_count_tracking() {
    let env = test_env();
    let mut mgr = EnvSnapshotManager::new(16);

    assert_eq!(mgr.snapshot_count(), 0);
    for expected in 1..=6 {
        mgr.push_snapshot(EnvSnapshot::take(&env));
        assert_eq!(mgr.snapshot_count(), expected);
    }
    for expected in (0..6).rev() {
        mgr.pop_snapshot();
        assert_eq!(mgr.snapshot_count(), expected);
    }
}

#[test]
fn test_empty_manager_operations() {
    let mut mgr = EnvSnapshotManager::new(4);

    assert_eq!(mgr.snapshot_count(), 0);
    assert!(mgr.peek_snapshot().is_none());
    assert!(mgr.pop_snapshot().is_none());

    // Clear on empty should be harmless.
    mgr.clear();
    assert_eq!(mgr.snapshot_count(), 0);
}

#[test]
fn test_nested_snapshots() {
    let env = test_env();
    let mut mgr = EnvSnapshotManager::new(8);

    // Simulate nested speculation by pushing multiple snapshots.
    mgr.push_snapshot(EnvSnapshot::take(&env));
    mgr.push_snapshot(EnvSnapshot::take(&env));
    mgr.push_snapshot(EnvSnapshot::take(&env));
    assert_eq!(mgr.snapshot_count(), 3);

    // Unwinding nested speculation — pop in reverse.
    mgr.pop_snapshot();
    assert_eq!(mgr.snapshot_count(), 2);
    mgr.pop_snapshot();
    assert_eq!(mgr.snapshot_count(), 1);
    mgr.pop_snapshot();
    assert_eq!(mgr.snapshot_count(), 0);
}

#[test]
fn test_multiple_speculative_attempts() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(8);

    // Attempt 1: failure.
    let _r1: SpeculativeResult<()> = mgr.speculative(&mut env, |e| {
        e.set_option("attempt1".to_string(), None);
        Err(ElabError::CannotInfer)
    });
    assert!(env.get_option("attempt1").is_none());
    assert_eq!(mgr.snapshot_count(), 1);

    // Attempt 2: success.
    let _r2 = mgr.speculative(&mut env, |e| {
        e.set_option("attempt2".to_string(), Some("ok".to_string()));
        Ok("good")
    });
    assert!(env.get_option("attempt2").is_some());
    assert_eq!(mgr.snapshot_count(), 1); // success doesn't push

    // Attempt 3: failure.
    let _r3: SpeculativeResult<()> = mgr.speculative(&mut env, |e| {
        e.set_option("attempt3".to_string(), None);
        Err(ElabError::NotImplemented("test".into()))
    });
    assert!(env.get_option("attempt3").is_none());
    assert!(env.get_option("attempt2").is_some()); // preserved
    assert_eq!(mgr.snapshot_count(), 2);
}

#[test]
fn test_speculative_with_warnings_partial_result() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);

    let result = mgr.speculative_with_warnings(&mut env, |e| {
        e.set_option("warned.opt".to_string(), Some("v".to_string()));
        Ok((100, vec!["Warning: deprecated path".to_string()]))
    });

    match result {
        SpeculativeResult::Partial { result, warnings } => {
            assert_eq!(result, 100);
            assert_eq!(warnings.len(), 1);
            assert!(warnings[0].contains("deprecated"));
        }
        _ => panic!("expected SpeculativeResult::Partial"),
    }
    // Changes kept on partial success.
    assert!(env.get_option("warned.opt").is_some());
}

#[test]
fn test_speculative_with_warnings_empty_is_success() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);

    let result = mgr.speculative_with_warnings(&mut env, |_e| Ok((7, vec![])));

    match result {
        SpeculativeResult::Success(v) => assert_eq!(v, 7),
        _ => panic!("expected SpeculativeResult::Success when warnings empty"),
    }
}

#[test]
fn test_speculative_with_warnings_failure_rolls_back() {
    let mut env = test_env();
    let mut mgr = EnvSnapshotManager::new(4);

    let result: SpeculativeResult<i32> = mgr.speculative_with_warnings(&mut env, |e| {
        e.set_option("gone".to_string(), None);
        Err(ElabError::CannotInfer)
    });

    assert!(matches!(result, SpeculativeResult::Failure { .. }));
    assert!(env.get_option("gone").is_none());
    assert_eq!(mgr.snapshot_count(), 1);
}
