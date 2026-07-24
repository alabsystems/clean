// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`env_snapshot_ext`] — extended environment snapshot management.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use crate::env_snapshot_ext::{
    Checkpoint, CompressedSnapshot, DeclFingerprint, EnvironmentDiff, ExtSnapshotConfig,
    ExtSnapshotManager, MergeResult, SerializedSnapshot,
};
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

/// Helper: fresh empty environment.
fn test_env() -> Environment {
    Environment::new()
}

/// Helper: add an axiom declaration to the environment.
fn add_axiom(env: &mut Environment, name: &str) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("should add axiom");
}

// ---- Checkpoint save/restore ------------------------------------------------

#[test]
fn test_checkpoint_empty_env() {
    let env = test_env();
    let cp = Checkpoint::take(&env, "empty", true);
    assert_eq!(cp.label(), "empty");
    assert_eq!(cp.decl_count(), env.num_constants());
    assert!(cp.decl_names().is_empty() || cp.decl_count() == cp.decl_names().len());
}

#[test]
fn test_checkpoint_captures_declarations() {
    let mut env = test_env();
    add_axiom(&mut env, "A");
    add_axiom(&mut env, "B");
    let cp = Checkpoint::take(&env, "two_decls", true);
    assert_eq!(cp.decl_count(), env.num_constants());
    assert!(cp.decl_names().contains(&Name::from_string("A")));
    assert!(cp.decl_names().contains(&Name::from_string("B")));
}

#[test]
fn test_checkpoint_without_fingerprints() {
    let mut env = test_env();
    add_axiom(&mut env, "X");
    let cp = Checkpoint::take(&env, "no_fp", false);
    assert_eq!(cp.decl_count(), env.num_constants());
    // No fingerprints computed but names still captured.
    assert!(cp.decl_names().contains(&Name::from_string("X")));
}

#[test]
fn test_manager_save_and_get_checkpoint() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "init");
    assert_eq!(mgr.checkpoint_count(), 1);
    assert!(mgr.get_checkpoint("init").is_some());
    assert!(mgr.get_checkpoint("nonexistent").is_none());
}

#[test]
fn test_manager_checkpoint_overwrite() {
    let mut env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "cp");
    let count_before = mgr.get_checkpoint("cp").unwrap().decl_count();
    add_axiom(&mut env, "extra");
    mgr.save_checkpoint(&env, "cp");
    let count_after = mgr.get_checkpoint("cp").unwrap().decl_count();
    assert!(count_after > count_before);
    assert_eq!(mgr.checkpoint_count(), 1);
}

#[test]
fn test_manager_evicts_oldest_at_capacity() {
    let env = test_env();
    let config = ExtSnapshotConfig {
        max_checkpoints: 3,
        auto_fingerprint: false,
        track_stats: true,
    };
    let mut mgr = ExtSnapshotManager::new(config);
    mgr.save_checkpoint(&env, "a");
    mgr.save_checkpoint(&env, "b");
    mgr.save_checkpoint(&env, "c");
    assert_eq!(mgr.checkpoint_count(), 3);
    mgr.save_checkpoint(&env, "d");
    assert_eq!(mgr.checkpoint_count(), 3);
    assert!(
        mgr.get_checkpoint("a").is_none(),
        "oldest should be evicted"
    );
    assert!(mgr.get_checkpoint("d").is_some());
}

#[test]
fn test_checkpoint_labels_order() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "first");
    mgr.save_checkpoint(&env, "second");
    mgr.save_checkpoint(&env, "third");
    assert_eq!(mgr.checkpoint_labels(), &["first", "second", "third"]);
}

// ---- Environment diffing ----------------------------------------------------

#[test]
fn test_diff_empty_no_changes() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "base");
    let diff = mgr.diff_from_checkpoint("base", &env).unwrap();
    assert!(diff.is_empty());
    assert_eq!(diff.total_changes(), 0);
}

#[test]
fn test_diff_detects_added_declarations() {
    let mut env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "base");
    add_axiom(&mut env, "NewDecl");
    let diff = mgr.diff_from_checkpoint("base", &env).unwrap();
    assert!(!diff.is_empty());
    assert!(diff.added.contains(&Name::from_string("NewDecl")));
}

#[test]
fn test_diff_detects_multiple_additions() {
    let mut env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "base");
    add_axiom(&mut env, "D1");
    add_axiom(&mut env, "D2");
    add_axiom(&mut env, "D3");
    let diff = mgr.diff_from_checkpoint("base", &env).unwrap();
    assert_eq!(diff.added.len(), 3);
}

#[test]
fn test_diff_nonexistent_checkpoint_returns_none() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    assert!(mgr.diff_from_checkpoint("nope", &env).is_none());
}

#[test]
fn test_diff_between_directly() {
    let mut env = test_env();
    add_axiom(&mut env, "Pre");
    let cp = Checkpoint::take(&env, "snap", true);
    add_axiom(&mut env, "Post");
    let diff = EnvironmentDiff::between(&cp, &env);
    assert!(diff.added.contains(&Name::from_string("Post")));
    assert!(diff.removed.is_empty());
}

// ---- Environment merging ----------------------------------------------------

#[test]
fn test_merge_non_conflicting() {
    let diff_a = EnvironmentDiff {
        added: vec![Name::from_string("A1"), Name::from_string("A2")],
        removed: vec![],
        modified: vec![],
    };
    let diff_b = EnvironmentDiff {
        added: vec![Name::from_string("B1")],
        removed: vec![],
        modified: vec![],
    };
    let result = MergeResult::merge(&diff_a, &diff_b);
    assert!(result.is_clean());
    assert_eq!(result.from_a.len(), 2);
    assert_eq!(result.from_b.len(), 1);
}

#[test]
fn test_merge_with_conflict() {
    let diff_a = EnvironmentDiff {
        added: vec![Name::from_string("Shared"), Name::from_string("OnlyA")],
        removed: vec![],
        modified: vec![],
    };
    let diff_b = EnvironmentDiff {
        added: vec![Name::from_string("Shared"), Name::from_string("OnlyB")],
        removed: vec![],
        modified: vec![],
    };
    let result = MergeResult::merge(&diff_a, &diff_b);
    assert!(!result.is_clean());
    assert_eq!(result.conflicts.len(), 1);
    assert_eq!(result.conflicts[0].name, Name::from_string("Shared"));
    assert_eq!(result.from_a, vec![Name::from_string("OnlyA")]);
    assert_eq!(result.from_b, vec![Name::from_string("OnlyB")]);
}

#[test]
fn test_merge_both_empty() {
    let empty = EnvironmentDiff {
        added: vec![],
        removed: vec![],
        modified: vec![],
    };
    let result = MergeResult::merge(&empty, &empty);
    assert!(result.is_clean());
    assert!(result.from_a.is_empty());
    assert!(result.from_b.is_empty());
}

#[test]
fn test_manager_merge_diffs_updates_stats() {
    let mut mgr = ExtSnapshotManager::with_defaults();
    let diff_a = EnvironmentDiff {
        added: vec![Name::from_string("Conflict")],
        removed: vec![],
        modified: vec![],
    };
    let diff_b = EnvironmentDiff {
        added: vec![Name::from_string("Conflict")],
        removed: vec![],
        modified: vec![],
    };
    let result = mgr.merge_diffs(&diff_a, &diff_b);
    assert_eq!(result.conflicts.len(), 1);
    assert_eq!(mgr.stats().merges_attempted, 1);
    assert_eq!(mgr.stats().merge_conflicts, 1);
}

// ---- Declaration fingerprinting ---------------------------------------------

#[test]
fn test_fingerprint_deterministic() {
    let mut env = test_env();
    add_axiom(&mut env, "FP");
    let info = env.get_const(&Name::from_string("FP")).unwrap();
    let fp1 = DeclFingerprint::from_constant(info);
    let fp2 = DeclFingerprint::from_constant(info);
    assert_eq!(fp1, fp2);
    assert_eq!(fp1.value(), fp2.value());
}

#[test]
fn test_fingerprint_differs_for_different_decls() {
    let mut env = test_env();
    add_axiom(&mut env, "Alpha");
    add_axiom(&mut env, "Beta");
    let fp_a = DeclFingerprint::from_constant(env.get_const(&Name::from_string("Alpha")).unwrap());
    let fp_b = DeclFingerprint::from_constant(env.get_const(&Name::from_string("Beta")).unwrap());
    // Different names should produce different fingerprints (with very high probability).
    assert_ne!(fp_a, fp_b);
}

// ---- Snapshot compression ---------------------------------------------------

#[test]
fn test_compressed_snapshot_basic() {
    let mut env = test_env();
    add_axiom(&mut env, "C1");
    add_axiom(&mut env, "C2");
    let cp = Checkpoint::take(&env, "comp", true);
    let compressed = CompressedSnapshot::from_checkpoint(&cp);
    assert_eq!(compressed.label, "comp");
    assert_eq!(compressed.decl_count, cp.decl_count());
    assert!(compressed.contains_name(&Name::from_string("C1")));
    assert!(compressed.contains_name(&Name::from_string("C2")));
    assert!(!compressed.contains_name(&Name::from_string("C3")));
}

#[test]
fn test_compressed_snapshot_sorted_names() {
    let mut env = test_env();
    add_axiom(&mut env, "Z");
    add_axiom(&mut env, "A");
    add_axiom(&mut env, "M");
    let cp = Checkpoint::take(&env, "sort_test", true);
    let compressed = CompressedSnapshot::from_checkpoint(&cp);
    // Verify sorted order for the names we added (env may have others).
    let our_names: Vec<&Name> = compressed
        .sorted_names
        .iter()
        .filter(|n| {
            let s = format!("{n}");
            s == "A" || s == "M" || s == "Z"
        })
        .collect();
    assert!(our_names.len() >= 3);
    for w in our_names.windows(2) {
        assert!(w[0] <= w[1]);
    }
}

#[test]
fn test_compressed_empty_checkpoint() {
    let env = test_env();
    let cp = Checkpoint::take(&env, "empty_comp", true);
    let compressed = CompressedSnapshot::from_checkpoint(&cp);
    assert_eq!(compressed.decl_count, cp.decl_count());
}

// ---- Serialization round-trip -----------------------------------------------

#[test]
fn test_serialization_round_trip() {
    let mut env = test_env();
    add_axiom(&mut env, "Ser1");
    add_axiom(&mut env, "Ser2");
    let cp = Checkpoint::take(&env, "serial", true);
    let serialized = SerializedSnapshot::from_checkpoint(&cp);
    let restored = serialized.to_checkpoint();
    assert_eq!(restored.label(), "serial");
    assert_eq!(restored.decl_count(), cp.decl_count());
    assert!(restored.decl_names().contains(&Name::from_string("Ser1")));
    assert!(restored.decl_names().contains(&Name::from_string("Ser2")));
}

#[test]
fn test_serialization_preserves_fingerprints() {
    let mut env = test_env();
    add_axiom(&mut env, "FPSer");
    let cp = Checkpoint::take(&env, "fp_serial", true);
    let serialized = SerializedSnapshot::from_checkpoint(&cp);
    assert!(!serialized.fingerprints.is_empty());
    assert_eq!(serialized.decl_count, cp.decl_count());
}

#[test]
fn test_serialization_equality() {
    let mut env = test_env();
    add_axiom(&mut env, "EqTest");
    let cp = Checkpoint::take(&env, "eq", true);
    let s1 = SerializedSnapshot::from_checkpoint(&cp);
    let s2 = SerializedSnapshot::from_checkpoint(&cp);
    assert_eq!(s1, s2);
}

#[test]
fn test_serialization_empty_env() {
    let env = test_env();
    let cp = Checkpoint::take(&env, "empty_ser", true);
    let serialized = SerializedSnapshot::from_checkpoint(&cp);
    let restored = serialized.to_checkpoint();
    assert_eq!(restored.decl_count(), cp.decl_count());
    assert_eq!(restored.label(), "empty_ser");
}

// ---- Rollback ---------------------------------------------------------------

#[test]
fn test_rollback_restores_environment() {
    let mut env = test_env();
    let backup = env.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "before");
    let count_before = env.num_constants();
    add_axiom(&mut env, "Added");
    assert!(env.num_constants() > count_before);
    let success = mgr.rollback("before", &mut env, &backup);
    assert!(success);
    assert_eq!(env.num_constants(), count_before);
}

#[test]
fn test_rollback_nonexistent_returns_false() {
    let mut env = test_env();
    let backup = env.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    assert!(!mgr.rollback("nope", &mut env, &backup));
}

#[test]
fn test_rollback_updates_stats() {
    let mut env = test_env();
    let backup = env.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "rb");
    mgr.rollback("rb", &mut env, &backup);
    assert_eq!(mgr.stats().rollbacks_performed, 1);
}

// ---- Change callbacks -------------------------------------------------------

#[test]
fn test_change_callback_invoked() {
    let counter = Arc::new(AtomicUsize::new(0));
    let counter_clone = counter.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.on_change(Box::new(move |diff| {
        counter_clone.fetch_add(diff.total_changes(), Ordering::SeqCst);
    }));
    let diff = EnvironmentDiff {
        added: vec![Name::from_string("CB1"), Name::from_string("CB2")],
        removed: vec![],
        modified: vec![],
    };
    mgr.notify_change(&diff);
    assert_eq!(counter.load(Ordering::SeqCst), 2);
}

#[test]
fn test_multiple_callbacks() {
    let c1 = Arc::new(AtomicUsize::new(0));
    let c2 = Arc::new(AtomicUsize::new(0));
    let c1c = c1.clone();
    let c2c = c2.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.on_change(Box::new(move |_| {
        c1c.fetch_add(1, Ordering::SeqCst);
    }));
    mgr.on_change(Box::new(move |_| {
        c2c.fetch_add(1, Ordering::SeqCst);
    }));
    let diff = EnvironmentDiff {
        added: vec![],
        removed: vec![],
        modified: vec![],
    };
    mgr.notify_change(&diff);
    assert_eq!(c1.load(Ordering::SeqCst), 1);
    assert_eq!(c2.load(Ordering::SeqCst), 1);
}

#[test]
fn test_callback_receives_correct_diff() {
    let added_count = Arc::new(AtomicUsize::new(0));
    let ac = added_count.clone();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.on_change(Box::new(move |diff| {
        ac.store(diff.added.len(), Ordering::SeqCst);
    }));
    let diff = EnvironmentDiff {
        added: vec![
            Name::from_string("X"),
            Name::from_string("Y"),
            Name::from_string("Z"),
        ],
        removed: vec![],
        modified: vec![],
    };
    mgr.notify_change(&diff);
    assert_eq!(added_count.load(Ordering::SeqCst), 3);
}

// ---- Statistics tracking ----------------------------------------------------

#[test]
fn test_stats_initial() {
    let mgr = ExtSnapshotManager::with_defaults();
    let s = mgr.stats();
    assert_eq!(s.checkpoints_created, 0);
    assert_eq!(s.rollbacks_performed, 0);
    assert_eq!(s.diffs_computed, 0);
    assert_eq!(s.merges_attempted, 0);
    assert_eq!(s.merge_conflicts, 0);
    assert_eq!(s.current_checkpoint_count, 0);
}

#[test]
fn test_stats_checkpoint_count() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "s1");
    mgr.save_checkpoint(&env, "s2");
    assert_eq!(mgr.stats().checkpoints_created, 2);
    assert_eq!(mgr.stats().current_checkpoint_count, 2);
}

#[test]
fn test_stats_diff_count() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "d");
    mgr.diff_from_checkpoint("d", &env);
    mgr.diff_from_checkpoint("d", &env);
    assert_eq!(mgr.stats().diffs_computed, 2);
}

#[test]
fn test_stats_disabled() {
    let env = test_env();
    let config = ExtSnapshotConfig {
        max_checkpoints: 64,
        auto_fingerprint: true,
        track_stats: false,
    };
    let mut mgr = ExtSnapshotManager::new(config);
    mgr.save_checkpoint(&env, "x");
    assert_eq!(mgr.stats().checkpoints_created, 0);
}

// ---- Edge cases -------------------------------------------------------------

#[test]
fn test_remove_checkpoint() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "rm");
    assert!(mgr.remove_checkpoint("rm"));
    assert_eq!(mgr.checkpoint_count(), 0);
    assert!(!mgr.remove_checkpoint("rm"));
}

#[test]
fn test_clear_checkpoints() {
    let env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    mgr.save_checkpoint(&env, "a");
    mgr.save_checkpoint(&env, "b");
    mgr.clear_checkpoints();
    assert_eq!(mgr.checkpoint_count(), 0);
    assert!(mgr.checkpoint_labels().is_empty());
}

#[test]
fn test_many_checkpoints() {
    let env = test_env();
    let config = ExtSnapshotConfig {
        max_checkpoints: 5,
        auto_fingerprint: false,
        track_stats: true,
    };
    let mut mgr = ExtSnapshotManager::new(config);
    for i in 0..10 {
        mgr.save_checkpoint(&env, &format!("cp{i}"));
    }
    assert_eq!(mgr.checkpoint_count(), 5);
    // Oldest 5 should be gone.
    assert!(mgr.get_checkpoint("cp0").is_none());
    assert!(mgr.get_checkpoint("cp4").is_none());
    assert!(mgr.get_checkpoint("cp5").is_some());
    assert!(mgr.get_checkpoint("cp9").is_some());
}

#[test]
fn test_manager_debug_impl() {
    let mgr = ExtSnapshotManager::with_defaults();
    let debug_str = format!("{mgr:?}");
    assert!(debug_str.contains("ExtSnapshotManager"));
    assert!(debug_str.contains("checkpoints"));
}

#[test]
fn test_single_decl_checkpoint_and_diff() {
    let mut env = test_env();
    let mut mgr = ExtSnapshotManager::with_defaults();
    add_axiom(&mut env, "Solo");
    mgr.save_checkpoint(&env, "with_solo");
    // No changes since checkpoint.
    let diff = mgr.diff_from_checkpoint("with_solo", &env).unwrap();
    assert!(diff.is_empty());
}
