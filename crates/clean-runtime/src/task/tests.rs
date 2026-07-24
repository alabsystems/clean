// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for core task primitives: pure, clone, state transitions,
//! raw handle round-trip, and global scheduler initialization.

use super::*;
use crate::object_model::{is_scalar, lean_box, lean_unbox};

#[test]
fn test_task_pure_returns_value() {
    let val = lean_box(42);
    let handle = task_pure(val);
    assert!(handle.is_done());
    let result = handle.join();
    assert!(is_scalar(result));
    assert_eq!(lean_unbox(result), 42);
}

#[test]
fn test_task_pure_join_twice() {
    let handle = task_pure(lean_box(99));
    assert_eq!(lean_unbox(handle.join()), 99);
    assert_eq!(lean_unbox(handle.join()), 99);
}

#[test]
fn test_task_handle_clone_shares_state() {
    let h1 = task_pure(lean_box(7));
    let h2 = h1.clone();
    assert!(h1.is_done());
    assert!(h2.is_done());
    assert_eq!(lean_unbox(h1.join()), 7);
    assert_eq!(lean_unbox(h2.join()), 7);
}

#[test]
fn test_task_state_transitions() {
    assert_eq!(TaskState::from_u8(0), TaskState::Pending);
    assert_eq!(TaskState::from_u8(1), TaskState::Running);
    assert_eq!(TaskState::from_u8(2), TaskState::Completed);
    assert_eq!(TaskState::from_u8(3), TaskState::Failed);
    assert_eq!(TaskState::from_u8(255), TaskState::Failed);
}

#[test]
fn test_scheduler_creation_and_shutdown() {
    let sched = TaskScheduler::new(2);
    sched.shutdown();
}

#[test]
fn test_task_inner_null_thunk_fails() {
    let inner = TaskInner::new(std::ptr::null_mut());
    inner.execute();
    assert_eq!(inner.state(), TaskState::Failed);
}

#[test]
fn test_handle_raw_round_trip() {
    let handle = task_pure(lean_box(55));
    let raw = handle.into_raw();
    assert!(!raw.is_null());
    let recovered = unsafe { TaskHandle::from_raw(raw) };
    assert!(recovered.is_done());
    assert_eq!(lean_unbox(recovered.join()), 55);
}

#[test]
fn test_handle_clone_from_raw() {
    let handle = task_pure(lean_box(123));
    let raw = handle.into_raw();
    let cloned = unsafe { TaskHandle::clone_from_raw(raw) };
    assert!(cloned.is_done());
    assert_eq!(lean_unbox(cloned.join()), 123);
    let _ = unsafe { TaskHandle::from_raw(raw) }; // cleanup
}

#[test]
fn test_global_scheduler_init_idempotent() {
    init_task_scheduler();
    init_task_scheduler();
    let _ = global_scheduler();
}
