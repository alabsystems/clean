// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Task IO actions: TaskSpawn, TaskGet, TaskBind, TaskMap,
//! TaskPure, and AsTask.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};

use super::task_io::IoTaskHandle;
use super::{io_bind, IoAction, IoRuntime, IoValue};

// ---------------------------------------------------------------------------
// TaskPure
// ---------------------------------------------------------------------------

#[test]
fn test_task_pure_returns_completed_handle() {
    let rt = IoRuntime::new();
    let result = rt
        .execute(IoAction::TaskPure(IoValue::Nat(42)))
        .expect("TaskPure should succeed");
    match result {
        IoValue::Task(h) => {
            assert!(h.is_done());
            let inner = h.join().expect("pure task join should succeed");
            assert_eq!(inner, IoValue::Nat(42));
        }
        other => panic!("expected Task, got {other:?}"),
    }
}

#[test]
fn test_task_pure_string_value() {
    let rt = IoRuntime::new();
    let result = rt
        .execute(IoAction::TaskPure(IoValue::String("hello".to_string())))
        .expect("TaskPure should succeed");
    match result {
        IoValue::Task(h) => {
            let inner = h.join().expect("join should succeed");
            assert_eq!(inner, IoValue::String("hello".to_string()));
        }
        other => panic!("expected Task, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// TaskSpawn + TaskGet
// ---------------------------------------------------------------------------

#[test]
fn test_task_spawn_and_get_basic() {
    let rt = IoRuntime::new();

    // Spawn a task that returns Nat(100)
    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(100))))
        .expect("TaskSpawn should succeed");

    let handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Get the result
    let get_result = rt
        .execute(IoAction::TaskGet(handle))
        .expect("TaskGet should succeed");
    assert_eq!(get_result, IoValue::Nat(100));
}

#[test]
fn test_task_spawn_string_computation() {
    let rt = IoRuntime::new();
    let result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| {
            IoValue::String(format!("computed: {}", 2 + 3))
        })))
        .expect("TaskSpawn should succeed");

    let handle = match result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let val = rt
        .execute(IoAction::TaskGet(handle))
        .expect("TaskGet should succeed");
    assert_eq!(val, IoValue::String("computed: 5".to_string()));
}

#[test]
fn test_task_spawn_multiple_concurrent() {
    let rt = IoRuntime::new();

    let handles: Vec<IoTaskHandle> = (0..8)
        .map(|i| {
            let result = rt
                .execute(IoAction::TaskSpawn(Box::new(move || IoValue::Nat(i))))
                .expect("TaskSpawn should succeed");
            match result {
                IoValue::Task(h) => h,
                other => panic!("expected Task, got {other:?}"),
            }
        })
        .collect();

    for (i, h) in handles.into_iter().enumerate() {
        let val = rt
            .execute(IoAction::TaskGet(h))
            .expect("TaskGet should succeed");
        assert_eq!(val, IoValue::Nat(i as u64));
    }
}

// ---------------------------------------------------------------------------
// True parallelism via barrier
// ---------------------------------------------------------------------------

#[test]
fn test_task_spawn_runs_concurrently() {
    let rt = IoRuntime::new();
    let n = 4;
    let barrier = Arc::new(Barrier::new(n));
    let counter = Arc::new(AtomicUsize::new(0));

    let handles: Vec<IoTaskHandle> = (0..n)
        .map(|_| {
            let b = Arc::clone(&barrier);
            let c = Arc::clone(&counter);
            let result = rt
                .execute(IoAction::TaskSpawn(Box::new(move || {
                    b.wait(); // All tasks must reach here before any proceeds
                    c.fetch_add(1, Ordering::SeqCst);
                    IoValue::Unit
                })))
                .expect("TaskSpawn should succeed");
            match result {
                IoValue::Task(h) => h,
                other => panic!("expected Task, got {other:?}"),
            }
        })
        .collect();

    // Wait for all to complete
    for h in &handles {
        let _ = rt.execute(IoAction::TaskGet(h.clone()));
    }

    assert_eq!(counter.load(Ordering::SeqCst), n);
}

// ---------------------------------------------------------------------------
// TaskBind
// ---------------------------------------------------------------------------

#[test]
fn test_task_bind_chains_computation() {
    let rt = IoRuntime::new();

    // Spawn task returning Nat(10)
    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(10))))
        .expect("TaskSpawn should succeed");
    let handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Bind: take the Nat, double it
    let bind_result = rt
        .execute(IoAction::TaskBind(
            handle,
            Box::new(|val| match val {
                IoValue::Nat(n) => IoValue::Nat(n * 2),
                other => panic!("expected Nat, got {other:?}"),
            }),
        ))
        .expect("TaskBind should succeed");

    let bound_handle = match bind_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let final_val = rt
        .execute(IoAction::TaskGet(bound_handle))
        .expect("TaskGet should succeed");
    assert_eq!(final_val, IoValue::Nat(20));
}

#[test]
fn test_task_bind_chain_multiple() {
    let rt = IoRuntime::new();

    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(1))))
        .expect("spawn");
    let mut handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Chain 5 binds: each adds 1
    for _ in 0..5 {
        let bind_result = rt
            .execute(IoAction::TaskBind(
                handle,
                Box::new(|val| match val {
                    IoValue::Nat(n) => IoValue::Nat(n + 1),
                    other => panic!("expected Nat, got {other:?}"),
                }),
            ))
            .expect("bind");
        handle = match bind_result {
            IoValue::Task(h) => h,
            other => panic!("expected Task, got {other:?}"),
        };
    }

    let final_val = rt.execute(IoAction::TaskGet(handle)).expect("get");
    assert_eq!(final_val, IoValue::Nat(6));
}

// ---------------------------------------------------------------------------
// TaskMap
// ---------------------------------------------------------------------------

#[test]
fn test_task_map_transforms_result() {
    let rt = IoRuntime::new();

    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(5))))
        .expect("spawn");
    let handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let map_result = rt
        .execute(IoAction::TaskMap(
            handle,
            Box::new(|val| match val {
                IoValue::Nat(n) => IoValue::String(format!("value={n}")),
                other => panic!("expected Nat, got {other:?}"),
            }),
        ))
        .expect("map");

    let mapped_handle = match map_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let final_val = rt.execute(IoAction::TaskGet(mapped_handle)).expect("get");
    assert_eq!(final_val, IoValue::String("value=5".to_string()));
}

#[test]
fn test_task_map_chain() {
    let rt = IoRuntime::new();

    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(1))))
        .expect("spawn");
    let mut handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Chain 3 maps: each multiplies by 2
    for _ in 0..3 {
        let map_result = rt
            .execute(IoAction::TaskMap(
                handle,
                Box::new(|val| match val {
                    IoValue::Nat(n) => IoValue::Nat(n * 2),
                    other => panic!("expected Nat, got {other:?}"),
                }),
            ))
            .expect("map");
        handle = match map_result {
            IoValue::Task(h) => h,
            other => panic!("expected Task, got {other:?}"),
        };
    }

    let final_val = rt.execute(IoAction::TaskGet(handle)).expect("get");
    assert_eq!(final_val, IoValue::Nat(8)); // 1 * 2 * 2 * 2
}

// ---------------------------------------------------------------------------
// AsTask
// ---------------------------------------------------------------------------

#[test]
fn test_as_task_pure_action() {
    let rt = IoRuntime::new();

    let result = rt
        .execute(IoAction::AsTask(Box::new(IoAction::Pure(IoValue::Nat(77)))))
        .expect("AsTask should succeed");

    let handle = match result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let val = rt
        .execute(IoAction::TaskGet(handle))
        .expect("get should succeed");
    assert_eq!(val, IoValue::Nat(77));
}

#[test]
fn test_as_task_println_action() {
    let rt = IoRuntime::new();

    // AsTask wraps a PrintLn; the child runtime captures the output
    // but the parent does not see it (separate IoRuntime on the thread).
    let result = rt
        .execute(IoAction::AsTask(Box::new(IoAction::PrintLn(
            "hello from task".to_string(),
        ))))
        .expect("AsTask should succeed");

    let handle = match result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let val = rt
        .execute(IoAction::TaskGet(handle))
        .expect("get should succeed");
    assert_eq!(val, IoValue::Unit);
    // The parent runtime's stdout should be empty (PrintLn ran on child).
    assert!(rt.stdout_output().is_empty());
}

// ---------------------------------------------------------------------------
// Error propagation
// ---------------------------------------------------------------------------

#[test]
fn test_task_get_on_failed_task_returns_error() {
    let rt = IoRuntime::new();

    // AsTask wraps a Panic action
    let result = rt
        .execute(IoAction::AsTask(Box::new(IoAction::Panic(
            "boom".to_string(),
        ))))
        .expect("AsTask should succeed (returns handle, not error)");

    let handle = match result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // TaskGet should return the error
    let err = rt.execute(IoAction::TaskGet(handle));
    assert!(err.is_err());
    let err_msg = err.unwrap_err().to_string();
    assert!(
        err_msg.contains("panic") || err_msg.contains("boom"),
        "error should mention the panic: {err_msg}"
    );
}

#[test]
fn test_task_bind_propagates_source_failure() {
    let rt = IoRuntime::new();

    let spawn_result = rt
        .execute(IoAction::AsTask(Box::new(IoAction::Panic(
            "source fail".to_string(),
        ))))
        .expect("AsTask should succeed");
    let handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Bind should propagate the source task failure
    let bind_result = rt
        .execute(IoAction::TaskBind(
            handle,
            Box::new(|val| {
                // This should never be called
                panic!("continuation should not run on failed source: {val:?}");
            }),
        ))
        .expect("TaskBind returns a handle even if source will fail");

    let bound_handle = match bind_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    let err = rt.execute(IoAction::TaskGet(bound_handle));
    assert!(err.is_err());
}

// ---------------------------------------------------------------------------
// Integration: Bind chain via io_bind
// ---------------------------------------------------------------------------

#[test]
fn test_task_spawn_get_via_io_bind() {
    let rt = IoRuntime::new();

    // spawn >>= get: the idiomatic IO pattern
    let action = io_bind(
        IoAction::TaskSpawn(Box::new(|| IoValue::Nat(99))),
        |spawn_result| match spawn_result {
            IoValue::Task(h) => IoAction::TaskGet(h),
            other => IoAction::Panic(format!("expected Task, got {other:?}")),
        },
    );

    let val = rt.execute(action).expect("spawn>>get should succeed");
    assert_eq!(val, IoValue::Nat(99));
}

#[test]
fn test_task_spawn_map_get_via_io_bind() {
    let rt = IoRuntime::new();

    // spawn >>= map(+1) >>= get
    let action = io_bind(
        IoAction::TaskSpawn(Box::new(|| IoValue::Nat(10))),
        |spawn_result| {
            let handle = match spawn_result {
                IoValue::Task(h) => h,
                other => return IoAction::Panic(format!("expected Task, got {other:?}")),
            };
            io_bind(
                IoAction::TaskMap(
                    handle,
                    Box::new(|val| match val {
                        IoValue::Nat(n) => IoValue::Nat(n + 1),
                        other => panic!("expected Nat, got {other:?}"),
                    }),
                ),
                |map_result| match map_result {
                    IoValue::Task(h) => IoAction::TaskGet(h),
                    other => IoAction::Panic(format!("expected Task, got {other:?}")),
                },
            )
        },
    );

    let val = rt.execute(action).expect("spawn>>map>>get should succeed");
    assert_eq!(val, IoValue::Nat(11));
}

// ---------------------------------------------------------------------------
// Multiple joiners on same task handle
// ---------------------------------------------------------------------------

#[test]
fn test_task_get_multiple_times() {
    let rt = IoRuntime::new();

    let spawn_result = rt
        .execute(IoAction::TaskSpawn(Box::new(|| IoValue::Nat(55))))
        .expect("spawn");
    let handle = match spawn_result {
        IoValue::Task(h) => h,
        other => panic!("expected Task, got {other:?}"),
    };

    // Get the same handle multiple times
    for _ in 0..5 {
        let val = rt.execute(IoAction::TaskGet(handle.clone())).expect("get");
        assert_eq!(val, IoValue::Nat(55));
    }
}
