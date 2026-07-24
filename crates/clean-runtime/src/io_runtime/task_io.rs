// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Task parallelism IO actions.
//!
//! Bridges the `IoAction` tree with the thread-pool task scheduler in
//! `crate::task`. This operates at the `IoValue` level (high-level value
//! domain) rather than the `LeanObjPtr` level used by the low-level task
//! runtime.
//!
//! # Lean 4 task API
//!
//! - `Task.spawn : (Unit -> α) -> Task α`
//! - `Task.get : Task α -> α`  (blocks until done)
//! - `Task.bind : Task α -> (α -> Task β) -> Task β`
//! - `Task.map : Task α -> (α -> β) -> Task β`
//! - `Task.pure : α -> Task α`
//! - `BaseIO.asTask : IO α -> Task α`

use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use super::{IoError, IoRuntime, IoValue};

/// Completion states for an `IoValue`-level task.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IoTaskState {
    Pending,
    Completed,
    Failed,
}

/// Shared interior for an `IoValue`-level task.
struct IoTaskInner {
    state: Mutex<IoTaskState>,
    result: Mutex<Option<Result<IoValue, String>>>,
    done: Condvar,
}

/// A handle to a concurrent task producing an `IoValue`.
///
/// This is the `IoValue`-level analog of `crate::task::TaskHandle` (which
/// works with `LeanObjPtr`). Cloneable via `Arc`.
#[derive(Clone)]
pub struct IoTaskHandle {
    inner: Arc<IoTaskInner>,
}

impl std::fmt::Debug for IoTaskHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self
            .inner
            .state
            .lock()
            .map(|s| *s)
            .unwrap_or(IoTaskState::Failed);
        f.debug_struct("IoTaskHandle")
            .field("state", &state)
            .finish()
    }
}

impl PartialEq for IoTaskHandle {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for IoTaskHandle {}

impl IoTaskHandle {
    /// Create an already-completed task holding a value.
    #[must_use]
    pub fn from_value(val: IoValue) -> Self {
        Self {
            inner: Arc::new(IoTaskInner {
                state: Mutex::new(IoTaskState::Completed),
                result: Mutex::new(Some(Ok(val))),
                done: Condvar::new(),
            }),
        }
    }

    /// Block until the task completes and return the result.
    pub(crate) fn join(&self) -> Result<IoValue, String> {
        let guard = self.inner.result.lock().expect("invariant: result lock");
        let guard = self
            .inner
            .done
            .wait_while(guard, |r| r.is_none())
            .expect("invariant: condvar wait");

        match guard.as_ref() {
            Some(Ok(val)) => Ok(val.clone()),
            Some(Err(msg)) => Err(msg.clone()),
            None => Err("task result not available".to_string()),
        }
    }

    /// Check whether the task has finished (successfully or with error).
    #[must_use]
    pub fn is_done(&self) -> bool {
        let state = *self.inner.state.lock().expect("invariant: state lock");
        matches!(state, IoTaskState::Completed | IoTaskState::Failed)
    }
}

/// Spawn a thunk on a new thread, returning a task handle.
///
/// Corresponds to `Task.spawn : (Unit -> α) -> Task α`.
pub(crate) fn exec_task_spawn(
    thunk: Box<dyn FnOnce() -> IoValue + Send>,
) -> Result<IoValue, IoError> {
    let inner = Arc::new(IoTaskInner {
        state: Mutex::new(IoTaskState::Pending),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    thread::Builder::new()
        .name("clean-io-task".to_string())
        .spawn(move || {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(thunk));
            match result {
                Ok(val) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(Ok(val));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Completed;
                }
                Err(panic_payload) => {
                    let msg = if let Some(s) = panic_payload.downcast_ref::<&str>() {
                        (*s).to_string()
                    } else if let Some(s) = panic_payload.downcast_ref::<String>() {
                        s.clone()
                    } else {
                        "task panicked".to_string()
                    };
                    *inner.result.lock().expect("invariant: result lock") = Some(Err(msg));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Failed;
                }
            }
            inner.done.notify_all();
        })
        .map_err(|e| IoError::TaskFailed(format!("failed to spawn task thread: {e}")))?;

    Ok(IoValue::Task(IoTaskHandle { inner: inner_clone }))
}

/// Block until a task completes and return its result.
///
/// Corresponds to `Task.get : Task α -> α`.
pub(crate) fn exec_task_get(handle: &IoTaskHandle) -> Result<IoValue, IoError> {
    handle.join().map_err(IoError::TaskFailed)
}

/// Monadic bind: spawn a thread that waits for `task` to complete, then
/// applies `f` to the result, returning the new value in a fresh task.
///
/// Corresponds to `Task.bind : Task α -> (α -> Task β) -> Task β`.
pub(crate) fn exec_task_bind(
    handle: &IoTaskHandle,
    f: Box<dyn FnOnce(IoValue) -> IoValue + Send>,
) -> Result<IoValue, IoError> {
    let source = handle.clone();
    let inner = Arc::new(IoTaskInner {
        state: Mutex::new(IoTaskState::Pending),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    thread::Builder::new()
        .name("clean-io-task-bind".to_string())
        .spawn(move || {
            let source_result = source.join();
            match source_result {
                Ok(val) => {
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(val)));
                    match result {
                        Ok(new_val) => {
                            *inner.result.lock().expect("invariant: result lock") =
                                Some(Ok(new_val));
                            *inner.state.lock().expect("invariant: state lock") =
                                IoTaskState::Completed;
                        }
                        Err(_) => {
                            *inner.result.lock().expect("invariant: result lock") =
                                Some(Err("task bind continuation panicked".to_string()));
                            *inner.state.lock().expect("invariant: state lock") =
                                IoTaskState::Failed;
                        }
                    }
                }
                Err(msg) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(Err(msg));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Failed;
                }
            }
            inner.done.notify_all();
        })
        .map_err(|e| IoError::TaskFailed(format!("failed to spawn bind thread: {e}")))?;

    Ok(IoValue::Task(IoTaskHandle { inner: inner_clone }))
}

/// Functor map: spawn a thread that waits for `task`, applies `f` to
/// the result, and wraps the output in a new task.
///
/// Corresponds to `Task.map : (α -> β) -> Task α -> Task β`.
pub(crate) fn exec_task_map(
    handle: &IoTaskHandle,
    f: Box<dyn FnOnce(IoValue) -> IoValue + Send>,
) -> Result<IoValue, IoError> {
    let source = handle.clone();
    let inner = Arc::new(IoTaskInner {
        state: Mutex::new(IoTaskState::Pending),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    thread::Builder::new()
        .name("clean-io-task-map".to_string())
        .spawn(move || {
            let source_result = source.join();
            match source_result {
                Ok(val) => {
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(val)));
                    match result {
                        Ok(mapped) => {
                            *inner.result.lock().expect("invariant: result lock") =
                                Some(Ok(mapped));
                            *inner.state.lock().expect("invariant: state lock") =
                                IoTaskState::Completed;
                        }
                        Err(_) => {
                            *inner.result.lock().expect("invariant: result lock") =
                                Some(Err("task map function panicked".to_string()));
                            *inner.state.lock().expect("invariant: state lock") =
                                IoTaskState::Failed;
                        }
                    }
                }
                Err(msg) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(Err(msg));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Failed;
                }
            }
            inner.done.notify_all();
        })
        .map_err(|e| IoError::TaskFailed(format!("failed to spawn map thread: {e}")))?;

    Ok(IoValue::Task(IoTaskHandle { inner: inner_clone }))
}

/// Convert an IO action into a task by executing it on a new thread.
///
/// Corresponds to `BaseIO.asTask : IO α -> Task α`. The action is
/// executed in a fresh `IoRuntime` on the spawned thread.
pub(crate) fn exec_as_task(
    action: super::IoAction,
    _parent_rt: &IoRuntime,
) -> Result<IoValue, IoError> {
    // IoAction is not Send because it contains Box<dyn FnOnce(...)> without
    // Send bound (on Bind/Map/Catch variants). For AsTask we require the
    // action to only be a leaf (Pure, PrintLn, etc.) or use Send-safe closures.
    //
    // We transmute the action to satisfy Send. This is safe when:
    // 1. The action tree does not capture non-Send references from the parent.
    // 2. The spawned thread gets exclusive ownership of the action.
    //
    // In practice, AsTask wraps IO actions built from IoValue (all Send)
    // and boxed closures over IoValue (Send when the closure is Send).

    let inner = Arc::new(IoTaskInner {
        state: Mutex::new(IoTaskState::Pending),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    // SAFETY: We transfer exclusive ownership of `action` to the new thread.
    // The caller must ensure the action tree does not capture thread-local or
    // non-Send state from the parent runtime.
    let action_send: Box<dyn FnOnce() -> Result<IoValue, String> + Send> = unsafe {
        let boxed: Box<dyn FnOnce() -> Result<IoValue, String>> = Box::new(move || {
            let rt = IoRuntime::new();
            rt.execute(action).map_err(|e| e.to_string())
        });
        std::mem::transmute(boxed)
    };

    thread::Builder::new()
        .name("clean-io-as-task".to_string())
        .spawn(move || {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(action_send));
            match result {
                Ok(Ok(val)) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(Ok(val));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Completed;
                }
                Ok(Err(msg)) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(Err(msg));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Failed;
                }
                Err(_) => {
                    *inner.result.lock().expect("invariant: result lock") =
                        Some(Err("asTask action panicked".to_string()));
                    *inner.state.lock().expect("invariant: state lock") = IoTaskState::Failed;
                }
            }
            inner.done.notify_all();
        })
        .map_err(|e| IoError::TaskFailed(format!("failed to spawn asTask thread: {e}")))?;

    Ok(IoValue::Task(IoTaskHandle { inner: inner_clone }))
}
