// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Task parallelism for the clean runtime — thread-pool based task scheduler
//! matching Lean 4's `Task` monad. Part of #3099.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};

use crate::object_model::{lean_box, LeanObjPtr};
use crate::runtime::closure::closure_apply;
use crate::runtime::{clean_task_get_imp, clean_task_get_value, lean_dec, lean_inc};

/// Wrapper to send `LeanObjPtr` across thread boundaries.
/// # Safety
/// The wrapped pointer must be a valid Lean object with correct ref count,
/// or a tagged scalar. Task synchronization prevents concurrent access.
struct SendPtr(LeanObjPtr);
unsafe impl Send for SendPtr {}

/// # Safety: Caller must ensure all captured raw pointers are valid Lean objects
/// with correct ref counts, and that synchronization prevents data races.
unsafe fn spawn_send(name: &str, f: impl FnOnce() + 'static) {
    let boxed: Box<dyn FnOnce()> = Box::new(f);
    // SAFETY: caller guarantees all captured pointers are valid and synchronized
    let send_box: Box<dyn FnOnce() + Send> = unsafe { std::mem::transmute(boxed) };
    std::thread::Builder::new()
        .name(name.to_string())
        .spawn(send_box)
        .expect("invariant: failed to spawn thread");
}

/// Task lifecycle states. Transitions: Pending -> Running -> Completed|Failed.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TaskState {
    Pending = 0,
    Running = 1,
    Completed = 2,
    Failed = 3,
}

impl TaskState {
    fn from_u8(v: u8) -> Self {
        match v {
            0 => Self::Pending,
            1 => Self::Running,
            2 => Self::Completed,
            3 => Self::Failed,
            _ => Self::Failed,
        }
    }
}

/// Shared state backing a single spawned task. Reference-counted via `Arc`.
pub(crate) struct TaskInner {
    state: AtomicU8,
    thunk: Mutex<LeanObjPtr>,
    result: Mutex<Option<LeanObjPtr>>,
    done: Condvar,
}

// SAFETY: LeanObjPtr is *mut CleanObj which is !Send by default. The runtime
// guarantees task thunks/results are scalars (tagged pointers) or heap objects
// with correct ref counts. Mutex+Condvar prevents concurrent mutation.
unsafe impl Send for TaskInner {}
unsafe impl Sync for TaskInner {}

impl TaskInner {
    fn new(thunk: LeanObjPtr) -> Self {
        Self {
            state: AtomicU8::new(TaskState::Pending as u8),
            thunk: Mutex::new(thunk),
            result: Mutex::new(None),
            done: Condvar::new(),
        }
    }

    fn state(&self) -> TaskState {
        TaskState::from_u8(self.state.load(Ordering::Acquire))
    }

    /// Execute the thunk and store the result. Called by worker threads.
    fn execute(&self) {
        self.state
            .store(TaskState::Running as u8, Ordering::Release);

        let thunk = {
            let mut guard = self.thunk.lock().expect("invariant: thunk lock");
            let t = *guard;
            *guard = std::ptr::null_mut();
            t
        };

        if thunk.is_null() {
            self.state.store(TaskState::Failed as u8, Ordering::Release);
            self.done.notify_all();
            return;
        }

        // Pass lean_box(0) (Lean Unit/⟨⟩) as the thunk argument, matching
        // Lean 4's lean_task_spawn_core which calls lean_apply_1(c, lean_box(0)).
        let unit = lean_box(0);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            closure_apply(thunk, &[unit])
        }));
        lean_dec(thunk);

        match result {
            Ok(value) => {
                *self.result.lock().expect("invariant: result lock") = Some(value);
                self.state
                    .store(TaskState::Completed as u8, Ordering::Release);
            }
            Err(_) => {
                self.state.store(TaskState::Failed as u8, Ordering::Release);
            }
        }
        self.done.notify_all();
    }

    /// Block until the task completes. Returns null on failure.
    fn join(&self) -> LeanObjPtr {
        let guard = self.result.lock().expect("invariant: result lock");
        let guard = self
            .done
            .wait_while(guard, |r| r.is_none() && self.state() != TaskState::Failed)
            .expect("invariant: condvar wait");

        match *guard {
            Some(ptr) => {
                lean_inc(ptr);
                ptr
            }
            None => std::ptr::null_mut(),
        }
    }
}

/// A handle to a spawned task. Cloneable (reference counted).
#[derive(Clone)]
pub struct TaskHandle {
    inner: Arc<TaskInner>,
}

// SAFETY: TaskInner is Send+Sync (unsafe impl above), Arc<TaskInner> is
// therefore safe to share. TaskHandle is just an Arc wrapper.
unsafe impl Send for TaskHandle {}
unsafe impl Sync for TaskHandle {}

impl TaskHandle {
    /// Block until the task completes and return its result.
    /// The returned `LeanObjPtr` has an incremented ref count.
    #[must_use]
    pub fn join(&self) -> LeanObjPtr {
        self.inner.join()
    }

    /// Check whether the task has completed (successfully or with failure).
    #[must_use]
    pub fn is_done(&self) -> bool {
        matches!(self.inner.state(), TaskState::Completed | TaskState::Failed)
    }

    /// Convert into a raw `Arc` pointer for storage in `TaskObj.imp`.
    pub(crate) fn into_raw(self) -> *mut () {
        Arc::into_raw(self.inner) as *mut ()
    }

    /// Reconstruct from a raw pointer from [`into_raw`](Self::into_raw).
    ///
    /// # Safety
    /// `ptr` must be a valid pointer from `TaskHandle::into_raw`, not yet reclaimed.
    #[cfg(test)]
    pub(crate) unsafe fn from_raw(ptr: *mut ()) -> Self {
        // SAFETY: Caller guarantees `ptr` from Arc::into_raw, not double-freed.
        Self {
            inner: unsafe { Arc::from_raw(ptr as *const TaskInner) },
        }
    }

    /// Clone the handle from a raw pointer without consuming it.
    ///
    /// # Safety
    /// `ptr` must be a live `Arc<TaskInner>` raw pointer.
    pub(crate) unsafe fn clone_from_raw(ptr: *mut ()) -> Self {
        // SAFETY: Caller guarantees valid Arc raw pointer.
        unsafe {
            let arc = Arc::from_raw(ptr as *const TaskInner);
            let cloned = arc.clone();
            let _ = Arc::into_raw(arc); // restore original ref count
            Self { inner: cloned }
        }
    }
}

/// Thread-pool task scheduler. Workers pull from a shared FIFO queue.
pub struct TaskScheduler {
    queue: Arc<Mutex<VecDeque<Arc<TaskInner>>>>,
    notify: Arc<Condvar>,
    shutdown: Arc<Mutex<bool>>,
    workers: Vec<std::thread::JoinHandle<()>>,
}

fn default_num_workers() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
}

impl TaskScheduler {
    /// Create a new scheduler with `num_workers` threads.
    pub fn new(num_workers: usize) -> Self {
        let queue = Arc::new(Mutex::new(VecDeque::<Arc<TaskInner>>::new()));
        let notify = Arc::new(Condvar::new());
        let shutdown = Arc::new(Mutex::new(false));

        let mut workers = Vec::with_capacity(num_workers);
        for i in 0..num_workers {
            let q = Arc::clone(&queue);
            let n = Arc::clone(&notify);
            let s = Arc::clone(&shutdown);
            let handle = std::thread::Builder::new()
                .name(format!("clean-task-{i}"))
                .spawn(move || worker_loop(&q, &n, &s))
                .expect("invariant: failed to spawn worker thread");
            workers.push(handle);
        }
        Self {
            queue,
            notify,
            shutdown,
            workers,
        }
    }

    /// Submit a task for execution. Returns a handle for joining.
    pub fn spawn(&self, thunk: LeanObjPtr) -> TaskHandle {
        let inner = Arc::new(TaskInner::new(thunk));
        {
            let mut q = self.queue.lock().expect("invariant: queue lock");
            q.push_back(Arc::clone(&inner));
        }
        self.notify.notify_one();
        TaskHandle { inner }
    }

    /// Shut down the scheduler, waiting for all workers to finish.
    pub fn shutdown(self) {
        {
            let mut flag = self.shutdown.lock().expect("invariant: shutdown lock");
            *flag = true;
        }
        self.notify.notify_all();
        for w in self.workers {
            let _ = w.join();
        }
    }
}

fn worker_loop(queue: &Mutex<VecDeque<Arc<TaskInner>>>, notify: &Condvar, shutdown: &Mutex<bool>) {
    loop {
        let task = {
            let mut q = queue.lock().expect("invariant: queue lock");
            loop {
                if let Some(t) = q.pop_front() {
                    break Some(t);
                }
                if *shutdown.lock().expect("invariant: shutdown lock") {
                    break None;
                }
                q = notify.wait(q).expect("invariant: condvar wait");
            }
        };
        match task {
            Some(inner) => inner.execute(),
            None => return,
        }
    }
}

// Global scheduler singleton

static GLOBAL_SCHEDULER: OnceLock<TaskScheduler> = OnceLock::new();

/// Initialize the global task scheduler. Idempotent.
pub fn init_task_scheduler() {
    GLOBAL_SCHEDULER.get_or_init(|| TaskScheduler::new(default_num_workers()));
}

fn global_scheduler() -> &'static TaskScheduler {
    GLOBAL_SCHEDULER.get_or_init(|| TaskScheduler::new(default_num_workers()))
}

// Public API

/// Spawn a task executing `thunk` (a fully-applied closure). Ownership
/// of `thunk` is transferred; caller must `clean_inc` to retain a reference.
#[must_use]
pub fn spawn_task(thunk: LeanObjPtr) -> TaskHandle {
    global_scheduler().spawn(thunk)
}

/// Block until the task completes. Returns result with incremented ref count.
#[must_use]
pub fn join_task(handle: &TaskHandle) -> LeanObjPtr {
    handle.join()
}

/// Create an already-completed task holding `val` (Lean 4 `Task.pure`).
#[must_use]
pub fn task_pure(val: LeanObjPtr) -> TaskHandle {
    lean_inc(val);
    let inner = Arc::new(TaskInner {
        state: AtomicU8::new(TaskState::Completed as u8),
        thunk: Mutex::new(std::ptr::null_mut()),
        result: Mutex::new(Some(val)),
        done: Condvar::new(),
    });
    TaskHandle { inner }
}

/// Monadic bind: when `task` completes, apply `f` to its result.
/// `f` must be a Lean closure expecting one argument. Ref count of `f`
/// is incremented (bind holds its own reference).
#[must_use]
pub fn task_bind(task: &TaskHandle, f: LeanObjPtr) -> TaskHandle {
    lean_inc(f);
    let f_send = SendPtr(f);
    let source = task.clone();
    let inner = Arc::new(TaskInner {
        state: AtomicU8::new(TaskState::Pending as u8),
        thunk: Mutex::new(std::ptr::null_mut()),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    // SAFETY: f_send wraps a valid Lean closure with incremented ref count,
    // source is a TaskHandle with Arc-based synchronization, inner is Arc<TaskInner>.
    unsafe {
        spawn_send("clean-task-bind", move || {
            let f = f_send.0;
            let source_result = source.join();
            inner
                .state
                .store(TaskState::Running as u8, Ordering::Release);

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                closure_apply(f, &[source_result])
            }));
            lean_dec(f);

            match result {
                Ok(value) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(value);
                    inner
                        .state
                        .store(TaskState::Completed as u8, Ordering::Release);
                }
                Err(_) => {
                    inner
                        .state
                        .store(TaskState::Failed as u8, Ordering::Release);
                }
            }
            inner.done.notify_all();
        });
    }

    TaskHandle { inner: inner_clone }
}

/// Functor map: when `task` completes, apply the closure `f` to its result
/// and wrap the output in a completed task. Unlike `task_bind`, `f` returns
/// a plain value, not a new `TaskHandle`.
///
/// `f` must be a Lean closure expecting one argument. Its ref count is
/// incremented (map holds its own reference).
#[must_use]
pub fn task_map(task: &TaskHandle, f: LeanObjPtr) -> TaskHandle {
    lean_inc(f);
    let f_send = SendPtr(f);
    let source = task.clone();
    let inner = Arc::new(TaskInner {
        state: AtomicU8::new(TaskState::Pending as u8),
        thunk: Mutex::new(std::ptr::null_mut()),
        result: Mutex::new(None),
        done: Condvar::new(),
    });
    let inner_clone = Arc::clone(&inner);

    // SAFETY: f_send wraps a valid Lean closure with incremented ref count,
    // source is a TaskHandle with Arc-based synchronization.
    unsafe {
        spawn_send("clean-task-map", move || {
            let f = f_send.0;
            let source_result = source.join();
            inner
                .state
                .store(TaskState::Running as u8, Ordering::Release);

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                closure_apply(f, &[source_result])
            }));
            lean_dec(f);

            match result {
                Ok(value) => {
                    *inner.result.lock().expect("invariant: result lock") = Some(value);
                    inner
                        .state
                        .store(TaskState::Completed as u8, Ordering::Release);
                }
                Err(_) => {
                    inner
                        .state
                        .store(TaskState::Failed as u8, Ordering::Release);
                }
            }
            inner.done.notify_all();
        });
    }

    TaskHandle { inner: inner_clone }
}

// Runtime object bridge

/// Allocate a `TaskObj` backed by a `TaskHandle`.
///
/// # Safety
/// Caller must manage the `TaskObj` lifetime via reference counting.
pub unsafe fn clean_task_from_handle(handle: TaskHandle) -> LeanObjPtr {
    let imp = handle.into_raw();
    // SAFETY: imp is a valid pointer from Arc::into_raw.
    unsafe { crate::clean_alloc_task(imp) }
}

/// Join a `TaskObj`, blocking until completion.
///
/// # Safety
/// `task_obj` must be a valid Task from `clean_task_from_handle`.
pub unsafe fn clean_task_join(task_obj: LeanObjPtr) -> LeanObjPtr {
    // SAFETY: Caller guarantees task_obj is a valid Task.
    let imp = unsafe { clean_task_get_imp(task_obj) };
    if imp.is_null() {
        return unsafe { clean_task_get_value(task_obj) };
    }
    // SAFETY: imp from clean_task_from_handle via Arc::into_raw.
    let handle = unsafe { TaskHandle::clone_from_raw(imp) };
    handle.join()
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_concurrent;
