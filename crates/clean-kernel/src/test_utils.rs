// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Centralized test utilities for stack size and timeout management.
//!
//! Provides standard stack size constants and helpers for running test closures
//! on threads with custom stack sizes and/or timeouts. Consolidates ad-hoc
//! `thread::Builder` patterns scattered across the workspace. See #2101.

use std::sync::{mpsc, Mutex, MutexGuard, OnceLock};
use std::time::Duration;

/// 4 MB stack — for parser and compatibility tests.
pub const SMALL_STACK: usize = 4 * 1024 * 1024;

/// 8 MB stack — for tests involving moderately deep type structures
/// (e.g., DivisionRing, Field).
pub const MEDIUM_STACK: usize = 8 * 1024 * 1024;

/// 16 MB stack — default for most deep recursion tests
/// (proof elaboration, specification building).
pub const DEFAULT_STACK: usize = 16 * 1024 * 1024;

/// 64 MB stack — for olean import, large inductive types, and
/// builder migration regression tests.
pub const LARGE_STACK: usize = 64 * 1024 * 1024;

/// Default timeout for scaling and long-running tests (30 seconds).
pub const DEFAULT_TEST_TIMEOUT: Duration = Duration::from_secs(30);

static SERIAL_TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

/// Run a closure on a thread with a custom stack size.
///
/// Panics from the closure are propagated to the caller via `resume_unwind`.
///
/// # Example
/// ```text
/// use clean_kernel::test_utils::{run_with_stack, LARGE_STACK};
/// let result = run_with_stack(LARGE_STACK, || 42);
/// assert_eq!(result, 42);
/// ```
pub fn run_with_stack<F, T>(stack_size: usize, f: F) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    let handle = std::thread::Builder::new()
        .stack_size(stack_size)
        .spawn(f)
        .expect("thread spawn should succeed");
    match handle.join() {
        Ok(val) => val,
        Err(e) => std::panic::resume_unwind(e),
    }
}

/// Serialize tests that mutate shared process state or depend on wall-clock timing.
pub fn serial_test_guard() -> MutexGuard<'static, ()> {
    SERIAL_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Run a closure on a thread with a custom stack size and a timeout.
///
/// Combines large-stack spawning with explicit timeout protection.
/// On timeout, panics with a descriptive message including the test name.
/// On closure panic, the panic is propagated to the caller.
///
/// # Example
/// ```text
/// use clean_kernel::test_utils::{run_with_stack_and_timeout, LARGE_STACK, DEFAULT_TEST_TIMEOUT};
/// run_with_stack_and_timeout(LARGE_STACK, DEFAULT_TEST_TIMEOUT, "my_test", || {
///     // ... deep recursion + needs timeout guard ...
/// });
/// ```
pub fn run_with_stack_and_timeout<F>(stack_size: usize, timeout: Duration, test_name: &str, f: F)
where
    F: FnOnce() + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<()>();
    let test_name_owned = test_name.to_string();

    let handle = std::thread::Builder::new()
        .stack_size(stack_size)
        .name(test_name_owned.clone())
        .spawn(move || {
            f();
            tx.send(()).ok();
        })
        .expect("thread spawn should succeed");

    match rx.recv_timeout(timeout) {
        Ok(()) => {
            handle.join().expect("test thread panicked");
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!(
                "TIMEOUT: {} timed out after {}s (see #2101)",
                test_name_owned,
                timeout.as_secs()
            );
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            // Thread panicked before sending — join to propagate
            if let Err(e) = handle.join() {
                std::panic::resume_unwind(e);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_with_stack_returns_value() {
        let result = run_with_stack(SMALL_STACK, || 42);
        assert_eq!(result, 42);
    }

    #[test]
    #[should_panic(expected = "intentional")]
    fn test_run_with_stack_propagates_panic() {
        run_with_stack(SMALL_STACK, || -> i32 { panic!("intentional") });
    }

    #[test]
    fn test_run_with_stack_and_timeout_completes() {
        run_with_stack_and_timeout(SMALL_STACK, Duration::from_secs(5), "fast_test", || {});
    }

    #[test]
    fn test_serial_test_guard_blocks_parallel_callers() {
        let guard = serial_test_guard();
        let (tx, rx) = mpsc::channel();
        let handle = std::thread::spawn(move || {
            let _guard = serial_test_guard();
            tx.send(()).expect("worker should report lock acquisition");
        });

        assert!(
            matches!(
                rx.recv_timeout(Duration::from_millis(50)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ),
            "second caller should block while the first guard is held"
        );

        drop(guard);
        rx.recv_timeout(Duration::from_secs(1))
            .expect("second caller should acquire the guard after release");
        handle
            .join()
            .expect("worker should finish after lock release");
    }

    #[test]
    fn test_serial_test_guard_recovers_after_panic() {
        let handle = std::thread::spawn(|| {
            let _guard = serial_test_guard();
            panic!("intentional serial test panic");
        });
        assert!(
            handle.join().is_err(),
            "worker should panic while holding the guard"
        );

        let _guard = serial_test_guard();
    }

    #[test]
    #[should_panic(expected = "TIMEOUT")]
    fn test_run_with_stack_and_timeout_detects_timeout() {
        run_with_stack_and_timeout(SMALL_STACK, Duration::from_millis(50), "slow_test", || {
            std::thread::sleep(Duration::from_secs(10));
        });
    }
}
