// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helper functions for building type checker test expressions.
//!
//! This module consolidates common expression builders used across multiple test files
//! to reduce code duplication and ensure consistency. See #1047.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use crate::expr::{BinderInfo, Expr};
use crate::Name;

/// Build a deeply nested lambda expression.
///
/// Creates: `λ (x₀ : ty). λ (x₁ : ty). ... λ (xₙ : ty). body`
///
/// # Arguments
/// * `depth` - Number of lambda layers
/// * `ty` - The type annotation for each binder
/// * `body` - The innermost body expression
///
/// # Example
/// ```text
/// // λ (_ : Type). λ (_ : Type). BVar(1) - refers to outer lambda
/// let lam = build_nested_lam(2, &Expr::type_(), Expr::bvar(1));
/// ```
pub fn build_nested_lam(depth: usize, ty: &Expr, body: Expr) -> Expr {
    let mut result = body;
    for _ in 0..depth {
        result = Expr::lam(BinderInfo::Default, ty.clone(), result);
    }
    result
}

/// Build a deeply nested lambda with default type (Type) and body (BVar(0)).
///
/// Creates: `λ (_ : Type). λ (_ : Type). ... λ (_ : Type). BVar(0)`
///
/// The body `BVar(0)` refers to the innermost (last) lambda binder.
/// This is a convenience wrapper around [`build_nested_lam`].
pub fn build_nested_lambda(depth: usize) -> Expr {
    build_nested_lam(depth, &Expr::type_(), Expr::bvar(0))
}

/// Build a deeply nested Pi type.
///
/// Creates: `(x₀ : Type) → (x₁ : Type) → ... → (xₙ : Type) → Type`
pub fn build_nested_pi(depth: usize) -> Expr {
    let mut e = Expr::type_();
    for _ in 0..depth {
        e = Expr::pi(BinderInfo::Default, Expr::type_(), e);
    }
    e
}

/// Build a chain of applications with repeated argument.
///
/// Creates: `(((...((f arg) arg) arg)...) arg)` (n applications)
///
/// # Arguments
/// * `n` - Number of applications
/// * `f` - The function expression
/// * `arg` - The argument to apply repeatedly
pub fn build_app_chain(n: usize, f: Expr, arg: &Expr) -> Expr {
    let mut result = f;
    for _ in 0..n {
        result = Expr::app(result, arg.clone());
    }
    result
}

/// Build nested let expressions with BVar(0) as body.
///
/// Creates: `let _ := Prop in let _ := Prop in ... BVar(0)`
///
/// The body is `BVar(0)` which refers to the innermost let-bound variable.
pub fn build_nested_lets(depth: usize) -> Expr {
    let mut e = Expr::bvar(0);
    for _ in 0..depth {
        e = Expr::let_named(Name::anon(), Expr::type_(), Expr::prop(), e, false);
    }
    e
}

/// Build nested beta redexes.
///
/// Creates: `((λ x. (λ y. (λ z. ... body))) Prop) Prop) ...`
pub fn build_nested_beta_redex(depth: usize) -> Expr {
    // Start with the innermost body: bvar(0)
    let mut body = Expr::bvar(0);

    // Build nested lambdas
    for _ in 0..depth {
        body = Expr::lam(BinderInfo::Default, Expr::type_(), body);
    }

    // Apply arguments from outside to inside
    for _ in 0..depth {
        body = Expr::app(body, Expr::prop());
    }

    body
}

/// Default timeout for scaling tests (30 seconds).
///
/// This is chosen to be long enough for any individual scaling test to complete
/// under normal conditions, but short enough to fail fast rather than hitting
/// the cargo wrapper's 10-minute timeout. See #1045.
pub const SCALING_TEST_TIMEOUT: Duration = Duration::from_secs(30);

/// Run a test closure with an explicit timeout.
///
/// This allows scaling tests to fail fast with a clear error message instead of
/// waiting for the cargo wrapper's 10-minute timeout. The closure runs in a
/// separate thread; if it doesn't complete within the timeout, the test panics.
///
/// # Arguments
/// * `timeout` - Maximum duration to wait for the test
/// * `test_name` - Name of the test (used in timeout panic message)
/// * `f` - The test closure to run
///
/// # Example
/// ```text
/// run_with_timeout(SCALING_TEST_TIMEOUT, "my_scaling_test", || {
///     // ... test code ...
/// });
/// ```
///
/// # Panics
/// - If the closure panics
/// - If the closure doesn't complete within the timeout
/// - If `timeout` is zero (immediate timeout)
pub fn run_with_timeout<F>(timeout: Duration, test_name: &str, f: F)
where
    F: FnOnce() + Send + 'static,
{
    let (tx, rx) = mpsc::channel::<()>();
    let test_name_owned = test_name.to_string();

    let handle = thread::spawn(move || {
        f();
        tx.send(()).ok();
    });

    match rx.recv_timeout(timeout) {
        Ok(()) => {
            handle.join().expect("Test thread panicked");
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Panic instead of process::exit so the test harness can continue.
            // The spawned thread becomes orphaned but the shared test lock
            // prevents concurrent scaling tests, and cargo wrapper's 10-min
            // timeout is the backstop.
            panic!(
                "TIMEOUT: {} timed out after {}s (see #1045, #1652)",
                test_name_owned,
                timeout.as_secs()
            );
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            // Thread panicked before sending, join to propagate the panic
            handle.join().expect("Test thread panicked");
        }
    }
}
