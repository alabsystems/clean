// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test utilities for clean-verify.
//!
//! This module provides common helpers for tests that need larger stack sizes
//! to handle deep recursion during proof term elaboration.
//! Stack size constants are centralized in `clean_kernel::test_utils` (#2101).

use crate::spec::Specification;

/// Stack size for tests requiring deep recursion (64MB).
///
/// Specification construction + cross-validation elaborates complex proof terms
/// that recurse deeply through the kernel and elaborator. 16MB (DEFAULT_STACK)
/// was insufficient after Wave 0/1 infrastructure additions increased
/// elaboration depth.
pub const TEST_STACK_SIZE: usize = clean_kernel::test_utils::LARGE_STACK;

/// Run a function on a thread with a larger stack.
///
/// Delegates to `clean_kernel::test_utils::run_with_stack` with `DEFAULT_STACK`.
///
/// # Example
/// ```no_run
/// # use clean_verify::test_utils::run_with_stack;
/// let result = run_with_stack(|| 42);
/// assert_eq!(result, 42);
/// ```
pub fn run_with_stack<F, T>(f: F) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    clean_kernel::test_utils::run_with_stack(TEST_STACK_SIZE, f)
}

/// Build a specification on a thread with larger stack.
///
/// Specification building involves deep recursion during proof term elaboration,
/// so it requires a larger stack than the default test thread provides.
pub fn build_spec_with_stack() -> Specification {
    run_with_stack(|| Specification::new().expect("spec should build"))
}

/// Build the implementation-soundness subset of the specification on a larger stack.
///
/// This avoids full-spec construction in focused implementation-soundness tests,
/// which keeps their dependency surface aligned with the modules under test.
#[cfg(any(test, feature = "test-utils"))]
pub fn build_implementation_soundness_spec_with_stack() -> Specification {
    run_with_stack(|| {
        Specification::new_implementation_soundness_test_spec()
            .expect("implementation-soundness test spec should build")
    })
}
