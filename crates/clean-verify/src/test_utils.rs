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

/// Build the `EvalIR` subset of the specification (crystal job C3) on a larger
/// stack: foundation types plus the trust-ir executable-semantics stage.
///
/// Used by the EvalIR witness tests and by the vacuity firewall's audit of the
/// EvalIR relations. Much cheaper than the full spec — EvalIR depends on nothing
/// but `Nat`, `Bool` and `Eq`.
#[cfg(any(test, feature = "test-utils"))]
pub fn build_eval_ir_spec_with_stack() -> Specification {
    crate::eval_ir::build_spec_with_stack().expect("EvalIR test spec should build")
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

/// Parse-check a specification declaration WITHOUT elaborating it.
///
/// `add_recursive_def` parses first and elaborates second, so a malformed
/// source dies at parse time — but only once the whole specification is being
/// built, which costs ~27 minutes. Parsing one declaration costs microseconds.
///
/// This exists because two failures in a row were parse errors, not proof
/// errors: a parenthesised `forall` in argument position (which this parser
/// rejects), and a `fun` keyword dropped by a mechanical edit. Neither is
/// visible to `cargo check`, since specification sources are Rust string
/// literals, and neither is visible to a paren-balance check — the second one
/// balances perfectly and simply is not a lambda.
///
/// Use it in a module's unit tests on every source that module generates. Those
/// run in milliseconds and turn the commonest failure class into instant
/// feedback.
pub fn parse_check(source: &str) -> Result<(), String> {
    clean_parser::parse_decl(source)
        .map(|_| ())
        .map_err(|e| format!("{e}"))
}
