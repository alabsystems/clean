// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests for tc subsystem
//!
//! Covers gaps identified in P1 671 proof_coverage phase:
//! - checked_add_u32 overflow saturation (local_context.rs:16)
//! - set_trace_collector lifecycle (tc/mod.rs:520)
//! - NullCollector tracing_enabled behavior (cert/trace.rs:245)

use super::*;

// =============================================================================
// checked_add_u32 overflow saturation (tc/local_context.rs:16)
// Verifies saturating_add behavior on overflow
// =============================================================================

#[test]
fn test_checked_add_u32_normal() {
    use super::local_context::checked_add_u32;
    assert_eq!(checked_add_u32(10, 20, "test"), 30);
    assert_eq!(checked_add_u32(0, 0, "test"), 0);
    assert_eq!(checked_add_u32(u32::MAX - 1, 1, "test"), u32::MAX);
}

#[test]
fn test_checked_add_u32_overflow_saturates() {
    use super::local_context::checked_add_u32;
    assert_eq!(checked_add_u32(u32::MAX, 1, "test_overflow"), u32::MAX);
}

#[test]
fn test_checked_add_u32_large_overflow_saturates() {
    use super::local_context::checked_add_u32;
    assert_eq!(
        checked_add_u32(u32::MAX / 2 + 1, u32::MAX / 2 + 1, "test_large"),
        u32::MAX,
    );
}

// =============================================================================
// set_trace_collector lifecycle (tc/mod.rs:520-548)
// ZERO previous coverage for set/clear lifecycle
// =============================================================================

#[test]
fn test_set_trace_collector_enables_tracing() {
    use crate::cert::ThreadedCollector;
    use std::sync::Arc;

    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);

    // Set a real trace collector
    let collector: crate::cert::SharedTraceCollector = Arc::new(ThreadedCollector::new());
    tc.set_trace_collector(Some(collector.clone()));

    assert!(
        tc.trace_collector().is_some(),
        "Trace collector should be set after set_trace_collector(Some(...))"
    );
    assert!(
        tc.tracing_enabled(),
        "Tracing should be enabled with ThreadedCollector"
    );

    // Clear the trace collector
    tc.set_trace_collector(None);
    assert!(
        tc.trace_collector().is_none(),
        "Trace collector should be None after set_trace_collector(None)"
    );
    assert!(
        !tc.tracing_enabled(),
        "Tracing should be disabled after clearing collector"
    );
}

#[test]
fn test_null_collector_reports_tracing_disabled() {
    use crate::cert::NullCollector;
    use std::sync::Arc;

    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);

    // NullCollector is set but reports enabled() = false
    let collector: crate::cert::SharedTraceCollector = Arc::new(NullCollector);
    tc.set_trace_collector(Some(collector));

    assert!(
        tc.trace_collector().is_some(),
        "Collector should be set even with NullCollector"
    );
    assert!(
        !tc.tracing_enabled(),
        "NullCollector should report tracing as disabled"
    );
}
