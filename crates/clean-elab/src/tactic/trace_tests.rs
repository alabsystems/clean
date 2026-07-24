// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for tactic execution tracing (`trace.rs`).

use super::trace::{TacticTrace, TraceResult};

#[test]
fn test_trace_new_is_disabled() {
    let trace = TacticTrace::new();
    assert!(!trace.is_enabled());
    assert!(trace.entries().is_empty());
    assert_eq!(trace.current_depth(), 0);
}

#[test]
fn test_trace_default_is_disabled() {
    let trace = TacticTrace::default();
    assert!(!trace.is_enabled());
    assert!(trace.entries().is_empty());
}

#[test]
fn test_trace_enable_disable() {
    let mut trace = TacticTrace::new();
    assert!(!trace.is_enabled());
    trace.enable();
    assert!(trace.is_enabled());
    trace.disable();
    assert!(!trace.is_enabled());
}

#[test]
fn test_trace_disabled_enter_exit_noop() {
    let mut trace = TacticTrace::new();
    // Disabled — enter/exit should be no-ops
    trace.enter("simp", 3);
    trace.exit(2, TraceResult::Success);
    assert!(trace.entries().is_empty());
    assert_eq!(trace.current_depth(), 0);
}

#[test]
fn test_trace_single_entry_success() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("exact", 1);
    trace.exit(0, TraceResult::Success);

    assert_eq!(trace.entries().len(), 1);
    let entry = &trace.entries()[0];
    assert_eq!(entry.tactic_name, "exact");
    assert_eq!(entry.depth, 0);
    assert_eq!(entry.before_goals, 1);
    assert_eq!(entry.after_goals, 0);
    assert_eq!(entry.result, TraceResult::Success);
    // Duration should be non-negative (could be 0 on fast machines)
    // Just ensure it was recorded.
}

#[test]
fn test_trace_single_entry_failure() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("apply", 2);
    trace.exit(2, TraceResult::Failure("type mismatch".into()));

    assert_eq!(trace.entries().len(), 1);
    let entry = &trace.entries()[0];
    assert_eq!(entry.tactic_name, "apply");
    assert_eq!(entry.before_goals, 2);
    assert_eq!(entry.after_goals, 2);
    assert_eq!(entry.result, TraceResult::Failure("type mismatch".into()));
}

#[test]
fn test_trace_single_entry_skipped() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("norm_num", 1);
    trace.exit(1, TraceResult::Skipped);

    assert_eq!(trace.entries().len(), 1);
    assert_eq!(trace.entries()[0].result, TraceResult::Skipped);
}

#[test]
fn test_trace_nested_depth_tracking() {
    let mut trace = TacticTrace::new();
    trace.enable();

    // Outer tactic
    trace.enter("simp", 3);
    assert_eq!(trace.current_depth(), 1);

    // Inner tactic
    trace.enter("norm_num", 3);
    assert_eq!(trace.current_depth(), 2);

    // Exit inner
    trace.exit(2, TraceResult::Success);
    assert_eq!(trace.current_depth(), 1);

    // Exit outer
    trace.exit(2, TraceResult::Success);
    assert_eq!(trace.current_depth(), 0);

    assert_eq!(trace.entries().len(), 2);
    // Inner exits first (stack order)
    assert_eq!(trace.entries()[0].tactic_name, "norm_num");
    assert_eq!(trace.entries()[0].depth, 1);
    assert_eq!(trace.entries()[1].tactic_name, "simp");
    assert_eq!(trace.entries()[1].depth, 0);
}

#[test]
fn test_trace_success_failure_counts() {
    let mut trace = TacticTrace::new();
    trace.enable();

    trace.enter("intro", 2);
    trace.exit(2, TraceResult::Success);

    trace.enter("exact", 2);
    trace.exit(2, TraceResult::Failure("no match".into()));

    trace.enter("assumption", 2);
    trace.exit(1, TraceResult::Success);

    trace.enter("ring", 1);
    trace.exit(1, TraceResult::Skipped);

    assert_eq!(trace.success_count(), 2);
    assert_eq!(trace.failure_count(), 1);
    assert_eq!(trace.skipped_count(), 1);
}

#[test]
fn test_trace_total_duration_ns() {
    let mut trace = TacticTrace::new();
    trace.enable();

    trace.enter("simp", 1);
    // Tiny delay to ensure non-zero duration on most platforms
    for _ in 0..100 {
        std::hint::black_box(42);
    }
    trace.exit(0, TraceResult::Success);

    // Duration is at least 0 (cannot assert > 0 reliably on all hardware)
    let _ = trace.total_duration_ns();
    assert_eq!(trace.entries().len(), 1);
}

#[test]
fn test_trace_format_empty() {
    let trace = TacticTrace::new();
    assert_eq!(trace.format_trace(), "(empty trace)");
}

#[test]
fn test_trace_format_single() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("exact", 1);
    trace.exit(0, TraceResult::Success);

    let output = trace.format_trace();
    assert!(output.contains("exact"));
    assert!(output.contains("1 -> 0 goals"));
    assert!(output.contains("[Success]"));
}

#[test]
fn test_trace_format_nested_indentation() {
    let mut trace = TacticTrace::new();
    trace.enable();

    trace.enter("simp", 3);
    trace.enter("norm_num", 3);
    trace.exit(2, TraceResult::Success);
    trace.exit(2, TraceResult::Success);

    let output = trace.format_trace();
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines.len(), 2);
    // Inner entry (depth=1) should have 2-space indent
    assert!(lines[0].starts_with("  "));
    // Outer entry (depth=0) should have no indent
    assert!(!lines[1].starts_with(' '));
}

#[test]
fn test_trace_format_failure_message() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("linarith", 1);
    trace.exit(1, TraceResult::Failure("no certificate".into()));

    let output = trace.format_trace();
    assert!(output.contains("[Failure: no certificate]"));
}

#[test]
fn test_trace_clear() {
    let mut trace = TacticTrace::new();
    trace.enable();
    trace.enter("simp", 1);
    trace.exit(0, TraceResult::Success);
    assert_eq!(trace.entries().len(), 1);

    trace.clear();
    assert!(trace.entries().is_empty());
    assert_eq!(trace.current_depth(), 0);
}

#[test]
fn test_trace_exit_without_enter_is_noop() {
    let mut trace = TacticTrace::new();
    trace.enable();
    // No matching enter — should not panic or add entry
    trace.exit(0, TraceResult::Success);
    assert!(trace.entries().is_empty());
    assert_eq!(trace.current_depth(), 0);
}

#[test]
fn test_trace_multiple_sequential_entries() {
    let mut trace = TacticTrace::new();
    trace.enable();

    trace.enter("intro", 3);
    trace.exit(3, TraceResult::Success);

    trace.enter("apply", 3);
    trace.exit(4, TraceResult::Success);

    trace.enter("exact", 4);
    trace.exit(3, TraceResult::Success);

    assert_eq!(trace.entries().len(), 3);
    assert_eq!(trace.entries()[0].tactic_name, "intro");
    assert_eq!(trace.entries()[1].tactic_name, "apply");
    assert_eq!(trace.entries()[2].tactic_name, "exact");
    // All at depth 0 (sequential, not nested)
    assert!(trace.entries().iter().all(|e| e.depth == 0));
}

#[test]
fn test_trace_enable_mid_sequence() {
    let mut trace = TacticTrace::new();

    // Disabled — not recorded
    trace.enter("intro", 2);
    trace.exit(2, TraceResult::Success);

    // Enable mid-sequence
    trace.enable();
    trace.enter("apply", 2);
    trace.exit(3, TraceResult::Success);

    assert_eq!(trace.entries().len(), 1);
    assert_eq!(trace.entries()[0].tactic_name, "apply");
}
