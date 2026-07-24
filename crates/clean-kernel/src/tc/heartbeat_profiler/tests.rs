// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the heartbeat profiler.

use super::profiler::HeartbeatProfiler;
use super::types::{round_up_to_next, HeartbeatProfileCategory, OverrunEstimate, SourcePos};
use super::MAX_DISTINCT_POSITIONS;
use crate::name::Name;

#[test]
fn test_profiler_tick_categories() {
    let profiler = HeartbeatProfiler::new();
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    profiler.tick(HeartbeatProfileCategory::IsDefEq, None);
    profiler.tick(HeartbeatProfileCategory::InferType, None);

    assert_eq!(profiler.total_ticks_raw(), 4);
    assert_eq!(
        profiler.category_count_for(HeartbeatProfileCategory::Whnf),
        2
    );
    assert_eq!(
        profiler.category_count_for(HeartbeatProfileCategory::IsDefEq),
        1
    );
    assert_eq!(
        profiler.category_count_for(HeartbeatProfileCategory::InferType),
        1
    );
}

#[test]
fn test_profiler_tick_with_explicit_name() {
    let profiler = HeartbeatProfiler::new();
    let name = Name::from_string("Nat.add");

    profiler.tick(HeartbeatProfileCategory::Whnf, Some(&name));
    profiler.tick(HeartbeatProfileCategory::Whnf, Some(&name));
    profiler.tick(HeartbeatProfileCategory::Whnf, None);

    assert_eq!(profiler.total_ticks_raw(), 3);
    assert_eq!(profiler.name_count_for(&name), 2);
}

#[test]
fn test_profiler_tick_uses_active_name_when_explicit_name_missing() {
    let profiler = HeartbeatProfiler::new();
    let name = Name::from_string("Nat.add");

    profiler.set_active_name(name.clone());
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    profiler.clear_active_name();
    profiler.tick(HeartbeatProfileCategory::Whnf, None);

    assert_eq!(profiler.total_ticks_raw(), 3);
    assert_eq!(profiler.name_count_for(&name), 2);
}

#[test]
fn test_profiler_report_sorted() {
    let profiler = HeartbeatProfiler::new();
    for _ in 0..100 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    for _ in 0..50 {
        profiler.tick(HeartbeatProfileCategory::IsDefEq, None);
    }
    for _ in 0..10 {
        profiler.tick(HeartbeatProfileCategory::InferType, None);
    }

    let report = profiler.report(200_000, 10);
    assert_eq!(report.total, 160);
    assert_eq!(report.limit, 200_000);
    assert_eq!(report.categories.len(), 3);
    assert_eq!(
        report.categories[0].category,
        HeartbeatProfileCategory::Whnf
    );
    assert_eq!(report.categories[0].heartbeats, 100);
}

#[test]
fn test_profiler_report_top_n_names() {
    let profiler = HeartbeatProfiler::new();

    profiler.set_active_name(Name::from_string("A"));
    for _ in 0..50 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }

    profiler.set_active_name(Name::from_string("B"));
    for _ in 0..30 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }

    profiler.set_active_name(Name::from_string("C"));
    for _ in 0..10 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }

    let report = profiler.report(200_000, 2);
    assert_eq!(report.top_names.len(), 2);
    assert_eq!(report.top_names[0].name, Name::from_string("A"));
    assert_eq!(report.top_names[0].heartbeats, 50);
    assert_eq!(report.top_names[1].name, Name::from_string("B"));
    assert_eq!(report.top_names[1].heartbeats, 30);
}

#[test]
fn test_profiler_display_format() {
    let profiler = HeartbeatProfiler::new();
    profiler.set_active_name(Name::from_string("Nat.add"));
    for _ in 0..142_000 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.set_active_name(Name::from_string("StateT.bind"));
    for _ in 0..48_000 {
        profiler.tick(HeartbeatProfileCategory::IsDefEq, None);
    }
    profiler.clear_active_name();
    for _ in 0..10_000 {
        profiler.tick(HeartbeatProfileCategory::InferType, None);
    }

    let report = profiler.report(200_000, 10);
    let display = format!("{report}");
    assert!(display.contains("Heartbeat profile"));
    assert!(display.contains("whnf"));
    assert!(display.contains("isDefEq"));
    assert!(display.contains("inferType"));
    assert!(display.contains("Nat.add"));
    assert!(display.contains("StateT.bind"));
    assert!(display.contains("Projected total:"));
    assert!(display.contains("Suggestion: set_option maxHeartbeats"));
}

#[test]
fn test_profiler_reset() {
    let profiler = HeartbeatProfiler::new();
    profiler.set_active_name(Name::from_string("test"));
    profiler.push_tactic("simp");
    profiler.push_position(SourcePos::new(0, 10, 1));
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    assert_eq!(profiler.total_ticks_raw(), 1);

    profiler.reset();
    assert_eq!(profiler.total_ticks_raw(), 0);
    assert!(profiler.category_counts_empty());
    assert!(profiler.name_counts_empty());
    assert!(profiler.active_name_is_none());
    assert!(profiler.tactic_stack_empty());
    assert!(profiler.position_stack_empty());
    assert!(profiler.tactic_counts_empty());
    assert!(profiler.tactic_invocations_empty());
    assert!(profiler.position_counts_empty());
}

#[test]
fn test_profile_category_display() {
    assert_eq!(format!("{}", HeartbeatProfileCategory::Whnf), "whnf");
    assert_eq!(format!("{}", HeartbeatProfileCategory::IsDefEq), "isDefEq");
    assert_eq!(
        format!("{}", HeartbeatProfileCategory::InferType),
        "inferType"
    );
}

// ── Phase A (#3399) — tactic & position attribution, overrun estimate ──

/// AC2: two `simp` invocations and one `cases` push: top_tactics[0]
/// is `simp` with invocations==2.
#[test]
fn tactic_attribution() {
    let profiler = HeartbeatProfiler::new();

    profiler.push_tactic("simp");
    for _ in 0..100 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.pop_tactic();

    profiler.push_tactic("cases");
    for _ in 0..25 {
        profiler.tick(HeartbeatProfileCategory::IsDefEq, None);
    }
    profiler.pop_tactic();

    profiler.push_tactic("simp");
    for _ in 0..50 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.pop_tactic();

    let report = profiler.report(200_000, 10);
    assert_eq!(report.top_tactics.len(), 2);
    let top = &report.top_tactics[0];
    assert_eq!(top.tactic, "simp");
    assert_eq!(top.heartbeats, 150);
    assert_eq!(top.invocations, 2);

    let cases_entry = report
        .top_tactics
        .iter()
        .find(|e| e.tactic == "cases")
        .expect("cases entry");
    assert_eq!(cases_entry.heartbeats, 25);
    assert_eq!(cases_entry.invocations, 1);
}

/// AC3: ticks under two distinct positions show both with correct counts.
#[test]
fn position_attribution() {
    let profiler = HeartbeatProfiler::new();

    let p1 = SourcePos::new(0, 10, 1);
    let p2 = SourcePos::new(0, 20, 1);

    profiler.push_position(p1);
    for _ in 0..40 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.pop_position();

    profiler.push_position(p2);
    for _ in 0..15 {
        profiler.tick(HeartbeatProfileCategory::IsDefEq, None);
    }
    profiler.pop_position();

    let report = profiler.report(200_000, 10);
    assert_eq!(report.top_positions.len(), 2);
    assert_eq!(report.top_positions[0].position, p1);
    assert_eq!(report.top_positions[0].heartbeats, 40);
    assert_eq!(report.top_positions[1].position, p2);
    assert_eq!(report.top_positions[1].heartbeats, 15);
}

/// AC4: suggested_limit is a multiple of 50_000 and strictly greater
/// than consumed.
#[test]
fn overrun_estimate() {
    // Below the first boundary
    let est = OverrunEstimate::from_consumed(1);
    assert_eq!(est.projected_total, 2);
    assert_eq!(est.suggested_limit % 50_000, 0);
    assert!(u64::from(est.suggested_limit) >= 1);
    assert_eq!(est.suggested_limit, 50_000);

    // Near a boundary: consumed == projected_total == 50_000 must push
    // to the *next* boundary so the user gets a real bump.
    let est = OverrunEstimate::from_consumed(25_000);
    assert_eq!(est.projected_total, 50_000);
    assert_eq!(est.suggested_limit % 50_000, 0);
    assert!(u64::from(est.suggested_limit) > 25_000);
    assert_eq!(est.suggested_limit, 100_000);

    // Bigger input: suggested_limit > projected_total, still aligned.
    let est = OverrunEstimate::from_consumed(200_000);
    assert_eq!(est.projected_total, 400_000);
    assert_eq!(est.suggested_limit % 50_000, 0);
    assert!(u64::from(est.suggested_limit) > est.projected_total);

    // Zero consumed still returns a usable suggestion.
    let est = OverrunEstimate::from_consumed(0);
    assert_eq!(est.projected_total, 0);
    assert_eq!(est.suggested_limit, 50_000);

    // Saturation near u64::MAX does not panic and clamps to u32::MAX.
    let est = OverrunEstimate::from_consumed(u64::MAX);
    assert_eq!(est.projected_total, u64::MAX);
    assert_eq!(est.suggested_limit, u32::MAX);
}

/// AC6 (profiler side): popping on an empty stack is a no-op, not a
/// panic; ticks without active tactic/position produce no per-scope
/// counts. The `TypeChecker::push_tactic_scope` wrapper layer adds a
/// further `if let Some(&profiler)` guard for zero overhead when
/// profiling is disabled.
#[test]
fn disabled_zero_cost() {
    let profiler = HeartbeatProfiler::new();
    profiler.pop_tactic();
    profiler.pop_position();
    profiler.tick(HeartbeatProfileCategory::Whnf, None);

    let report = profiler.report(100, 10);
    assert!(report.top_tactics.is_empty());
    assert!(report.top_positions.is_empty());
    assert_eq!(report.total, 1);
}

/// Ticks land on the innermost tactic/position when multiple scopes
/// are active.
#[test]
fn innermost_scope_attribution() {
    let profiler = HeartbeatProfiler::new();

    profiler.push_tactic("simp");
    profiler.push_tactic("rewrite");
    for _ in 0..30 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.pop_tactic(); // rewrite off
    for _ in 0..20 {
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
    }
    profiler.pop_tactic(); // simp off

    let report = profiler.report(200_000, 10);
    let rewrite = report
        .top_tactics
        .iter()
        .find(|e| e.tactic == "rewrite")
        .expect("rewrite entry");
    let simp = report
        .top_tactics
        .iter()
        .find(|e| e.tactic == "simp")
        .expect("simp entry");
    assert_eq!(rewrite.heartbeats, 30);
    assert_eq!(simp.heartbeats, 20);
    assert_eq!(rewrite.invocations, 1);
    assert_eq!(simp.invocations, 1);
}

/// Tactic invocation counts increment on push, not on tick.
#[test]
fn tactic_invocation_counts() {
    let profiler = HeartbeatProfiler::new();

    profiler.push_tactic("simp");
    profiler.pop_tactic();
    profiler.push_tactic("simp");
    profiler.pop_tactic();
    profiler.push_tactic("simp");
    profiler.pop_tactic();

    let report = profiler.report(200_000, 10);
    let simp = report
        .top_tactics
        .iter()
        .find(|e| e.tactic == "simp")
        .expect("simp entry");
    assert_eq!(simp.invocations, 3);
    assert_eq!(simp.heartbeats, 0);
}

/// The tactic- and position-stack depths are observable for debugging.
#[test]
fn stack_depth_tracking() {
    let profiler = HeartbeatProfiler::new();
    assert_eq!(profiler.tactic_depth(), 0);
    assert_eq!(profiler.position_depth(), 0);

    profiler.push_tactic("a");
    profiler.push_tactic("b");
    profiler.push_position(SourcePos::new(1, 1, 1));
    assert_eq!(profiler.tactic_depth(), 2);
    assert_eq!(profiler.position_depth(), 1);

    profiler.pop_tactic();
    profiler.pop_position();
    assert_eq!(profiler.tactic_depth(), 1);
    assert_eq!(profiler.position_depth(), 0);
}

/// Positions beyond MAX_DISTINCT_POSITIONS are coalesced into
/// (line/10, column 0) buckets rather than allocating unboundedly.
#[test]
fn position_coalescing_caps_map() {
    let profiler = HeartbeatProfiler::new();

    // Fill to the cap with distinct positions.
    for line in 1..=(MAX_DISTINCT_POSITIONS as u32) {
        let pos = SourcePos::new(1, line, 1);
        profiler.push_position(pos);
        profiler.tick(HeartbeatProfileCategory::Whnf, None);
        profiler.pop_position();
    }
    assert_eq!(profiler.position_count_len(), MAX_DISTINCT_POSITIONS);

    // One more new position must collapse into a coalesced bucket.
    let overflow_pos = SourcePos::new(1, (MAX_DISTINCT_POSITIONS as u32) + 1, 1);
    profiler.push_position(overflow_pos);
    profiler.tick(HeartbeatProfileCategory::Whnf, None);
    profiler.pop_position();

    assert!(profiler.position_count_len() <= MAX_DISTINCT_POSITIONS + 1);
    assert!(profiler.position_counts_has(overflow_pos.coalesced()));
}

/// `round_up_to_next` rounds up strictly past existing multiples.
#[test]
fn round_up_semantics() {
    assert_eq!(round_up_to_next(0, 50_000), 50_000);
    assert_eq!(round_up_to_next(1, 50_000), 50_000);
    assert_eq!(round_up_to_next(49_999, 50_000), 50_000);
    assert_eq!(round_up_to_next(50_000, 50_000), 100_000);
    assert_eq!(round_up_to_next(50_001, 50_000), 100_000);
    assert_eq!(round_up_to_next(175_000, 50_000), 200_000);
}

/// SourcePos Display renders the unknown sentinel and a populated
/// position in their expected forms.
#[test]
fn source_pos_display() {
    assert_eq!(format!("{}", SourcePos::unknown()), "<unknown>");
    assert_eq!(format!("{}", SourcePos::new(0, 10, 5)), "10:5");
    assert_eq!(format!("{}", SourcePos::new(7, 10, 5)), "#7:10:5");
}
