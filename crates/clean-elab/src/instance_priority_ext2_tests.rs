// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended instance priority resolution (ext2).

use crate::instance_priority_ext2::*;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

// ===========================================================================
// Helpers
// ===========================================================================

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// Make a simple const expression for testing.
fn cexpr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Make a type expression `ClassName TypeArg` for testing.
fn app_type(class: &str, type_arg: &str) -> Expr {
    Expr::app(cexpr(class), cexpr(type_arg))
}

fn register_test_instance(
    ext: &mut InstancePriorityExt2,
    name: &str,
    class: &str,
    type_arg: &str,
    priority: u32,
    specificity: u32,
) {
    ext.register(
        n(name),
        n(class),
        cexpr(name),
        app_type(class, type_arg),
        priority,
        specificity,
        None,
    );
}

// ===========================================================================
// Priority ordering
// ===========================================================================

#[test]
fn test_sorted_candidates_by_priority() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "low", "Add", "Nat", 50, 1);
    register_test_instance(&mut ext, "high", "Add", "Nat", 500, 1);
    register_test_instance(&mut ext, "mid", "Add", "Nat", 100, 1);

    let sorted = ext.sorted_candidates(&n("Add"));
    assert_eq!(sorted.len(), 3);
    assert_eq!(sorted[0].name, n("high"));
    assert_eq!(sorted[1].name, n("mid"));
    assert_eq!(sorted[2].name, n("low"));
}

#[test]
fn test_sorted_candidates_empty_class() {
    let ext = InstancePriorityExt2::new();
    let sorted = ext.sorted_candidates(&n("Unknown"));
    assert!(sorted.is_empty());
}

#[test]
fn test_sorted_candidates_single() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "only", "Add", "Nat", 100, 1);

    let sorted = ext.sorted_candidates(&n("Add"));
    assert_eq!(sorted.len(), 1);
    assert_eq!(sorted[0].name, n("only"));
}

// ===========================================================================
// Default priority assignment
// ===========================================================================

#[test]
fn test_default_priority_base() {
    assert_eq!(
        InstancePriorityExt2::default_priority_for_specificity(0),
        100
    );
}

#[test]
fn test_default_priority_scales_with_specificity() {
    assert_eq!(
        InstancePriorityExt2::default_priority_for_specificity(1),
        110
    );
    assert_eq!(
        InstancePriorityExt2::default_priority_for_specificity(5),
        150
    );
    assert_eq!(
        InstancePriorityExt2::default_priority_for_specificity(10),
        200
    );
}

#[test]
fn test_default_priority_no_overflow() {
    // Very large specificity should saturate, not overflow.
    let p = InstancePriorityExt2::default_priority_for_specificity(u32::MAX);
    assert!(p >= 100);
}

// ===========================================================================
// Overlap detection
// ===========================================================================

#[test]
fn test_detect_overlaps_two_instances_same_type() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "inst1", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "inst2", "Add", "Nat", 200, 2);

    let overlaps = ext.detect_overlaps(&n("Add"), &n("Nat"));
    assert_eq!(overlaps.len(), 1);
    let pair = [overlaps[0].first.clone(), overlaps[0].second.clone()];
    assert!(pair.contains(&n("inst1")));
    assert!(pair.contains(&n("inst2")));
}

#[test]
fn test_detect_overlaps_no_overlap_different_types() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "inst1", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "inst2", "Add", "Int", 200, 2);

    let overlaps = ext.detect_overlaps(&n("Add"), &n("Nat"));
    assert_eq!(overlaps.len(), 0);
}

#[test]
fn test_detect_overlaps_three_way() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "a", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "b", "Add", "Nat", 200, 1);
    register_test_instance(&mut ext, "c", "Add", "Nat", 300, 1);

    let overlaps = ext.detect_overlaps(&n("Add"), &n("Nat"));
    // (a,b), (a,c), (b,c)
    assert_eq!(overlaps.len(), 3);
}

#[test]
fn test_detect_overlaps_empty() {
    let mut ext = InstancePriorityExt2::new();
    let overlaps = ext.detect_overlaps(&n("Add"), &n("Nat"));
    assert!(overlaps.is_empty());
}

#[test]
fn test_detect_overlaps_with_local() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "global", "Add", "Nat", 100, 1);
    ext.register_local(
        n("local"),
        n("Add"),
        cexpr("local"),
        app_type("Add", "Nat"),
        200,
        1,
    );

    let overlaps = ext.detect_overlaps(&n("Add"), &n("Nat"));
    assert_eq!(overlaps.len(), 1);
}

// ===========================================================================
// Overlap resolution strategies
// ===========================================================================

#[test]
fn test_resolve_overlap_most_specific_wins() {
    let ext = InstancePriorityExt2::with_config(OverlapStrategy::MostSpecificWins, 32);
    let c1 = InstanceCandidate {
        name: n("general"),
        class: n("Add"),
        expr: cexpr("general"),
        type_: app_type("Add", "Nat"),
        priority: 200,
        specificity: 1,
        is_local: false,
        defining_module: None,
    };
    let c2 = InstanceCandidate {
        name: n("specific"),
        class: n("Add"),
        expr: cexpr("specific"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 3,
        is_local: false,
        defining_module: None,
    };

    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[&c1, &c2]);
    assert_eq!(result.expect("should resolve"), n("specific"));
}

#[test]
fn test_resolve_overlap_explicit_priority_wins() {
    let ext = InstancePriorityExt2::with_config(OverlapStrategy::ExplicitPriorityWins, 32);
    let c1 = InstanceCandidate {
        name: n("low_prio"),
        class: n("Add"),
        expr: cexpr("low_prio"),
        type_: app_type("Add", "Nat"),
        priority: 50,
        specificity: 3,
        is_local: false,
        defining_module: None,
    };
    let c2 = InstanceCandidate {
        name: n("high_prio"),
        class: n("Add"),
        expr: cexpr("high_prio"),
        type_: app_type("Add", "Nat"),
        priority: 500,
        specificity: 1,
        is_local: false,
        defining_module: None,
    };

    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[&c1, &c2]);
    assert_eq!(result.expect("should resolve"), n("high_prio"));
}

#[test]
fn test_resolve_overlap_error_on_ambiguity() {
    let ext = InstancePriorityExt2::with_config(OverlapStrategy::ErrorOnAmbiguity, 32);
    let c1 = InstanceCandidate {
        name: n("inst1"),
        class: n("Add"),
        expr: cexpr("inst1"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 1,
        is_local: false,
        defining_module: None,
    };
    let c2 = InstanceCandidate {
        name: n("inst2"),
        class: n("Add"),
        expr: cexpr("inst2"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 1,
        is_local: false,
        defining_module: None,
    };

    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[&c1, &c2]);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, InstanceResolutionError::AmbiguousOverlap { .. }),
        "expected AmbiguousOverlap, got: {err:?}"
    );
}

#[test]
fn test_resolve_overlap_tie_most_specific() {
    let ext = InstancePriorityExt2::with_config(OverlapStrategy::MostSpecificWins, 32);
    let c1 = InstanceCandidate {
        name: n("a"),
        class: n("Add"),
        expr: cexpr("a"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 2,
        is_local: false,
        defining_module: None,
    };
    let c2 = InstanceCandidate {
        name: n("b"),
        class: n("Add"),
        expr: cexpr("b"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 2,
        is_local: false,
        defining_module: None,
    };

    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[&c1, &c2]);
    assert!(result.is_err(), "tied specificity should be ambiguous");
}

#[test]
fn test_resolve_overlap_single_candidate() {
    let ext = InstancePriorityExt2::new();
    let c = InstanceCandidate {
        name: n("only"),
        class: n("Add"),
        expr: cexpr("only"),
        type_: app_type("Add", "Nat"),
        priority: 100,
        specificity: 1,
        is_local: false,
        defining_module: None,
    };

    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[&c]);
    assert_eq!(result.expect("single should resolve"), n("only"));
}

#[test]
fn test_resolve_overlap_empty_candidates() {
    let ext = InstancePriorityExt2::new();
    let result = ext.resolve_overlap(&n("Add"), &n("Nat"), &[]);
    assert!(result.is_err());
}

// ===========================================================================
// Orphan detection
// ===========================================================================

#[test]
fn test_orphan_class_local_ok() {
    let ext = InstancePriorityExt2::new();
    let result = ext.check_orphan(&n("inst"), &n("MyMod.Add"), &n("Foreign.Nat"), &n("MyMod"));
    assert!(result.is_ok());
}

#[test]
fn test_orphan_type_local_ok() {
    let ext = InstancePriorityExt2::new();
    let result = ext.check_orphan(
        &n("inst"),
        &n("Foreign.Add"),
        &n("MyMod.MyType"),
        &n("MyMod"),
    );
    assert!(result.is_ok());
}

#[test]
fn test_orphan_both_foreign_err() {
    let ext = InstancePriorityExt2::new();
    let result = ext.check_orphan(&n("inst"), &n("Foreign.Add"), &n("Other.Nat"), &n("MyMod"));
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err,
        InstanceResolutionError::OrphanInstance { .. }
    ));
}

#[test]
fn test_orphan_anonymous_module_always_ok() {
    let ext = InstancePriorityExt2::new();
    let result = ext.check_orphan(
        &n("inst"),
        &n("Foreign.Add"),
        &n("Foreign.Nat"),
        &Name::anon(),
    );
    assert!(result.is_ok());
}

// ===========================================================================
// Coherence checking
// ===========================================================================

#[test]
fn test_coherence_single_instance_ok() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "inst1", "Add", "Nat", 100, 1);

    let result = ext.check_coherence(&n("Add"), &n("Nat"));
    assert!(result.is_ok());
}

#[test]
fn test_coherence_two_instances_same_type_err() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "inst1", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "inst2", "Add", "Nat", 200, 2);

    let result = ext.check_coherence(&n("Add"), &n("Nat"));
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err,
        InstanceResolutionError::IncoherentInstances { .. }
    ));
}

#[test]
fn test_coherence_different_types_ok() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "inst1", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "inst2", "Add", "Int", 200, 2);

    let result = ext.check_coherence(&n("Add"), &n("Nat"));
    assert!(result.is_ok());
}

#[test]
fn test_coherence_with_local_instance() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "global", "Add", "Nat", 100, 1);
    ext.register_local(
        n("local"),
        n("Add"),
        cexpr("local"),
        app_type("Add", "Nat"),
        200,
        1,
    );

    let result = ext.check_coherence(&n("Add"), &n("Nat"));
    assert!(result.is_err());
}

// ===========================================================================
// Local instances
// ===========================================================================

#[test]
fn test_local_instances_prepended() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "global", "Add", "Nat", 100, 1);
    ext.register_local(
        n("local"),
        n("Add"),
        cexpr("local"),
        app_type("Add", "Nat"),
        50,
        1,
    );

    let sorted = ext.sorted_candidates(&n("Add"));
    assert_eq!(sorted.len(), 2);
    // Local comes first even with lower priority.
    assert!(sorted[0].is_local);
    assert_eq!(sorted[0].name, n("local"));
    assert_eq!(sorted[1].name, n("global"));
}

#[test]
fn test_clear_local_instances() {
    let mut ext = InstancePriorityExt2::new();
    ext.register_local(
        n("local"),
        n("Add"),
        cexpr("local"),
        app_type("Add", "Nat"),
        100,
        1,
    );
    assert_eq!(ext.total_local_candidates(), 1);

    ext.clear_local_instances();
    assert_eq!(ext.total_local_candidates(), 0);
    assert!(ext.sorted_candidates(&n("Add")).is_empty());
}

#[test]
fn test_multiple_local_instances_sorted() {
    let mut ext = InstancePriorityExt2::new();
    ext.register_local(
        n("loc_low"),
        n("Add"),
        cexpr("loc_low"),
        app_type("Add", "Nat"),
        50,
        1,
    );
    ext.register_local(
        n("loc_high"),
        n("Add"),
        cexpr("loc_high"),
        app_type("Add", "Nat"),
        200,
        1,
    );

    let sorted = ext.sorted_candidates(&n("Add"));
    assert_eq!(sorted.len(), 2);
    assert_eq!(sorted[0].name, n("loc_high"));
    assert_eq!(sorted[1].name, n("loc_low"));
}

// ===========================================================================
// Diamond resolution
// ===========================================================================

#[test]
fn test_record_diamond_resolved() {
    let mut ext = InstancePriorityExt2::new();
    assert_eq!(ext.stats().diamonds_resolved, 0);

    ext.record_diamond_resolved();
    assert_eq!(ext.stats().diamonds_resolved, 1);

    ext.record_diamond_resolved();
    assert_eq!(ext.stats().diamonds_resolved, 2);
}

// ===========================================================================
// Depth tracking
// ===========================================================================

#[test]
fn test_depth_tracker_basic() {
    let mut tracker = DepthTracker::new();
    assert_eq!(tracker.current_depth(), 0);
    assert_eq!(tracker.limit(), DEFAULT_DEPTH_LIMIT);

    tracker
        .enter(&n("Add"))
        .expect("should not exceed default limit");
    assert_eq!(tracker.current_depth(), 1);

    tracker.leave();
    assert_eq!(tracker.current_depth(), 0);
}

#[test]
fn test_depth_tracker_exceeds_limit() {
    let mut tracker = DepthTracker::with_limit(2);
    tracker.enter(&n("Add")).expect("depth 1");
    tracker.enter(&n("Add")).expect("depth 2");

    let result = tracker.enter(&n("Add"));
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(
        err,
        InstanceResolutionError::DepthLimitExceeded {
            depth: 3,
            limit: 2,
            ..
        }
    ));
}

#[test]
fn test_depth_tracker_max_observed() {
    let mut tracker = DepthTracker::with_limit(10);
    tracker.enter(&n("A")).expect("depth 1");
    tracker.enter(&n("B")).expect("depth 2");
    tracker.enter(&n("C")).expect("depth 3");
    assert_eq!(tracker.max_observed(), 3);

    tracker.leave();
    tracker.leave();
    assert_eq!(tracker.max_observed(), 3); // max is sticky
    assert_eq!(tracker.current_depth(), 1);
}

#[test]
fn test_depth_tracker_reset() {
    let mut tracker = DepthTracker::new();
    tracker.enter(&n("A")).expect("ok");
    tracker.enter(&n("B")).expect("ok");
    tracker.reset();
    assert_eq!(tracker.current_depth(), 0);
    assert_eq!(tracker.max_observed(), 2); // max is preserved
}

#[test]
fn test_depth_via_ext2() {
    let mut ext = InstancePriorityExt2::with_config(OverlapStrategy::default(), 3);
    ext.enter_depth(&n("A")).expect("depth 1");
    ext.enter_depth(&n("B")).expect("depth 2");
    ext.enter_depth(&n("C")).expect("depth 3");

    let result = ext.enter_depth(&n("D"));
    assert!(result.is_err());

    ext.leave_depth();
    ext.leave_depth();
    ext.leave_depth();
    assert_eq!(ext.depth_tracker().current_depth(), 0);
}

#[test]
fn test_depth_leave_saturates_at_zero() {
    let mut tracker = DepthTracker::new();
    tracker.leave(); // should not underflow
    assert_eq!(tracker.current_depth(), 0);
}

// ===========================================================================
// Statistics
// ===========================================================================

#[test]
fn test_stats_initial() {
    let ext = InstancePriorityExt2::new();
    let stats = ext.stats();
    assert_eq!(stats.instances_considered, 0);
    assert_eq!(stats.overlaps_detected, 0);
    assert_eq!(stats.diamonds_resolved, 0);
    assert_eq!(stats.depth_limit_hits, 0);
}

#[test]
fn test_stats_overlaps_counted() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "a", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "b", "Add", "Nat", 200, 1);

    ext.detect_overlaps(&n("Add"), &n("Nat"));
    assert_eq!(ext.stats().overlaps_detected, 1);
}

#[test]
fn test_stats_depth_limit_hits() {
    let mut ext = InstancePriorityExt2::with_config(OverlapStrategy::default(), 1);
    ext.enter_depth(&n("A")).expect("ok");
    let _ = ext.enter_depth(&n("B")); // exceeds limit
    assert_eq!(ext.stats().depth_limit_hits, 1);
}

#[test]
fn test_stats_coherence_violations() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "a", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "b", "Add", "Nat", 200, 1);

    let _ = ext.check_coherence(&n("Add"), &n("Nat"));
    assert_eq!(ext.stats().coherence_violations, 1);
}

#[test]
fn test_finalize_stats_copies_max_depth() {
    let mut ext = InstancePriorityExt2::new();
    ext.enter_depth(&n("A")).expect("ok");
    ext.enter_depth(&n("B")).expect("ok");
    ext.finalize_stats();
    assert_eq!(ext.stats().max_depth_observed, 2);
}

// ===========================================================================
// Configuration
// ===========================================================================

#[test]
fn test_default_strategy() {
    let ext = InstancePriorityExt2::new();
    assert_eq!(ext.strategy(), OverlapStrategy::ExplicitPriorityWins);
}

#[test]
fn test_custom_strategy() {
    let ext = InstancePriorityExt2::with_config(OverlapStrategy::MostSpecificWins, 64);
    assert_eq!(ext.strategy(), OverlapStrategy::MostSpecificWins);
    assert_eq!(ext.depth_tracker().limit(), 64);
}

// ===========================================================================
// Total counts
// ===========================================================================

#[test]
fn test_total_candidates_count() {
    let mut ext = InstancePriorityExt2::new();
    assert_eq!(ext.total_candidates(), 0);

    register_test_instance(&mut ext, "a", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "b", "Mul", "Nat", 100, 1);
    assert_eq!(ext.total_candidates(), 2);
}

#[test]
fn test_total_local_candidates_count() {
    let mut ext = InstancePriorityExt2::new();
    assert_eq!(ext.total_local_candidates(), 0);

    ext.register_local(n("l"), n("Add"), cexpr("l"), app_type("Add", "Nat"), 100, 1);
    assert_eq!(ext.total_local_candidates(), 1);
}

// ===========================================================================
// Error display
// ===========================================================================

#[test]
fn test_error_display_ambiguous() {
    let err = InstanceResolutionError::AmbiguousOverlap {
        class: n("Add"),
        type_name: n("Nat"),
        candidates: vec![n("a"), n("b")],
    };
    let msg = err.to_string();
    assert!(msg.contains("Add"));
    assert!(msg.contains("Nat"));
}

#[test]
fn test_error_display_depth() {
    let err = InstanceResolutionError::DepthLimitExceeded {
        class: n("Add"),
        depth: 33,
        limit: 32,
    };
    let msg = err.to_string();
    assert!(msg.contains("33"));
    assert!(msg.contains("32"));
}

#[test]
fn test_error_display_incoherent() {
    let err = InstanceResolutionError::IncoherentInstances {
        class: n("Add"),
        type_name: n("Nat"),
        first: n("inst1"),
        second: n("inst2"),
    };
    let msg = err.to_string();
    assert!(msg.contains("inst1"));
    assert!(msg.contains("inst2"));
}

#[test]
fn test_error_display_orphan() {
    let err = InstanceResolutionError::OrphanInstance {
        instance: n("bad"),
        class: n("Add"),
        type_name: n("Nat"),
    };
    let msg = err.to_string();
    assert!(msg.contains("bad"));
    assert!(msg.contains("orphan"));
}

// ===========================================================================
// Overlap accumulation across calls
// ===========================================================================

#[test]
fn test_detected_overlaps_accumulate() {
    let mut ext = InstancePriorityExt2::new();
    register_test_instance(&mut ext, "a", "Add", "Nat", 100, 1);
    register_test_instance(&mut ext, "b", "Add", "Nat", 200, 1);

    ext.detect_overlaps(&n("Add"), &n("Nat"));
    ext.detect_overlaps(&n("Add"), &n("Nat"));

    assert_eq!(ext.detected_overlaps().len(), 2);
    assert_eq!(ext.stats().overlaps_detected, 2);
}

#[test]
fn test_reset_depth_between_queries() {
    let mut ext = InstancePriorityExt2::with_config(OverlapStrategy::default(), 2);
    ext.enter_depth(&n("A")).expect("ok");
    ext.enter_depth(&n("B")).expect("ok");
    // At limit now.
    ext.reset_depth();
    // Should be able to enter again.
    ext.enter_depth(&n("C")).expect("ok after reset");
    assert_eq!(ext.depth_tracker().current_depth(), 1);
}
