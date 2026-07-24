// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for PendingForall::total_priority() and compute_premise_bonus().
//!
//! Design: `designs/archive/2026-01-28-ematching-premise-gaps.md` #224
//! Issue: #233

use std::collections::HashMap;

use super::*;
use crate::premise::PremiseId;

/// Helper: create a minimal PendingForall with the specified base priority and origin.
fn make_pending_with_origin(base_priority: i32, origin: Option<QuantifierOrigin>) -> PendingForall {
    PendingForall {
        _tys: vec![Expr::const_(Name::from_string("A"), vec![])],
        body: Expr::bvar(0),
        triggers: vec![],
        bound_vars: vec![0],
        priority: base_priority,
        instantiation_count: 0,
        origin,
    }
}

fn make_pending_with_premise(base_priority: i32, premise_id: Option<PremiseId>) -> PendingForall {
    make_pending_with_origin(
        base_priority,
        Some(QuantifierOrigin::Named {
            name: Name::from_string("test_premise"),
            premise_id,
        }),
    )
}

// ---------------------------------------------------------------------------
// compute_premise_bonus tests
// ---------------------------------------------------------------------------

#[test]
fn test_compute_premise_bonus_no_premise_id_returns_zero() {
    let pending = make_pending_with_premise(10, None);
    let scores = HashMap::new();
    assert_eq!(pending.compute_premise_bonus(&scores), 0);
}

#[test]
fn test_compute_premise_bonus_premise_id_not_in_scores_returns_zero() {
    let pending = make_pending_with_premise(10, Some(PremiseId(42)));
    let scores = HashMap::new();
    assert_eq!(pending.compute_premise_bonus(&scores), 0);
}

#[test]
fn test_compute_premise_bonus_score_zero_returns_min() {
    // score 0.0 → -15 + 0.0 * 45 = -15
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.0)]);
    assert_eq!(pending.compute_premise_bonus(&scores), -15);
}

#[test]
fn test_compute_premise_bonus_score_one_returns_max() {
    // score 1.0 → -15 + 1.0 * 45 = 30
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 1.0)]);
    assert_eq!(pending.compute_premise_bonus(&scores), 30);
}

#[test]
fn test_compute_premise_bonus_score_half() {
    // score 0.5 → -15 + 0.5 * 45 = -15 + 22.5 = 7.5 → rounds to 8
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.5)]);
    assert_eq!(pending.compute_premise_bonus(&scores), 8);
}

#[test]
fn test_compute_premise_bonus_high_relevance() {
    // score 0.9 → -15 + 0.9 * 45 = -15 + 40.5 = 25.5 → rounds to 26
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.9)]);
    assert_eq!(pending.compute_premise_bonus(&scores), 26);
}

#[test]
fn test_compute_premise_bonus_low_relevance() {
    // score 0.1 → -15 + 0.1 * 45 = -15 + 4.5 = -10.5 → rounds to -11 (away from zero)
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.1)]);
    assert_eq!(pending.compute_premise_bonus(&scores), -11);
}

#[test]
fn test_compute_premise_bonus_local_origin_is_neutral() {
    let pending = make_pending_with_origin(
        10,
        Some(QuantifierOrigin::Local {
            fvar_id: FVarId::new(7),
        }),
    );
    let scores = HashMap::from([(PremiseId(1), 1.0)]);
    assert_eq!(pending.compute_premise_bonus(&scores), 0);
}

#[test]
fn test_compute_premise_bonus_synthesized_origin_is_neutral() {
    let pending = make_pending_with_origin(10, Some(QuantifierOrigin::Synthesized));
    let scores = HashMap::from([(PremiseId(1), 1.0)]);
    assert_eq!(pending.compute_premise_bonus(&scores), 0);
}

// ---------------------------------------------------------------------------
// total_priority tests
// ---------------------------------------------------------------------------

#[test]
fn test_total_priority_no_scores_equals_base() {
    let pending = make_pending_with_premise(25, Some(PremiseId(1)));
    let scores = HashMap::new();
    assert_eq!(pending.total_priority(&scores), 25);
}

#[test]
fn test_total_priority_no_premise_id_equals_base() {
    let pending = make_pending_with_premise(25, None);
    let scores = HashMap::from([(PremiseId(1), 0.9)]);
    assert_eq!(pending.total_priority(&scores), 25);
}

#[test]
fn test_total_priority_combines_base_and_bonus() {
    // base = 10, score 0.9 → bonus 26, total = 36
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.9)]);
    assert_eq!(pending.total_priority(&scores), 36);
}

#[test]
fn test_total_priority_negative_bonus_reduces_total() {
    // base = 10, score 0.1 → bonus -11, total = -1
    let pending = make_pending_with_premise(10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 0.1)]);
    assert_eq!(pending.total_priority(&scores), -1);
}

#[test]
fn test_total_priority_ordering_high_vs_low_relevance() {
    // Two quantifiers with identical base priority but different relevance
    let high = make_pending_with_premise(10, Some(PremiseId(1)));
    let low = make_pending_with_premise(10, Some(PremiseId(2)));
    let scores = HashMap::from([
        (PremiseId(1), 0.9), // high relevance
        (PremiseId(2), 0.1), // low relevance
    ]);

    let total_high = high.total_priority(&scores);
    let total_low = low.total_priority(&scores);

    assert!(
        total_high > total_low,
        "high relevance total {total_high} should beat low relevance {total_low}"
    );

    // Verify exact values per design spec
    assert_eq!(total_high, 10 + 26); // 36
    assert_eq!(total_low, 10 - 11); // -1
}

#[test]
fn test_total_priority_saturating_add_no_overflow() {
    // Ensure saturating_add prevents overflow with extreme values
    let pending = make_pending_with_premise(i32::MAX - 10, Some(PremiseId(1)));
    let scores = HashMap::from([(PremiseId(1), 1.0)]);
    // bonus = 30, but base is near i32::MAX, so should saturate
    assert_eq!(pending.total_priority(&scores), i32::MAX);
}

// ---------------------------------------------------------------------------
// QuantifierOrigin unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_quantifier_origin_named_clone_debug() {
    let origin = QuantifierOrigin::Named {
        name: Name::from_string("my_lemma"),
        premise_id: Some(PremiseId(42)),
    };
    let cloned = origin.clone();
    let debug_str = format!("{:?}", cloned);
    assert!(debug_str.contains("Named"));
    assert!(debug_str.contains("42"));
    assert_eq!(origin.name(), Some(&Name::from_string("my_lemma")));
    assert_eq!(origin.premise_id(), Some(PremiseId(42)));
}

#[test]
fn test_quantifier_origin_local_variant() {
    let origin = QuantifierOrigin::Local {
        fvar_id: FVarId::new(99),
    };
    let debug_str = format!("{:?}", origin);
    assert!(debug_str.contains("Local"));
}

#[test]
fn test_quantifier_origin_synthesized_variant() {
    let origin = QuantifierOrigin::Synthesized;
    let debug_str = format!("{:?}", origin);
    assert!(debug_str.contains("Synthesized"));
    assert!(origin.is_empty());
}
