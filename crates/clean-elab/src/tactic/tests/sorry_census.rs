// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sorry census: tracks sorry term creation across tactic test runs.
//!
//! This module provides a census test that reports sorry usage metrics and
//! enforces a ratchet baseline — the sorry count must never increase above
//! the recorded baseline in `scripts/sorry_baseline.json`.
//!
//! The census captures the cumulative sorry count from all prior tests in the
//! same process. In parallel test runs this is approximate, but the ratchet
//! direction (never increase) remains valid.
//!
//! Part of #1144 sorry enforcement.

use clean_kernel::sorry::{
    create_sorry_term, enable_sorry_location_tracking, reset_sorry_counter, sorry_count,
    sorry_lifetime_count, sorry_locations,
};
use clean_kernel::Environment;
use serial_test::serial;

/// Intentional or test-only sorry producers that should not count against the
/// proof-reconstruction ratchet.
const RATCHET_EXEMPT_SORRY_PREFIXES: &[&str] = &[
    "crates/clean-elab/src/infer/tests/sorry.rs:",
    "crates/clean-elab/src/tactic/tests/sorry_census.rs:",
    "crates/clean-elab/src/tactic/tests/sorry_runtime/",
    "crates/clean-elab/src/tactic/smt/tests.rs:",
    "crates/clean-elab/src/tactic/arith_linarith/trusted_arith.rs:",
    "crates/clean-elab/src/tactic/term_close/mod.rs:",
    "crates/clean-kernel/src/sorry/",
];

/// Exact fixture-key overrides that are exempt from the sorry ratchet.
/// These are stable identifiers set via `with_sorry_location_key` in tests
/// whose purpose is to inspect provenance/warning behavior, not to represent
/// tracked runtime debt. (#2770)
const RATCHET_EXEMPT_SORRY_FIXTURE_KEYS: &[&str] = &[
    "fixture:sorry:infer:explicit_provenance",
    "fixture:sorry:infer:synthetic_parser_recovery",
    "fixture:sorry:registration_warning:explicit",
    "fixture:sorry:registration_warning:synthetic",
];

/// Read the baseline sorry count from scripts/sorry_baseline.json.
/// Returns None if the file doesn't exist or can't be parsed.
fn read_sorry_baseline() -> Option<u64> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()?
        .parent()?
        .join("scripts")
        .join("sorry_baseline.json");
    let content = std::fs::read_to_string(path).ok()?;
    let value: serde_json::Value = serde_json::from_str(&content).ok()?;
    value.get("sorry_count_baseline")?.as_u64()
}

fn is_ratchet_exempt_location(location: &str) -> bool {
    RATCHET_EXEMPT_SORRY_PREFIXES
        .iter()
        .any(|prefix| location.starts_with(prefix))
        || RATCHET_EXEMPT_SORRY_FIXTURE_KEYS.contains(&location)
}

#[test]
fn test_sorry_runtime_directory_locations_are_ratchet_exempt() {
    assert!(is_ratchet_exempt_location(
        "crates/clean-elab/src/tactic/tests/sorry_runtime/workloads.rs:167"
    ));
    assert!(is_ratchet_exempt_location(
        "crates/clean-elab/src/tactic/tests/sorry_runtime/ratchet.rs:34"
    ));
    assert!(!is_ratchet_exempt_location(
        "crates/clean-elab/src/tactic/tests/sorry_runtime_extra.rs:12"
    ));
}

fn sorted_sorry_locations() -> Vec<(String, u64)> {
    let mut sorted: Vec<_> = sorry_locations().unwrap_or_default().into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    sorted
}

fn ratchet_counts(locations: &[(String, u64)]) -> (u64, u64) {
    let mut tracked = 0;
    let mut exempt = 0;
    for (location, count) in locations {
        if is_ratchet_exempt_location(location) {
            exempt += *count;
        } else {
            tracked += *count;
        }
    }
    (tracked, exempt)
}

/// Census test: reports sorry term locations after a representative tactic run.
///
/// This test enables location tracking, runs a representative set of tactic
/// operations that may produce sorry terms, and reports the results. The
/// test itself always passes — it is an observability tool.
///
/// Run: `cargo test -p clean-elab --lib -- sorry_census`
#[test]
#[serial]
fn test_sorry_census_report() {
    // Enable location tracking so future sorry terms get recorded.
    // We do NOT reset the counter — this captures the cumulative count
    // from all prior tests in this process, which is the metric we track.
    enable_sorry_location_tracking();

    let lifetime_total = sorry_lifetime_count();
    let locations = sorted_sorry_locations();
    let (tracked, exempt) = ratchet_counts(&locations);
    let location_total = tracked + exempt;

    eprintln!("=== SORRY CENSUS ===");
    eprintln!("Tracked sorry terms (ratchet-relevant): {}", tracked);
    if exempt > 0 {
        eprintln!("Excluded intentional/test-only sorry terms: {}", exempt);
    }
    eprintln!("Location-mapped total: {}", location_total);
    eprintln!("Lifetime total: {}", lifetime_total);
    // The location map total may be less than the lifetime counter because
    // other tests call `reset_sorry_locations()` to isolate their assertions,
    // which clears the map without affecting the monotonic lifetime counter.
    // The ratchet uses only location-tracked data (not the lifetime counter),
    // so this divergence does not affect ratchet correctness.
    if location_total != lifetime_total {
        eprintln!(
            "NOTE: location map ({}) < lifetime counter ({}) — expected when \
             other tests reset sorry locations for isolation",
            location_total, lifetime_total
        );
    }

    if !locations.is_empty() {
        for (loc, cnt) in &locations {
            let marker = if is_ratchet_exempt_location(loc) {
                " (exempt)"
            } else {
                ""
            };
            eprintln!("  {} x{}{}", loc, cnt, marker);
        }
    }
    eprintln!("=== END SORRY CENSUS ===");
}

/// Ratchet test: ensures sorry count does not exceed the recorded baseline.
///
/// Reads `scripts/sorry_baseline.json` and asserts that the current sorry
/// count (from the entire test process) does not exceed the baseline.
/// If the baseline file doesn't exist, this test is skipped (passes trivially).
///
/// **Important:** This test is only meaningful when run as part of the full
/// test suite (`cargo test -p clean-elab --lib`). When run in isolation, the
/// lifetime counter is 0 (no prior tactic tests produced sorry terms), which
/// trivially passes the ratchet. The ratchet catches regressions in the full
/// suite where tactic tests collectively produce sorry terms.
///
/// The ratchet works one-directionally: when proof reconstruction improves
/// and sorry count decreases, the baseline should be lowered to lock in
/// the improvement. Increases require explicit baseline bumps with justification.
#[test]
#[serial]
fn test_sorry_ratchet() {
    let baseline = match read_sorry_baseline() {
        Some(b) => b,
        None => {
            eprintln!("SORRY RATCHET: no baseline file found, skipping ratchet check");
            eprintln!("Create scripts/sorry_baseline.json to enable ratchet enforcement");
            return;
        }
    };

    let locations = sorted_sorry_locations();
    let (current, exempt) = ratchet_counts(&locations);

    eprintln!("=== SORRY RATCHET ===");
    eprintln!("Baseline: {}", baseline);
    eprintln!("Current:  {}", current);
    if exempt > 0 {
        eprintln!("Excluded: {}", exempt);
    }

    // Detect isolated run: if count is 0 but baseline > 0, this test is
    // running without the full tactic test suite providing sorry data.
    // The ratchet is still valid (0 <= baseline) but the "improvement"
    // message would be misleading.
    if current == 0 && baseline > 0 {
        eprintln!(
            "NOTE: sorry count is 0 with baseline {}. This test is likely \
             running in isolation (no prior tactic tests produced sorry terms). \
             Run with full suite for meaningful ratchet validation.",
            baseline
        );
        eprintln!("=== END SORRY RATCHET ===");
        return;
    }

    assert!(
        current <= baseline,
        "SORRY RATCHET FAILED: sorry count {} exceeds baseline {}. \
         Proof reconstruction regressed. Either fix the regression or \
         bump scripts/sorry_baseline.json with justification.",
        current,
        baseline
    );

    if current < baseline {
        eprintln!(
            "IMPROVEMENT: sorry count decreased by {} (from {} to {}). \
             Consider lowering the baseline to lock in this improvement.",
            baseline - current,
            baseline,
            current
        );
    }
    eprintln!("=== END SORRY RATCHET ===");
}

/// Mechanism test: validates that the sorry ratchet infrastructure works
/// correctly, independent of the full test suite.
///
/// This test directly creates sorry terms and verifies:
/// 1. `sorry_lifetime_count` increments correctly (never reset)
/// 2. `sorry_count` increments and resets correctly
/// 3. The ratchet comparison logic (current <= baseline) is sound
///
/// Unlike `test_sorry_ratchet` which depends on other tests producing sorry
/// terms, this test is self-contained and validates the mechanism itself.
#[test]
#[serial]
fn test_sorry_ratchet_mechanism() {
    let initial_lifetime = sorry_lifetime_count();
    reset_sorry_counter();

    let env = Environment::new();

    // Create exactly 3 sorry terms
    for _ in 0..3 {
        let _ = create_sorry_term(&env, &clean_kernel::Expr::prop());
    }

    // Verify resettable counter
    assert_eq!(
        sorry_count(),
        3,
        "sorry_count should be 3 after 3 create_sorry_term calls"
    );

    // Verify lifetime counter incremented by exactly 3
    let after_lifetime = sorry_lifetime_count();
    assert_eq!(
        after_lifetime - initial_lifetime,
        3,
        "sorry_lifetime_count should increment by exactly 3 \
         (before={}, after={})",
        initial_lifetime,
        after_lifetime
    );

    // Verify reset doesn't affect lifetime counter
    reset_sorry_counter();
    assert_eq!(sorry_count(), 0, "sorry_count should be 0 after reset");
    assert_eq!(
        sorry_lifetime_count(),
        after_lifetime,
        "sorry_lifetime_count must not be affected by reset"
    );
}

/// Validates the ratchet comparison logic that test_sorry_ratchet uses.
///
/// test_sorry_ratchet_mechanism validates counter mechanics (increment/reset)
/// but never tests the actual ratchet comparison: current <= baseline.
/// This test directly validates both paths:
/// 1. Regression detection: current > baseline → ratchet would fail
/// 2. Improvement detection: current < baseline → ratchet would pass
/// 3. Exact match: current == baseline → ratchet would pass
///
/// Re: #1144, Re: #2153.
#[test]
#[serial]
fn test_sorry_ratchet_comparison_logic() {
    reset_sorry_counter();
    let initial_lifetime = sorry_lifetime_count();

    let env = Environment::new();

    // Create exactly 5 sorry terms
    for _ in 0..5 {
        let _ = create_sorry_term(&env, &clean_kernel::Expr::prop());
    }

    let current = sorry_lifetime_count() - initial_lifetime;
    assert_eq!(current, 5, "should have created exactly 5 sorry terms");

    // Ratchet comparison: current <= baseline
    // Regression case: baseline = 3, current = 5 → would fail
    let regression_baseline: u64 = 3;
    assert!(
        current > regression_baseline,
        "current ({current}) should exceed regression baseline ({regression_baseline})"
    );

    // Improvement case: baseline = 9, current = 5 → would pass
    let improvement_baseline: u64 = 9;
    assert!(
        current <= improvement_baseline,
        "current ({current}) should not exceed improvement baseline ({improvement_baseline})"
    );

    // Exact match case: baseline = 5, current = 5 → would pass
    let exact_baseline: u64 = 5;
    assert!(
        current <= exact_baseline,
        "current ({current}) should equal exact baseline ({exact_baseline})"
    );

    // Verify the improvement delta calculation matches
    let improvement_delta = improvement_baseline - current;
    assert_eq!(
        improvement_delta, 4,
        "improvement delta should be 4 (baseline 9 - current 5)"
    );
}

// =========================================================================
// Fixture-key exemption tests (#2770)
// =========================================================================

#[test]
fn test_fixture_keys_are_ratchet_exempt() {
    for key in RATCHET_EXEMPT_SORRY_FIXTURE_KEYS {
        assert!(
            is_ratchet_exempt_location(key),
            "fixture key {key:?} should be ratchet-exempt"
        );
    }
}

#[test]
fn test_near_match_fixture_key_is_not_exempt() {
    // A key that starts with "fixture:" but isn't in the exact-match list
    assert!(
        !is_ratchet_exempt_location("fixture:sorry:infer:unknown_lane"),
        "near-match fixture key should NOT be exempt (exact-match only)"
    );
    assert!(
        !is_ratchet_exempt_location("fixture:sorry:registration_warning:explicit:extra"),
        "extended fixture key should NOT be exempt (exact-match only)"
    );
}

#[test]
fn test_raw_file_line_locations_unchanged_by_fixture_keys() {
    // Verify that existing prefix-based exemptions still work
    assert!(is_ratchet_exempt_location(
        "crates/clean-elab/src/infer/tests/sorry.rs:42"
    ));
    // Verify that non-exempt raw file:line locations are still tracked
    assert!(!is_ratchet_exempt_location(
        "crates/clean-elab/src/infer/elab_core.rs:27"
    ));
}
