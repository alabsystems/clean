// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trusted axiom ratchet: prevents trustedArith and trustedAy counts from
//! increasing without explicit baseline bumps.
//!
//! Modeled after the sorry ratchet in `sorry_census.rs`. The ratchet is
//! one-directional: counts can only decrease (or stay same). When proof
//! reconstruction improves and a trusted axiom count decreases, the baseline
//! should be lowered to lock in the improvement.
//!
//! Baselines are stored in `scripts/sorry_baseline.json` alongside the sorry
//! baseline.
//!
//! Run: `cargo test -p clean-elab --lib -- trusted_ratchet`
//!
//! Part of #2231: trustedArith/trustedAy ratchet.

use crate::tactic::arith_linarith::{
    arith_lifetime_count, arith_locations, enable_arith_location_tracking,
};
use clean_kernel::sorry::{ay_lifetime_count, ay_locations, enable_ay_location_tracking};
use serial_test::serial;

/// Intentional test-only trustedArith producers that should not count against
/// the proof-reconstruction ratchet.
const RATCHET_EXEMPT_TRUSTED_ARITH_PREFIXES: &[&str] = &[
    "crates/clean-elab/src/tactic/tests/trusted_arith.rs:",
    "crates/clean-elab/src/tactic/tests/trusted_axiom_state.rs:",
    "crates/clean-elab/src/tactic/tests/trusted_axiom_fallback_sites.rs:",
    "crates/clean-elab/src/tactic/tests/trusted_ratchet.rs:",
    // Test-fixture files that exercise the replace-target wrapper (#2736)
    "crates/clean-elab/src/tactic/tests/replace_target.rs:",
    "crates/clean-elab/src/tactic/tests/replace_target_witness.rs:",
];

/// Helper provenance keys from test-fixture-only code paths.
/// These exercise the trust accounting API, not production proof gaps.
/// Exact-match only — a new helper key is NOT auto-exempted.
const RATCHET_EXEMPT_TRUSTED_ARITH_HELPER_KEYS: &[&str] = &[
    "helper:close_with_trusted_arith:linarith",
    "helper:close_with_trusted_arith:mathverse",
    "helper:replace_target_with_trusted_fallback:simp",
];

/// Intentional test-only trustedAy producers that should not count against
/// the proof-reconstruction ratchet.
const RATCHET_EXEMPT_TRUSTED_AY_PREFIXES: &[&str] = &[
    "crates/clean-elab/src/tactic/smt/selected_proof_accounting_tests.rs:",
    "crates/clean-elab/src/tactic/tests/trusted_ay.rs:",
    "crates/clean-elab/src/tactic/tests/trusted_ratchet.rs:",
];

/// Read the trusted arith baseline from scripts/sorry_baseline.json.
fn read_trusted_arith_baseline() -> Option<u64> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()?
        .parent()?
        .join("scripts")
        .join("sorry_baseline.json");
    let content = std::fs::read_to_string(path).ok()?;
    let value: serde_json::Value = serde_json::from_str(&content).ok()?;
    value.get("trusted_arith_baseline")?.as_u64()
}

/// Read the trusted Ay baseline from scripts/sorry_baseline.json.
fn read_trusted_ay_baseline() -> Option<u64> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()?
        .parent()?
        .join("scripts")
        .join("sorry_baseline.json");
    let content = std::fs::read_to_string(path).ok()?;
    let value: serde_json::Value = serde_json::from_str(&content).ok()?;
    value.get("trusted_ay_baseline")?.as_u64()
}

fn is_ratchet_exempt_trusted_arith_location(location: &str) -> bool {
    RATCHET_EXEMPT_TRUSTED_ARITH_PREFIXES
        .iter()
        .any(|prefix| location.starts_with(prefix))
        || RATCHET_EXEMPT_TRUSTED_ARITH_HELPER_KEYS.contains(&location)
}

fn is_helper_trusted_arith_location(location: &str) -> bool {
    location.starts_with("helper:")
}

type TrustedArithLocation = (String, u64);
type TrustedArithLocationBuckets = (Vec<TrustedArithLocation>, Vec<TrustedArithLocation>);

fn sorted_trusted_arith_locations() -> Vec<TrustedArithLocation> {
    let mut sorted: Vec<_> = arith_locations().unwrap_or_default().into_iter().collect();
    sorted.sort_by(|a, b| {
        is_helper_trusted_arith_location(&a.0)
            .cmp(&is_helper_trusted_arith_location(&b.0))
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| a.0.cmp(&b.0))
    });
    sorted
}

fn split_trusted_arith_locations(
    locations: &[TrustedArithLocation],
) -> TrustedArithLocationBuckets {
    let mut direct = Vec::new();
    let mut helper = Vec::new();

    for (location, count) in locations {
        if is_helper_trusted_arith_location(location) {
            helper.push((location.clone(), *count));
        } else {
            direct.push((location.clone(), *count));
        }
    }

    (direct, helper)
}

fn trusted_arith_location_marker(location: &str) -> &'static str {
    if is_ratchet_exempt_trusted_arith_location(location) {
        " (exempt)"
    } else {
        ""
    }
}

fn print_trusted_arith_section(header: &str, locations: &[TrustedArithLocation]) {
    if locations.is_empty() {
        return;
    }

    eprintln!("{header}:");
    for (location, count) in locations {
        eprintln!(
            "  {} x{}{}",
            location,
            count,
            trusted_arith_location_marker(location)
        );
    }
}

fn trusted_arith_ratchet_counts(locations: &[(String, u64)]) -> (u64, u64) {
    let mut tracked = 0;
    let mut exempt = 0;
    for (location, count) in locations {
        if is_ratchet_exempt_trusted_arith_location(location) {
            exempt += *count;
        } else {
            tracked += *count;
        }
    }
    (tracked, exempt)
}

fn is_ratchet_exempt_trusted_ay_location(location: &str) -> bool {
    RATCHET_EXEMPT_TRUSTED_AY_PREFIXES
        .iter()
        .any(|prefix| location.starts_with(prefix))
}

fn sorted_trusted_ay_locations() -> Vec<(String, u64)> {
    let mut sorted: Vec<_> = ay_locations().unwrap_or_default().into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    sorted
}

fn trusted_ay_ratchet_counts(locations: &[(String, u64)]) -> (u64, u64) {
    let mut tracked = 0;
    let mut exempt = 0;
    for (location, count) in locations {
        if is_ratchet_exempt_trusted_ay_location(location) {
            exempt += *count;
        } else {
            tracked += *count;
        }
    }
    (tracked, exempt)
}

/// Ratchet test: ensures trustedArith count does not exceed the recorded baseline.
///
/// Reads `scripts/sorry_baseline.json` and asserts that the current trustedArith
/// lifetime count does not exceed the baseline. If the baseline file doesn't exist
/// or doesn't contain the key, this test is skipped (passes trivially).
///
/// **Important:** Like the sorry ratchet, this test is only meaningful when run
/// as part of the full test suite (`cargo test -p clean-elab --lib`). When run
/// in isolation, the lifetime counter is 0 (no prior tactic tests produced
/// trustedArith terms), which trivially passes.
#[test]
#[serial]
fn test_trusted_arith_ratchet() {
    enable_arith_location_tracking();
    let baseline = match read_trusted_arith_baseline() {
        Some(b) => b,
        None => {
            eprintln!(
                "TRUSTED ARITH RATCHET: no baseline found, skipping ratchet check. \
                 Add trusted_arith_baseline to scripts/sorry_baseline.json to enable."
            );
            return;
        }
    };

    let total = arith_lifetime_count();
    let locations = sorted_trusted_arith_locations();
    let (current, exempt) = trusted_arith_ratchet_counts(&locations);

    eprintln!("=== TRUSTED ARITH RATCHET ===");
    eprintln!("Baseline: {}", baseline);
    eprintln!("Current:  {}", current);
    eprintln!("Total:    {}", total);
    if exempt > 0 {
        eprintln!("Excluded: {}", exempt);
    }
    assert_eq!(
        current + exempt,
        total,
        "trustedArith census mismatch: tracked + exempt = {}, lifetime = {}",
        current + exempt,
        total
    );
    let (direct_locations, helper_locations) = split_trusted_arith_locations(&locations);
    if !locations.is_empty() {
        print_trusted_arith_section("Direct runtime callers", &direct_locations);
        print_trusted_arith_section("Helper runtime callers", &helper_locations);
    }

    if current == 0 && baseline > 0 {
        eprintln!(
            "NOTE: trustedArith count is 0 with baseline {}. This test is likely \
             running in isolation. Run with full suite for meaningful ratchet.",
            baseline
        );
        eprintln!("=== END TRUSTED ARITH RATCHET ===");
        return;
    }

    assert!(
        current <= baseline,
        "TRUSTED ARITH RATCHET FAILED: trustedArith count {} exceeds baseline {}. \
         A tactic regressed from kernel proofs to trustedArith. Either fix the \
         regression or bump trusted_arith_baseline in scripts/sorry_baseline.json.",
        current,
        baseline
    );

    if current < baseline {
        eprintln!(
            "IMPROVEMENT: trustedArith count decreased by {} (from {} to {}). \
             Consider lowering the baseline to lock in this improvement.",
            baseline - current,
            baseline,
            current
        );
    }
    eprintln!("=== END TRUSTED ARITH RATCHET ===");
}

/// Ratchet test: ensures trustedAy count does not exceed the recorded baseline.
///
/// Same pattern as `test_trusted_arith_ratchet` but for Ay trusted proofs.
#[test]
#[serial]
fn test_trusted_ay_ratchet() {
    enable_ay_location_tracking();
    let baseline = match read_trusted_ay_baseline() {
        Some(b) => b,
        None => {
            eprintln!(
                "TRUSTED Ay RATCHET: no baseline found, skipping ratchet check. \
                 Add trusted_ay_baseline to scripts/sorry_baseline.json to enable."
            );
            return;
        }
    };

    let total = ay_lifetime_count();
    let locations = sorted_trusted_ay_locations();
    let (current, exempt) = trusted_ay_ratchet_counts(&locations);

    eprintln!("=== TRUSTED Ay RATCHET ===");
    eprintln!("Baseline: {}", baseline);
    eprintln!("Current:  {}", current);
    eprintln!("Total:    {}", total);
    if exempt > 0 {
        eprintln!("Excluded: {}", exempt);
    }
    assert_eq!(
        current + exempt,
        total,
        "trustedAy census mismatch: tracked + exempt = {}, lifetime = {}",
        current + exempt,
        total
    );
    if !locations.is_empty() {
        for (location, count) in &locations {
            let marker = if is_ratchet_exempt_trusted_ay_location(location) {
                " (exempt)"
            } else {
                ""
            };
            eprintln!("  {} x{}{}", location, count, marker);
        }
    }

    if current == 0 && baseline > 0 {
        eprintln!(
            "NOTE: trustedAy count is 0 with baseline {}. This test is likely \
             running in isolation. Run with full suite for meaningful ratchet.",
            baseline
        );
        eprintln!("=== END TRUSTED Ay RATCHET ===");
        return;
    }

    assert!(
        current <= baseline,
        "TRUSTED Ay RATCHET FAILED: trustedAy count {} exceeds baseline {}. \
         A tactic regressed from kernel proofs to trustedAy. Either fix the \
         regression or bump trusted_ay_baseline in scripts/sorry_baseline.json.",
        current,
        baseline
    );

    if current < baseline {
        eprintln!(
            "IMPROVEMENT: trustedAy count decreased by {} (from {} to {}). \
             Consider lowering the baseline to lock in this improvement.",
            baseline - current,
            baseline,
            current
        );
    }
    eprintln!("=== END TRUSTED Ay RATCHET ===");
}

/// Mechanism test: validates that the trusted arith lifetime counter works
/// correctly, independent of the full test suite.
#[test]
#[serial]
fn test_trusted_arith_ratchet_mechanism() {
    use crate::tactic::arith_linarith::{
        arith_proof_count, create_trusted_arith_term, reset_arith_counter,
    };
    use clean_kernel::Environment;

    let initial_lifetime = arith_lifetime_count();
    reset_arith_counter();

    let mut env = Environment::new();
    env.init_trusted_arith().unwrap();

    // Create exactly 2 trustedArith terms
    for _ in 0..2 {
        let _ = create_trusted_arith_term(&env, &clean_kernel::Expr::prop());
    }

    // Verify resettable counter
    assert_eq!(
        arith_proof_count(),
        2,
        "arith_proof_count should be 2 after 2 calls"
    );

    // Verify lifetime counter incremented by exactly 2
    let after_lifetime = arith_lifetime_count();
    assert_eq!(
        after_lifetime - initial_lifetime,
        2,
        "arith_lifetime_count should increment by exactly 2 \
         (before={}, after={})",
        initial_lifetime,
        after_lifetime
    );

    // Verify reset doesn't affect lifetime counter
    reset_arith_counter();
    assert_eq!(
        arith_proof_count(),
        0,
        "arith_proof_count should be 0 after reset"
    );
    assert_eq!(
        arith_lifetime_count(),
        after_lifetime,
        "arith_lifetime_count must not be affected by reset"
    );
}

#[test]
fn test_trusted_arith_ratchet_split_preserves_helper_tracking() {
    // Fixture helper keys (listed in RATCHET_EXEMPT_TRUSTED_ARITH_HELPER_KEYS)
    // should be exempt. Non-fixture helper keys should stay tracked.
    let locations = vec![
        (
            "crates/clean-elab/src/tactic/tests/trusted_axiom_state.rs:152".to_string(),
            2,
        ),
        // Fixture helper — exempt via RATCHET_EXEMPT_TRUSTED_ARITH_HELPER_KEYS
        ("helper:close_with_trusted_arith:linarith".to_string(), 3),
        // Fixture helper — exempt via RATCHET_EXEMPT_TRUSTED_ARITH_HELPER_KEYS
        (
            "helper:replace_target_with_trusted_fallback:simp".to_string(),
            1,
        ),
        // Non-fixture helper — NOT in the exemption list, so tracked
        ("helper:close_with_trusted_arith:ring".to_string(), 5),
    ];

    let (direct, helper) = split_trusted_arith_locations(&locations);
    assert_eq!(
        direct,
        vec![(
            "crates/clean-elab/src/tactic/tests/trusted_axiom_state.rs:152".to_string(),
            2,
        )],
        "file:line callers should stay in the direct section"
    );
    assert_eq!(
        helper.len(),
        3,
        "all helper keys should be split into the helper lane"
    );

    let (tracked, exempt) = trusted_arith_ratchet_counts(&locations);
    // tracked: ring helper (5) = 5
    // exempt: trusted_axiom_state.rs direct (2) + linarith helper (3) + simp helper (1) = 6
    assert_eq!(
        tracked, 5,
        "non-fixture helper traffic should stay on the tracked lane"
    );
    assert_eq!(
        exempt, 6,
        "direct exempt prefixes + fixture helper keys should both be exempt"
    );
}

/// Mechanism test: validates that the trusted Ay lifetime counter works
/// correctly, independent of the full test suite.
#[test]
#[serial]
fn test_trusted_ay_ratchet_mechanism() {
    use clean_kernel::sorry::{ay_proof_count, reset_ay_counter};
    use clean_kernel::{Environment, Expr};

    let initial_lifetime = ay_lifetime_count();
    reset_ay_counter();

    let mut env = Environment::new();
    env.init_trusted_ay().unwrap();

    // Create exactly 2 trustedAy terms
    for _ in 0..2 {
        let _ = clean_kernel::sorry::create_trusted_ay_term(&env, &Expr::prop());
    }

    // Verify resettable counter
    assert_eq!(
        ay_proof_count(),
        2,
        "ay_proof_count should be 2 after 2 calls"
    );

    // Verify lifetime counter incremented by exactly 2
    let after_lifetime = ay_lifetime_count();
    assert_eq!(
        after_lifetime - initial_lifetime,
        2,
        "ay_lifetime_count should increment by exactly 2 \
         (before={}, after={})",
        initial_lifetime,
        after_lifetime
    );

    // Verify reset doesn't affect lifetime counter
    reset_ay_counter();
    assert_eq!(
        ay_proof_count(),
        0,
        "ay_proof_count should be 0 after reset"
    );
    assert_eq!(
        ay_lifetime_count(),
        after_lifetime,
        "ay_lifetime_count must not be affected by reset"
    );
}
