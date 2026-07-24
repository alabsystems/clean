// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the clean-discovery crate.
//!
//! These tests exercise the full discovery pipeline: environment init,
//! candidate generation, kernel verification, and result collection.
//!
//! Part of #3258.

use clean_discovery::abstract_domain::AbstractDomainConfig;
use clean_discovery::complexity::VerificationComplexityConfig;
use clean_discovery::family::{CertSizeBoundConfig, TheoremFamily};
use clean_discovery::runner::{DiscoveryConfig, DiscoveryRunner};
use clean_discovery::tightness::DomainTightnessConfig;

/// Helper to build a small DiscoveryConfig for testing.
fn small_config(max_depth: u64, max_width: u64, max_c: u64) -> DiscoveryConfig {
    DiscoveryConfig {
        families: vec![TheoremFamily::CertSizeBound],
        cert_size_config: CertSizeBoundConfig {
            max_depth,
            max_width,
            max_c,
        },
        domain_tightness_config: DomainTightnessConfig::default(),
        complexity_config: VerificationComplexityConfig::default(),
        abstract_domain_config: AbstractDomainConfig::default(),
        // Use single thread for deterministic test behavior.
        num_threads: Some(1),
    }
}

#[test]
fn test_cert_size_bound_end_to_end() {
    let config = small_config(2, 2, 1);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");
    let results = runner.run().expect("discovery run should succeed");

    // With max_depth=2, max_width=2, max_c=1:
    // 4 bound functions * 1 C * 2 depths * 2 widths = 16 candidates
    assert_eq!(results.total_evaluated, 16, "should evaluate 16 candidates");
    assert_eq!(
        results.family_results.len(),
        1,
        "should have one family result"
    );

    let (_fam, ref search_result) = results.family_results[0];
    assert_eq!(
        search_result.outcomes.len(),
        16,
        "should have outcome for each candidate"
    );

    // Stats should be populated.
    assert!(
        results.total_wall_time_ns > 0,
        "wall time should be positive"
    );
    assert!(
        search_result.stats.throughput_per_sec > 0.0,
        "throughput should be positive"
    );
}

/// The honest loop end-to-end: the genuine verifier accepts ONLY candidates
/// whose proof term really proves the statement (kernel-confirmed via
/// `is_def_eq`), and rejects the hard-coded-axiom candidates that the old
/// infer-only path falsely "verified".
#[test]
fn test_honest_loop_verifies_only_genuine_candidates() {
    // 4 bound fns * C=1 * 2 depths * 2 widths = 16 candidates.
    // The only genuinely-provable shape is QuadraticWidth with C=1 (proven by
    // ibp_cert_polynomial_axiom). It is generated once per (d, w) pair = 4.
    let config = small_config(2, 2, 1);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");
    let results = runner.run().expect("discovery run should succeed");

    assert_eq!(results.total_evaluated, 16);
    assert_eq!(
        results.total_verified, 4,
        "exactly the 4 genuine QuadraticWidth/C=1 candidates should verify; \
         the hard-coded-axiom candidates of other shapes must be rejected"
    );

    let (_fam, ref search_result) = results.family_results[0];

    // Every verified candidate must have a genuine inferred type and no error;
    // every rejected candidate must carry an explanatory error. This is the
    // honest contract — no candidate is silently "verified".
    let verified: Vec<_> = search_result
        .outcomes
        .iter()
        .filter(|o| o.verified)
        .collect();
    assert_eq!(verified.len(), 4);
    for o in &verified {
        assert!(o.inferred_type.is_some());
        assert!(o.error.is_none());
    }
    for o in search_result.outcomes.iter().filter(|o| !o.verified) {
        assert!(
            o.error.is_some(),
            "rejected candidate {} must explain why",
            o.candidate_id.0
        );
    }

    // Demonstrate ONE genuinely-verified candidate end-to-end.
    let first = verified[0];
    println!(
        "GENUINELY VERIFIED candidate id={} (kernel-confirmed proof : statement)\n  proven type = {:?}",
        first.candidate_id.0,
        first.inferred_type.as_ref().unwrap()
    );
}

#[test]
fn test_discovery_runner_multiple_runs_deterministic() {
    let config = small_config(2, 2, 1);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");

    let results1 = runner.run().expect("first run should succeed");
    let results2 = runner.run().expect("second run should succeed");

    assert_eq!(
        results1.total_evaluated, results2.total_evaluated,
        "candidate count should be deterministic across runs"
    );
    assert_eq!(
        results1.total_verified, results2.total_verified,
        "verified count should be deterministic across runs"
    );

    // Verify individual outcomes match.
    let outcomes1 = &results1.family_results[0].1.outcomes;
    let outcomes2 = &results2.family_results[0].1.outcomes;
    assert_eq!(outcomes1.len(), outcomes2.len());
    for (o1, o2) in outcomes1.iter().zip(outcomes2.iter()) {
        assert_eq!(
            o1.candidate_id, o2.candidate_id,
            "candidate IDs should match"
        );
        assert_eq!(
            o1.verified, o2.verified,
            "verification results should be deterministic"
        );
    }
}

#[test]
fn test_batch_verifier_throughput() {
    // Use a larger search space to get meaningful throughput measurement.
    let config = small_config(3, 3, 2);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");

    let results = runner.run().expect("discovery run should succeed");

    // 4 bound fns * 2 C * 3 depths * 3 widths = 72 candidates
    assert_eq!(results.total_evaluated, 72, "should evaluate 72 candidates");

    let elapsed_secs = results.total_wall_time_ns as f64 / 1_000_000_000.0;
    let throughput = if elapsed_secs > 0.0 {
        results.total_evaluated as f64 / elapsed_secs
    } else {
        0.0
    };

    // Conservative floor: 100 candidates/sec. Actual throughput should be
    // orders of magnitude higher given sub-microsecond kernel operations.
    assert!(
        throughput > 100.0,
        "throughput should exceed 100 candidates/sec, got {throughput:.0}/sec"
    );
}

#[test]
fn test_all_candidates_have_outcomes() {
    let config = small_config(2, 2, 2);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");
    let results = runner.run().expect("discovery run should succeed");

    for (_fam, ref search_result) in &results.family_results {
        for outcome in &search_result.outcomes {
            // Every candidate must have a definite result: either verified or
            // has an error explaining why not.
            if outcome.verified {
                assert!(
                    outcome.inferred_type.is_some(),
                    "verified candidate {} should have an inferred type",
                    outcome.candidate_id.0
                );
                assert!(
                    outcome.error.is_none(),
                    "verified candidate {} should not have an error",
                    outcome.candidate_id.0
                );
            } else {
                assert!(
                    outcome.error.is_some(),
                    "failed candidate {} should have an error message",
                    outcome.candidate_id.0
                );
            }
        }
    }
}

#[test]
fn test_search_result_stats_consistent() {
    let config = small_config(2, 2, 2);
    let runner = DiscoveryRunner::new(config).expect("runner creation should succeed");
    let results = runner.run().expect("discovery run should succeed");

    // Global stats consistency.
    assert_eq!(
        results.total_evaluated,
        results.total_verified
            + results
                .family_results
                .iter()
                .map(|(_, sr)| sr.stats.total_failed)
                .sum::<u64>(),
        "total_evaluated should equal total_verified + total_failed"
    );

    // Per-family stats consistency.
    for (_fam, ref search_result) in &results.family_results {
        let stats = &search_result.stats;
        assert_eq!(
            stats.total_evaluated,
            stats.total_verified + stats.total_failed,
            "per-family: total_evaluated should equal verified + failed"
        );
        assert_eq!(
            stats.total_evaluated,
            search_result.outcomes.len() as u64,
            "total_evaluated should match outcomes length"
        );

        let counted_verified = search_result.outcomes.iter().filter(|o| o.verified).count() as u64;
        assert_eq!(
            stats.total_verified, counted_verified,
            "total_verified stat should match count of verified outcomes"
        );
    }
}
