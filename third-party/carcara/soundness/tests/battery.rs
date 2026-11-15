// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A bounded run of the full battery: every seed from Carcara's rule tests, a few mutants of each,
//! and every systematic generator. It must find no accepted step with a counterexample. The full
//! sweep (`carcara-soundness --mutants 20000`) is documented in third-party/carcara/DOWNSTREAM.md.

use carcara_soundness::run::{render, run_battery, BatteryConfig};
use carcara_soundness::zero_extend;
use std::path::PathBuf;

#[test]
fn no_accepted_step_has_a_counterexample() {
    let tests = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../carcara/tests/rules");
    let cfg = BatteryConfig {
        mutants_per_seed: 40,
        threads: 4,
        worker_exe: Some(PathBuf::from(env!("CARGO_BIN_EXE_carcara-soundness"))),
        ..BatteryConfig::default()
    };
    let report = run_battery(&tests, &cfg);
    let unsound: u64 = report.rules.values().map(|s| s.counterexamples).sum();
    assert!(
        report.seeds > 1000,
        "seed harvesting broke: {} seeds",
        report.seeds
    );
    assert!(
        report.rules.values().map(|s| s.exercised).sum::<u64>() > 10_000,
        "the battery exercised too few steps to mean anything"
    );
    assert!(
        report.seed_expectation_mismatches.is_empty(),
        "the checker disagrees with Carcara's own rule tests:\n{}",
        render(&report)
    );
    assert_eq!(unsound, 0, "unsound acceptances:\n{}", render(&report));
}

/// The `parser:zero_extend` audit on its own (`src/zero_extend.rs`): every reading of
/// `((_ zero_extend k) d)` under Clean's Alethe dialect is its definition, and every closed
/// reading was judged by the evaluator. The bounded run above includes it among the generators.
#[test]
fn zero_extend_is_parsed_as_its_definition() {
    let stats = zero_extend::audit(5);
    assert!(stats.accepted >= 400, "{} readings audited", stats.accepted);
    assert_eq!(stats.counterexamples, 0, "{:?}", stats.examples);
    assert_eq!(
        stats.exercised, stats.accepted,
        "a reading the evaluator could not judge"
    );
}
