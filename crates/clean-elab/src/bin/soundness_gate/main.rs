// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Normal-binary entrypoint for the kernel soundness gate.
//!
//! This reuses the existing gate helpers without running through the
//! integration-test target's broader dev-dependency graph.

use anyhow::Result;

mod accept;
mod ledger;
mod reject;

#[path = "../../../tests/soundness_gate/common.rs"]
mod common;

#[path = "../../../tests/soundness_gate/baseline.rs"]
mod baseline;

fn init_tracing() {
    let _ = tracing_subscriber::fmt()
        .with_target(false)
        .without_time()
        .try_init();
}

fn main() -> Result<()> {
    init_tracing();

    tracing::info!("soundness_gate: verifying corpus/baseline consistency");
    ledger::verify_corpus_manifest_and_baseline_complete()?;

    tracing::info!("soundness_gate: verifying regression ledger");
    ledger::verify_named_test_matcher_self_checks()?;
    ledger::verify_ledger_test_sources_cover_named_tests()?;
    ledger::verify_ledger_corpus_files_exist()?;
    ledger::verify_ledger_manifest_coverage()?;

    tracing::info!("soundness_gate: running accept lane");
    accept::run_accept_lane()?;

    tracing::info!("soundness_gate: running reject lane");
    reject::run_reject_lane()?;
    reject::verify_reject_reasons_are_type_errors()?;

    tracing::info!("soundness_gate: running trust regressions");
    accept::verify_trusted_accept_is_not_sound()?;
    accept::verify_parser_recovery_sorry_is_synthetic()?;
    accept::verify_explicit_sorry_is_not_fully_verified()?;
    accept::verify_synthetic_sorry_is_not_fully_verified()?;

    tracing::info!("soundness_gate: PASS");
    Ok(())
}
