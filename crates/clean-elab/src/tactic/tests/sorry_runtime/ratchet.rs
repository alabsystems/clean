// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Runtime sorry frequency ratchet (#2160 T1).
///
/// Runs all 9 workloads and asserts the total sorry count is at or below
/// `RUNTIME_SORRY_RATCHET`. When tactics improve and generate fewer sorry
/// terms, the ratchet value should be tightened downward.
///
/// On failure, prints a per-workload breakdown and location diagnostics.
#[test]
#[serial]
fn sorry_runtime_frequency_ratchet() {
    // Ratchet value — tighten downward as sorry paths are eliminated.
    // Current state (post-Phase 3):
    //   W1-W6: 0 each (arithmetic tactics with kernel-verified proofs)
    //   W7: 0 (instance resolution fails cleanly without sorry)
    //   W8: 1 (intentional sorry tactic — irreducible minimum)
    //   W9: 1 (structural sorry — irreducible minimum)
    // Total: 2 sorry. Minimum achievable: 2.
    const RUNTIME_SORRY_RATCHET: u64 = 2;

    // Reset counters and enable location tracking for diagnostics
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    // Run all workloads and collect per-workload sorry counts
    let results = vec![
        workload_linarith_basic(),
        workload_linarith_le_trans(),
        workload_linarith_scaled(),
        workload_mathverse_parity(),
        workload_mathverse_linear(),
        workload_nlinarith(),
        workload_instance_no_table(),
        workload_sorry_tactic(),
        workload_structural_sorry(),
    ];

    let total: u64 = results.iter().map(|(_, count)| count).sum();

    // Build diagnostic report
    let mut report = String::from("Runtime sorry frequency report:\n");
    for (name, count) in &results {
        let status = if *count == 0 { "OK" } else { "SORRY" };
        report.push_str(&format!("  [{status:>5}] {name}: {count} sorry\n"));
    }
    report.push_str(&format!(
        "  Total: {total} sorry (ratchet: {RUNTIME_SORRY_RATCHET})\n"
    ));
    report.push_str("\nSorry locations:\n");
    report.push_str(&format_sorry_locations());

    // Always print the report for visibility
    eprintln!("{report}");

    assert!(
        total <= RUNTIME_SORRY_RATCHET,
        "Runtime sorry ratchet FAILED: {total} sorry terms, ratchet allows {RUNTIME_SORRY_RATCHET}.\n\
         {report}\n\
         Investigate which workloads regressed and fix or update the ratchet."
    );

    // Signal when ratchet can be tightened
    if total < RUNTIME_SORRY_RATCHET {
        eprintln!(
            "INFO: Runtime sorry count ({total}) is below ratchet ({RUNTIME_SORRY_RATCHET}). \
             Consider tightening RUNTIME_SORRY_RATCHET in sorry_runtime/ratchet.rs."
        );
    }
}
