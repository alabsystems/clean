// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated measurement sweep for the full current Phase 1 manifest.
//!
//! Verification command:
//! ```text
//! cargo test -p clean-elab --test phase1_full_corpus -- --nocapture lean4_phase1_full_corpus_measurement
//! ```

#[path = "integration/phase1_corpus_common.rs"]
mod phase1_corpus_common;

use phase1_corpus_common::{
    elaborate_manifest_entry, read_manifest, DeclStatus, ManifestEntry, Phase1ElabMeasurement,
};
use std::path::Path;

struct FileMeasurement {
    filename: String,
    label: &'static str,
    succeeded: usize,
    total: usize,
    detail: Option<String>,
}

struct EntryMeasurement {
    file: FileMeasurement,
    fully_elaborated: bool,
    decls_elaborated: usize,
    decls_total: usize,
}

fn failed_file_measurement(filename: &str, detail: String) -> EntryMeasurement {
    EntryMeasurement {
        file: FileMeasurement {
            filename: filename.to_string(),
            label: "FAIL",
            succeeded: 0,
            total: 0,
            detail: Some(detail),
        },
        fully_elaborated: false,
        decls_elaborated: 0,
        decls_total: 0,
    }
}

fn classify_elab_outcome(measurement: &Phase1ElabMeasurement) -> &'static str {
    if measurement.succeeded == measurement.total {
        "PASS"
    } else if measurement
        .outcomes
        .iter()
        .any(|outcome| outcome.status == DeclStatus::Timeout)
    {
        "TIME"
    } else if measurement.succeeded == 0 {
        "FAIL"
    } else {
        "PART"
    }
}

fn measure_manifest_entry(entry: &ManifestEntry, corpus_dir: &Path) -> EntryMeasurement {
    let measurement = match elaborate_manifest_entry(entry, corpus_dir) {
        Ok(measurement) => measurement,
        Err(msg) => return failed_file_measurement(&entry.filename, msg),
    };

    let label = classify_elab_outcome(&measurement);

    EntryMeasurement {
        file: FileMeasurement {
            filename: entry.filename.clone(),
            label,
            succeeded: measurement.succeeded,
            total: measurement.total,
            detail: measurement.first_error,
        },
        fully_elaborated: label == "PASS",
        decls_elaborated: measurement.succeeded,
        decls_total: measurement.total,
    }
}

fn print_measurement_summary(
    manifest_len: usize,
    files_fully_elaborated: usize,
    decls_elaborated: usize,
    decls_total: usize,
    measurements: &[FileMeasurement],
) {
    println!("=== Phase 1 Full-Corpus Measurement ===");
    println!("Manifest: {} entries", manifest_len);
    println!(
        "Files fully elaborated: {}/{}",
        files_fully_elaborated, manifest_len
    );
    println!(
        "Declarations elaborated: {}/{}",
        decls_elaborated, decls_total
    );
    println!();
    println!("Per-file outcomes:");

    for measurement in measurements {
        match measurement.label {
            "PASS" => println!(
                "  PASS  {} ({}/{} decls)",
                measurement.filename, measurement.succeeded, measurement.total
            ),
            "PART" => println!(
                "  PART  {} ({}/{} decls) — {}",
                measurement.filename,
                measurement.succeeded,
                measurement.total,
                measurement.detail.as_deref().unwrap_or("")
            ),
            "TIME" => println!(
                "  TIME  {} ({}/{} decls) — {}",
                measurement.filename,
                measurement.succeeded,
                measurement.total,
                measurement.detail.as_deref().unwrap_or("")
            ),
            _ => {
                if measurement.total == 0 {
                    println!(
                        "  FAIL  {} — {}",
                        measurement.filename,
                        measurement.detail.as_deref().unwrap_or("")
                    );
                } else {
                    println!(
                        "  FAIL  {} ({}/{} decls) — {}",
                        measurement.filename,
                        measurement.succeeded,
                        measurement.total,
                        measurement.detail.as_deref().unwrap_or("")
                    );
                }
            }
        }
    }
}

/// Dedicated Phase 1 full-corpus elaboration measurement lane.
///
/// Iterates all 80 manifest entries, attempts elaboration for each with
/// timeout, and reports file-level + declaration-level results.
///
/// Verification command:
/// ```text
/// cargo test -p clean-elab --test phase1_full_corpus -- --nocapture lean4_phase1_full_corpus_measurement
/// ```
#[test]
fn lean4_phase1_full_corpus_measurement() {
    // Full-corpus elaboration of all 80 manifest entries routinely takes
    // well over 60 seconds and gets SIGKILL'd under the default test
    // runner / system limits. Gate behind `CLEAN_PHASE1_FULL_CORPUS=1`
    // so the test passes quickly in routine CI / dev runs while the
    // measurement lane remains opt-in for the ad-hoc capacity checks
    // this test was designed for. Run with
    // `CLEAN_PHASE1_FULL_CORPUS=1 cargo test --release -p clean-elab \
    //  --test phase1_full_corpus -- --nocapture` (release+--nocapture
    // recommended for the real measurement).
    if std::env::var_os("CLEAN_PHASE1_FULL_CORPUS").is_none() {
        eprintln!(
            "TRACE: lean4_phase1_full_corpus_measurement skipped — set \
             CLEAN_PHASE1_FULL_CORPUS=1 to run the full 80-entry sweep"
        );
        return;
    }

    let manifest_path = Path::new("../../tests/lean4_compat/phase1_gate_manifest.txt");
    let corpus_dir = Path::new("../../tests/lean4_compat/lean4_tests");

    assert!(manifest_path.exists(), "Phase 1 gate manifest not found");
    assert!(corpus_dir.exists(), "Lean 4 test corpus not found");

    let entries = read_manifest(manifest_path);
    assert_eq!(
        entries.len(),
        80,
        "Phase 1 manifest drift: expected 80 entries for the full-corpus measurement"
    );

    let mut files_fully_elaborated = 0;
    let mut decls_elaborated = 0;
    let mut decls_total = 0;
    let mut measurements = Vec::with_capacity(entries.len());

    for entry in &entries {
        let measurement = measure_manifest_entry(entry, corpus_dir);
        files_fully_elaborated += usize::from(measurement.fully_elaborated);
        decls_elaborated += measurement.decls_elaborated;
        decls_total += measurement.decls_total;
        measurements.push(measurement.file);
    }

    print_measurement_summary(
        entries.len(),
        files_fully_elaborated,
        decls_elaborated,
        decls_total,
        &measurements,
    );
}
