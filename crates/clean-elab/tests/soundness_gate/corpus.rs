// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness gate corpus completeness checks.
//!
//! Fails closed when corpus files, manifest entries, or checked-in Lean 4
//! baseline cases drift apart.
//!
//! Issue: #2543

use crate::baseline::{collect_corpus_files, load_checked_in_file_baseline, load_manifest};
use crate::common::{corpus_root, manifest_path};
use std::collections::HashSet;

fn sorted_difference(left: &HashSet<String>, right: &HashSet<String>) -> Vec<String> {
    let mut diff: Vec<_> = left.difference(right).cloned().collect();
    diff.sort();
    diff
}

fn completeness_failure_message(
    missing_from_manifest: &[String],
    missing_on_disk: &[String],
    missing_from_baseline: &[String],
    stale_baseline_cases: &[String],
) -> Option<String> {
    if missing_from_manifest.is_empty()
        && missing_on_disk.is_empty()
        && missing_from_baseline.is_empty()
        && stale_baseline_cases.is_empty()
    {
        return None;
    }

    let mut message = String::from("Soundness gate corpus/manifest/baseline drift detected:\n");
    if !missing_from_manifest.is_empty() {
        message.push_str("  corpus files missing from manifest:\n");
        for path in missing_from_manifest {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !missing_on_disk.is_empty() {
        message.push_str("  manifest entries missing from disk:\n");
        for path in missing_on_disk {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !missing_from_baseline.is_empty() {
        message.push_str("  manifest entries missing from Lean 4 baseline:\n");
        for path in missing_from_baseline {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !stale_baseline_cases.is_empty() {
        message.push_str("  stale Lean 4 baseline entries missing from manifest:\n");
        for path in stale_baseline_cases {
            message.push_str(&format!("    {path}\n"));
        }
    }
    Some(message)
}

#[test]
fn soundness_gate_corpus_manifest_and_baseline_are_complete() {
    let corpus = corpus_root();
    let manifest = load_manifest(&manifest_path());
    let baseline = load_checked_in_file_baseline(&manifest);

    let manifest_paths: HashSet<_> = manifest.iter().map(|entry| entry.path.clone()).collect();
    let disk_paths: HashSet<_> = collect_corpus_files(&corpus)
        .unwrap_or_else(|e| panic!("Failed to collect soundness gate corpus files: {e:#}"))
        .into_iter()
        .collect();
    let baseline_paths = baseline.case_path_set();

    let missing_from_manifest = sorted_difference(&disk_paths, &manifest_paths);
    let missing_on_disk = sorted_difference(&manifest_paths, &disk_paths);
    let missing_from_baseline = sorted_difference(&manifest_paths, &baseline_paths);
    let stale_baseline_cases = sorted_difference(&baseline_paths, &manifest_paths);

    if let Some(message) = completeness_failure_message(
        &missing_from_manifest,
        &missing_on_disk,
        &missing_from_baseline,
        &stale_baseline_cases,
    ) {
        panic!("{message}");
    }
}
