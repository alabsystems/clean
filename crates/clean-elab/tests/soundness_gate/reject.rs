// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness gate — reject lane.
//!
//! Verifies that clean rejects all corpus files under `tests/soundness_gate/reject/`.
//! These files are known to be invalid Lean 4 and must also be rejected by clean.
//! A reject-lane failure (clean accepts something Lean 4 rejects) is a soundness bug.
//!
//! Issue: #2134

use crate::baseline::load_gate_manifest_and_baseline;
use crate::common::{corpus_root, run_clean_file_threaded, GateVerdict, GateVerdictTag};

/// Run all reject-lane corpus files through clean and assert rejection.
#[test]
fn soundness_gate_reject() {
    let (manifest, baseline) = load_gate_manifest_and_baseline();
    let corpus = corpus_root();

    let reject_entries: Vec<_> = manifest
        .iter()
        .filter(|e| e.expected == GateVerdictTag::Reject)
        .collect();

    assert!(
        !reject_entries.is_empty(),
        "Soundness gate corpus has no reject entries — manifest is empty or broken"
    );

    let mut mismatches = Vec::new();

    for entry in &reject_entries {
        let file_path = corpus.join(&entry.path);
        let source = std::fs::read_to_string(&file_path)
            .unwrap_or_else(|e| panic!("Failed to read corpus file {}: {e}", file_path.display()));

        let result = run_clean_file_threaded(&source);
        let baseline_verdict = baseline.verdict_for(&entry.path).unwrap_or_else(|e| {
            panic!("Missing Lean 4 baseline verdict for {}: {e:#}", entry.path)
        });
        if result.verdict.tag() != baseline_verdict {
            mismatches.push((entry.path.clone(), result.verdict.clone(), baseline_verdict));
        }
    }

    if !mismatches.is_empty() {
        let mut msg = format!(
            "SOUNDNESS BUG: clean diverged from the Lean 4 baseline on {}/{} reject-lane files:\n",
            mismatches.len(),
            reject_entries.len()
        );
        for (path, clean_verdict, baseline_verdict) in &mismatches {
            msg.push_str(&format!(
                "  {path}: clean={}, baseline={baseline_verdict}\n",
                clean_verdict.tag()
            ));
        }
        panic!("{msg}");
    }

    eprintln!(
        "Soundness gate reject: {}/{} correctly rejected",
        reject_entries.len(),
        reject_entries.len()
    );
}

/// Verify that reject-lane rejections are *type/elaboration* errors, not parse
/// failures. A file that fails to parse does not exercise the kernel type
/// checker at all and would give false confidence in soundness coverage.
///
/// Issue: #2134
#[test]
fn reject_reasons_are_type_errors() {
    let (manifest, _) = load_gate_manifest_and_baseline();
    let corpus = corpus_root();

    let reject_entries: Vec<_> = manifest
        .iter()
        .filter(|e| e.expected == GateVerdictTag::Reject)
        .collect();

    let mut parse_failures = Vec::new();

    for entry in &reject_entries {
        let file_path = corpus.join(&entry.path);
        let source = std::fs::read_to_string(&file_path)
            .unwrap_or_else(|e| panic!("Failed to read corpus file {}: {e}", file_path.display()));

        let result = run_clean_file_threaded(&source);
        match &result.verdict {
            GateVerdict::Reject(reason) => {
                eprintln!("  {}: {reason}", entry.path);
                if reason.starts_with("parse error:") || reason.starts_with("thread panic") {
                    parse_failures.push((entry.path.clone(), reason.clone()));
                }
                // "elab error:" is the expected prefix for genuine type errors.
            }
            GateVerdict::Accept => {
                // soundness_gate_reject catches this case; skip here.
            }
        }
    }

    if !parse_failures.is_empty() {
        let mut msg = format!(
            "Reject corpus has {} files rejected for WRONG reason (parse/panic, not type error):\n",
            parse_failures.len()
        );
        for (path, reason) in &parse_failures {
            msg.push_str(&format!("  {path}: {reason}\n"));
        }
        msg.push_str(
            "These files do not exercise kernel type checking and give false soundness confidence.",
        );
        panic!("{msg}");
    }

    eprintln!(
        "Reject reasons verified: all {}/{} are elab/type errors (not parse failures)",
        reject_entries.len(),
        reject_entries.len()
    );
}
