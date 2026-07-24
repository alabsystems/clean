// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness gate — accept lane.
//!
//! Verifies that clean accepts all corpus files under `tests/soundness_gate/accept/`
//! without relying on trusted axioms or structural kernel-check fallback.
//! These files are known to be valid Lean 4 and must also be fully verified by clean.
//!
//! Issue: #2134

use crate::baseline::{load_gate_manifest_and_baseline, Lean4FileBaseline, ManifestEntry};
use crate::common::{
    corpus_root, explicit_sorry_probe, run_clean_file, run_clean_file_threaded,
    synthetic_sorry_probe, GateRunResult, GateVerdict, GateVerdictTag,
};
use serial_test::serial;
use std::path::Path;

fn format_trust_summary(result: &GateRunResult) -> String {
    format!(
        "sorry={} explicit_sorry={} synthetic_sorry={} ay={} arith={} kernel_failures={}",
        result.trust.sorry_count,
        result.trust.explicit_sorry_count,
        result.trust.synthetic_sorry_count,
        result.trust.ay_count,
        result.trust.arith_count,
        result.trust.kernel_check_failures
    )
}

fn load_accept_source(corpus: &Path, entry: &ManifestEntry) -> String {
    let file_path = corpus.join(&entry.path);
    std::fs::read_to_string(&file_path)
        .unwrap_or_else(|e| panic!("Failed to read corpus file {}: {e}", file_path.display()))
}

fn accept_failure(
    corpus: &Path,
    baseline: &Lean4FileBaseline,
    entry: &ManifestEntry,
) -> Option<(String, GateRunResult)> {
    let source = load_accept_source(corpus, entry);
    let result = run_clean_file_threaded(&source);
    let baseline_verdict = baseline
        .verdict_for(&entry.path)
        .unwrap_or_else(|e| panic!("Missing Lean 4 baseline verdict for {}: {e:#}", entry.path));
    if result.verdict.tag() == baseline_verdict && result.trust.fully_verified {
        None
    } else {
        Some((entry.path.clone(), result))
    }
}

fn append_accept_failure(msg: &mut String, path: &str, result: &GateRunResult) {
    match &result.verdict {
        GateVerdict::Accept => {
            msg.push_str(&format!(
                "  TRUSTED ACCEPT {path}\n    {}\n",
                format_trust_summary(result)
            ));
        }
        GateVerdict::Reject(reason) => {
            msg.push_str(&format!(
                "  REJECT {path}: {reason}\n    {}\n",
                format_trust_summary(result)
            ));
        }
    }
}

/// Run all accept-lane corpus files through clean and assert trust-free acceptance.
#[test]
fn soundness_gate_accept() {
    let (manifest, baseline) = load_gate_manifest_and_baseline();
    let corpus = corpus_root();

    let accept_entries: Vec<_> = manifest
        .iter()
        .filter(|e| e.expected == GateVerdictTag::Accept)
        .collect();

    assert!(
        !accept_entries.is_empty(),
        "Soundness gate corpus has no accept entries — manifest is empty or broken"
    );

    let mut failures = Vec::new();

    for entry in &accept_entries {
        if let Some(failure) = accept_failure(&corpus, &baseline, entry) {
            failures.push(failure);
        }
    }

    if !failures.is_empty() {
        let mut msg = format!(
            "Soundness gate ACCEPT failures: {}/{}\n",
            failures.len(),
            accept_entries.len()
        );
        for (path, result) in &failures {
            append_accept_failure(&mut msg, path, result);
        }
        panic!("{msg}");
    }

    eprintln!(
        "Soundness gate accept: {}/{} passed",
        accept_entries.len(),
        accept_entries.len()
    );
}

#[test]
#[serial]
fn soundness_gate_trusted_accept_is_not_sound() {
    let result = run_clean_file(
        r#"
theorem trusted_accept : True := by
  sorry
"#,
    );

    assert!(
        matches!(result.verdict, GateVerdict::Accept),
        "trusted regression should still elaborate: {result:?}"
    );
    assert!(
        result.trust.sorry_count > 0,
        "trusted regression should increment sorry_count: {result:?}"
    );
    assert_eq!(
        result.trust.explicit_sorry_count, 1,
        "user-written tactic sorry should count as explicit provenance: {result:?}"
    );
    assert_eq!(
        result.trust.synthetic_sorry_count, 0,
        "user-written tactic sorry should not count as synthetic provenance: {result:?}"
    );
    assert!(
        !result.trust.fully_verified,
        "trusted accept must fail closed in the gate: {result:?}"
    );
}

#[test]
#[serial]
fn soundness_gate_parser_recovery_sorry_is_synthetic() {
    let result = run_clean_file(
        "theorem parser_recovery : True := suffices h : True by have : True :=; True.intro",
    );

    assert!(
        matches!(result.verdict, GateVerdict::Accept),
        "parser recovery regression should still elaborate: {result:?}"
    );
    assert_eq!(
        result.trust.sorry_count, 1,
        "parser recovery regression should emit exactly one sorry: {result:?}"
    );
    assert_eq!(
        result.trust.explicit_sorry_count, 0,
        "parser recovery should stay off the explicit sorry lane: {result:?}"
    );
    assert_eq!(
        result.trust.synthetic_sorry_count, 1,
        "parser recovery should count as synthetic sorry: {result:?}"
    );
    assert!(
        !result.trust.fully_verified,
        "synthetic parser recovery must still fail the soundness gate trust check"
    );
}

#[test]
#[serial]
fn soundness_gate_explicit_sorry_is_not_fully_verified() {
    let (term, trust) = explicit_sorry_probe();

    assert!(
        term.is_non_synthetic_sorry(),
        "probe should construct an explicit/non-synthetic sorry term, got: {term:?}"
    );
    assert_eq!(trust.sorry_count, 1, "probe should emit exactly one sorry");
    assert_eq!(
        trust.explicit_sorry_count, 1,
        "explicit probe should increment explicit sorry accounting"
    );
    assert_eq!(
        trust.synthetic_sorry_count, 0,
        "explicit probe should not increment synthetic sorry accounting"
    );
    assert!(
        !trust.fully_verified,
        "explicit sorry must fail the soundness gate trust check"
    );
}

#[test]
#[serial]
fn soundness_gate_synthetic_sorry_is_not_fully_verified() {
    let (term, trust) = synthetic_sorry_probe();

    assert!(
        term.is_synthetic_sorry(),
        "probe should construct a synthetic sorryAx term, got: {term:?}"
    );
    assert_eq!(trust.sorry_count, 1, "probe should emit exactly one sorry");
    assert_eq!(
        trust.explicit_sorry_count, 0,
        "synthetic probe should not increment explicit sorry accounting"
    );
    assert_eq!(
        trust.synthetic_sorry_count, 1,
        "synthetic probe should increment synthetic sorry accounting"
    );
    assert!(
        !trust.fully_verified,
        "synthetic sorry must also fail the soundness gate trust check"
    );
}
