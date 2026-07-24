// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{baseline, common};
use anyhow::{anyhow, Result};
use std::path::Path;

fn format_trust_summary(result: &common::GateRunResult) -> String {
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

fn load_accept_source(corpus: &Path, entry: &baseline::ManifestEntry) -> Result<String> {
    let file_path = corpus.join(&entry.path);
    std::fs::read_to_string(&file_path)
        .map_err(|e| anyhow!("Failed to read corpus file {}: {e}", file_path.display()))
}

fn accept_failure(
    corpus: &Path,
    baseline: &baseline::Lean4FileBaseline,
    entry: &baseline::ManifestEntry,
) -> Result<Option<(String, common::GateRunResult)>> {
    let source = load_accept_source(corpus, entry)?;
    let result = common::run_clean_file_threaded(&source);
    let baseline_verdict = baseline
        .verdict_for(&entry.path)
        .map_err(|e| anyhow!("Missing Lean 4 baseline verdict for {}: {e:#}", entry.path))?;
    if result.verdict.tag() == baseline_verdict && result.trust.fully_verified {
        Ok(None)
    } else {
        Ok(Some((entry.path.clone(), result)))
    }
}

fn append_accept_failure(msg: &mut String, path: &str, result: &common::GateRunResult) {
    match &result.verdict {
        common::GateVerdict::Accept => {
            msg.push_str(&format!(
                "  TRUSTED ACCEPT {path}\n    {}\n",
                format_trust_summary(result)
            ));
        }
        common::GateVerdict::Reject(reason) => {
            msg.push_str(&format!(
                "  REJECT {path}: {reason}\n    {}\n",
                format_trust_summary(result)
            ));
        }
    }
}

pub(crate) fn run_accept_lane() -> Result<()> {
    let (manifest, baseline) = baseline::load_gate_manifest_and_baseline();
    let corpus = common::corpus_root();

    let accept_entries: Vec<_> = manifest
        .iter()
        .filter(|entry| entry.expected == common::GateVerdictTag::Accept)
        .collect();

    if accept_entries.is_empty() {
        return Err(anyhow!(
            "Soundness gate corpus has no accept entries — manifest is empty or broken"
        ));
    }

    let mut failures = Vec::new();
    for entry in &accept_entries {
        if let Some(failure) = accept_failure(&corpus, &baseline, entry)? {
            failures.push(failure);
        }
    }

    if failures.is_empty() {
        tracing::info!(
            "Soundness gate accept: {}/{} passed",
            accept_entries.len(),
            accept_entries.len()
        );
        return Ok(());
    }

    let mut msg = format!(
        "Soundness gate ACCEPT failures: {}/{}\n",
        failures.len(),
        accept_entries.len()
    );
    for (path, result) in &failures {
        append_accept_failure(&mut msg, path, result);
    }
    Err(anyhow!(msg))
}

pub(crate) fn verify_trusted_accept_is_not_sound() -> Result<()> {
    let result = common::run_clean_file(
        r#"
theorem trusted_accept : True := by
  sorry
"#,
    );

    if !matches!(result.verdict, common::GateVerdict::Accept) {
        return Err(anyhow!(
            "trusted regression should still elaborate: {result:?}"
        ));
    }
    if result.trust.sorry_count == 0 {
        return Err(anyhow!(
            "trusted regression should increment sorry_count: {result:?}"
        ));
    }
    if result.trust.explicit_sorry_count != 1 {
        return Err(anyhow!(
            "user-written tactic sorry should count as explicit provenance: {result:?}"
        ));
    }
    if result.trust.synthetic_sorry_count != 0 {
        return Err(anyhow!(
            "user-written tactic sorry should not count as synthetic provenance: {result:?}"
        ));
    }
    if result.trust.fully_verified {
        return Err(anyhow!(
            "trusted accept must fail closed in the gate: {result:?}"
        ));
    }
    Ok(())
}

pub(crate) fn verify_parser_recovery_sorry_is_synthetic() -> Result<()> {
    let result = common::run_clean_file(
        "theorem parser_recovery : True := suffices h : True by have : True :=; True.intro",
    );

    if !matches!(result.verdict, common::GateVerdict::Accept) {
        return Err(anyhow!(
            "parser recovery regression should still elaborate: {result:?}"
        ));
    }
    if result.trust.sorry_count != 1 {
        return Err(anyhow!(
            "parser recovery regression should emit exactly one sorry: {result:?}"
        ));
    }
    if result.trust.explicit_sorry_count != 0 {
        return Err(anyhow!(
            "parser recovery should stay off the explicit sorry lane: {result:?}"
        ));
    }
    if result.trust.synthetic_sorry_count != 1 {
        return Err(anyhow!(
            "parser recovery should count as synthetic sorry: {result:?}"
        ));
    }
    if result.trust.fully_verified {
        return Err(anyhow!(
            "synthetic parser recovery must still fail the soundness gate trust check"
        ));
    }
    Ok(())
}

pub(crate) fn verify_explicit_sorry_is_not_fully_verified() -> Result<()> {
    let (term, trust) = common::explicit_sorry_probe();

    if !term.is_non_synthetic_sorry() {
        return Err(anyhow!(
            "probe should construct an explicit/non-synthetic sorry term, got: {term:?}"
        ));
    }
    if trust.sorry_count != 1 {
        return Err(anyhow!("probe should emit exactly one sorry"));
    }
    if trust.explicit_sorry_count != 1 {
        return Err(anyhow!(
            "explicit probe should increment explicit sorry accounting"
        ));
    }
    if trust.synthetic_sorry_count != 0 {
        return Err(anyhow!(
            "explicit probe should not increment synthetic sorry accounting"
        ));
    }
    if trust.fully_verified {
        return Err(anyhow!(
            "explicit sorry must fail the soundness gate trust check"
        ));
    }
    Ok(())
}

pub(crate) fn verify_synthetic_sorry_is_not_fully_verified() -> Result<()> {
    let (term, trust) = common::synthetic_sorry_probe();

    if !term.is_synthetic_sorry() {
        return Err(anyhow!(
            "probe should construct a synthetic sorryAx term, got: {term:?}"
        ));
    }
    if trust.sorry_count != 1 {
        return Err(anyhow!("probe should emit exactly one sorry"));
    }
    if trust.explicit_sorry_count != 0 {
        return Err(anyhow!(
            "synthetic probe should not increment explicit sorry accounting"
        ));
    }
    if trust.synthetic_sorry_count != 1 {
        return Err(anyhow!(
            "synthetic probe should increment synthetic sorry accounting"
        ));
    }
    if trust.fully_verified {
        return Err(anyhow!(
            "synthetic sorry must also fail the soundness gate trust check"
        ));
    }
    Ok(())
}
