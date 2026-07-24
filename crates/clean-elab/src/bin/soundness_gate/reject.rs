// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{baseline, common};
use anyhow::{anyhow, Result};

pub(crate) fn run_reject_lane() -> Result<()> {
    let (manifest, baseline) = baseline::load_gate_manifest_and_baseline();
    let corpus = common::corpus_root();

    let reject_entries: Vec<_> = manifest
        .iter()
        .filter(|entry| entry.expected == common::GateVerdictTag::Reject)
        .collect();

    if reject_entries.is_empty() {
        return Err(anyhow!(
            "Soundness gate corpus has no reject entries — manifest is empty or broken"
        ));
    }

    let mut mismatches = Vec::new();
    for entry in &reject_entries {
        let file_path = corpus.join(&entry.path);
        let source = std::fs::read_to_string(&file_path)
            .map_err(|e| anyhow!("Failed to read corpus file {}: {e}", file_path.display()))?;
        let result = common::run_clean_file_threaded(&source);
        let baseline_verdict = baseline
            .verdict_for(&entry.path)
            .map_err(|e| anyhow!("Missing Lean 4 baseline verdict for {}: {e:#}", entry.path))?;
        if result.verdict.tag() != baseline_verdict {
            mismatches.push((entry.path.clone(), result.verdict.clone(), baseline_verdict));
        }
    }

    if mismatches.is_empty() {
        tracing::info!(
            "Soundness gate reject: {}/{} correctly rejected",
            reject_entries.len(),
            reject_entries.len()
        );
        return Ok(());
    }

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
    Err(anyhow!(msg))
}

pub(crate) fn verify_reject_reasons_are_type_errors() -> Result<()> {
    let (manifest, _) = baseline::load_gate_manifest_and_baseline();
    let corpus = common::corpus_root();

    let reject_entries: Vec<_> = manifest
        .iter()
        .filter(|entry| entry.expected == common::GateVerdictTag::Reject)
        .collect();

    let mut parse_failures = Vec::new();
    for entry in &reject_entries {
        let file_path = corpus.join(&entry.path);
        let source = std::fs::read_to_string(&file_path)
            .map_err(|e| anyhow!("Failed to read corpus file {}: {e}", file_path.display()))?;
        let result = common::run_clean_file_threaded(&source);
        match &result.verdict {
            common::GateVerdict::Reject(reason) => {
                tracing::debug!("{}: {reason}", entry.path);
                if reason.starts_with("parse error:") || reason.starts_with("thread panic") {
                    parse_failures.push((entry.path.clone(), reason.clone()));
                }
            }
            common::GateVerdict::Accept => {}
        }
    }

    if parse_failures.is_empty() {
        tracing::info!(
            "Reject reasons verified: all {}/{} are elab/type errors (not parse failures)",
            reject_entries.len(),
            reject_entries.len()
        );
        return Ok(());
    }

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
    Err(anyhow!(msg))
}
