// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{baseline, common};
use anyhow::{anyhow, Result};
use std::collections::HashSet;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GateMode {
    ExpressionParity,
    FileAccept,
    FileReject,
}

struct RegressionEntry {
    issue: u32,
    test_binary: &'static str,
    test_name: &'static str,
    test_source: &'static str,
    mode: GateMode,
    corpus_hint: &'static str,
}

fn ledger() -> Vec<RegressionEntry> {
    vec![
        RegressionEntry {
            issue: 1485,
            test_binary: "lean4_parity",
            test_name: "lean4_parity_check",
            test_source: "crates/clean-kernel/tests/lean4_parity.rs",
            mode: GateMode::ExpressionParity,
            corpus_hint: "tests/differential/expressions.txt",
        },
        RegressionEntry {
            issue: 2134,
            test_binary: "soundness_gate",
            test_name: "soundness_gate_accept",
            test_source: "crates/clean-elab/tests/soundness_gate/accept.rs",
            mode: GateMode::FileAccept,
            corpus_hint: "tests/soundness_gate/accept/basic_identity_const.lean",
        },
        RegressionEntry {
            issue: 2512,
            test_binary: "soundness_gate",
            test_name: "soundness_gate_accept",
            test_source: "crates/clean-elab/tests/soundness_gate/accept.rs",
            mode: GateMode::FileAccept,
            corpus_hint: "tests/soundness_gate/accept/basic_identity_const.lean",
        },
        RegressionEntry {
            issue: 2134,
            test_binary: "soundness_gate",
            test_name: "soundness_gate_reject",
            test_source: "crates/clean-elab/tests/soundness_gate/reject.rs",
            mode: GateMode::FileReject,
            corpus_hint: "tests/soundness_gate/reject/ill_typed_app.lean",
        },
    ]
}

fn sorted_difference(left: &HashSet<String>, right: &HashSet<String>) -> Vec<String> {
    let mut diff: Vec<_> = left.difference(right).cloned().collect();
    diff.sort();
    diff
}

pub(crate) fn verify_corpus_manifest_and_baseline_complete() -> Result<()> {
    let corpus = common::corpus_root();
    let manifest = baseline::load_manifest(&common::manifest_path());
    let baseline = baseline::load_checked_in_file_baseline(&manifest);

    let manifest_paths: HashSet<_> = manifest.iter().map(|entry| entry.path.clone()).collect();
    let disk_paths: HashSet<_> = baseline::collect_corpus_files(&corpus)?
        .into_iter()
        .collect();
    let baseline_paths = baseline.case_path_set();

    let missing_from_manifest = sorted_difference(&disk_paths, &manifest_paths);
    let missing_on_disk = sorted_difference(&manifest_paths, &disk_paths);
    let missing_from_baseline = sorted_difference(&manifest_paths, &baseline_paths);
    let stale_baseline_cases = sorted_difference(&baseline_paths, &manifest_paths);

    if missing_from_manifest.is_empty()
        && missing_on_disk.is_empty()
        && missing_from_baseline.is_empty()
        && stale_baseline_cases.is_empty()
    {
        return Ok(());
    }

    let mut message = String::from("Soundness gate corpus/manifest/baseline drift detected:\n");
    if !missing_from_manifest.is_empty() {
        message.push_str("  corpus files missing from manifest:\n");
        for path in &missing_from_manifest {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !missing_on_disk.is_empty() {
        message.push_str("  manifest entries missing from disk:\n");
        for path in &missing_on_disk {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !missing_from_baseline.is_empty() {
        message.push_str("  manifest entries missing from Lean 4 baseline:\n");
        for path in &missing_from_baseline {
            message.push_str(&format!("    {path}\n"));
        }
    }
    if !stale_baseline_cases.is_empty() {
        message.push_str("  stale Lean 4 baseline entries missing from manifest:\n");
        for path in &stale_baseline_cases {
            message.push_str(&format!("    {path}\n"));
        }
    }
    Err(anyhow!(message))
}

fn source_declares_named_test(source: &str, test_name: &str) -> bool {
    let fn_suffix = format!("{test_name}(");
    source.lines().any(|line| {
        let trimmed = line.trim_start();
        let Some(rest) = trimmed
            .strip_prefix("fn ")
            .or_else(|| trimmed.strip_prefix("pub fn "))
            .or_else(|| trimmed.strip_prefix("pub(crate) fn "))
            .or_else(|| trimmed.strip_prefix("async fn "))
            .or_else(|| trimmed.strip_prefix("pub async fn "))
            .or_else(|| trimmed.strip_prefix("pub(crate) async fn "))
        else {
            return false;
        };
        rest.starts_with(&fn_suffix)
    })
}

pub(crate) fn verify_named_test_matcher_self_checks() -> Result<()> {
    let fake = r#"
// fn soundness_gate_accept(
let fake = "fn soundness_gate_accept(";
"#;
    if source_declares_named_test(fake, "soundness_gate_accept") {
        return Err(anyhow!(
            "comments or string literals must not satisfy ledger test coverage"
        ));
    }

    let real = r#"
#[test]
pub(crate) async fn soundness_gate_accept() {}
"#;
    if !source_declares_named_test(real, "soundness_gate_accept") {
        return Err(anyhow!(
            "real function declarations should satisfy ledger test coverage"
        ));
    }

    Ok(())
}

fn repo_root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

pub(crate) fn verify_ledger_test_sources_cover_named_tests() -> Result<()> {
    let repo_root = repo_root();
    let mut missing_sources = Vec::new();
    let mut missing_tests = Vec::new();

    for entry in ledger() {
        let full_path = repo_root.join(entry.test_source);
        let source = match std::fs::read_to_string(&full_path) {
            Ok(source) => source,
            Err(_) => {
                missing_sources.push((entry.issue, entry.test_binary, entry.test_source));
                continue;
            }
        };

        if !source_declares_named_test(&source, entry.test_name) {
            missing_tests.push((
                entry.issue,
                entry.test_binary,
                entry.test_name,
                entry.test_source,
            ));
        }
    }

    if missing_sources.is_empty() && missing_tests.is_empty() {
        return Ok(());
    }

    let mut msg = String::from("Regression ledger test references are stale:\n");
    for (issue, test_binary, test_source) in &missing_sources {
        msg.push_str(&format!(
            "  #{issue}: missing source for {test_binary} at {test_source}\n"
        ));
    }
    for (issue, test_binary, test_name, test_source) in &missing_tests {
        msg.push_str(&format!(
            "  #{issue}: missing fn {test_name} in {test_binary} source {test_source}\n"
        ));
    }
    Err(anyhow!(msg))
}

pub(crate) fn verify_ledger_corpus_files_exist() -> Result<()> {
    let repo_root = repo_root();
    let entries = ledger();
    let mut missing = Vec::new();

    for entry in &entries {
        let full_path = repo_root.join(entry.corpus_hint);
        if !full_path.exists() {
            missing.push((entry.issue, entry.corpus_hint));
        }
    }

    if missing.is_empty() {
        tracing::info!(
            "Regression ledger: all {}/{} corpus files present",
            entries.len(),
            entries.len()
        );
        return Ok(());
    }

    let mut msg = format!(
        "Regression ledger: {}/{} corpus files missing:\n",
        missing.len(),
        entries.len()
    );
    for (issue, path) in &missing {
        msg.push_str(&format!("  #{issue}: {path}\n"));
    }
    Err(anyhow!(msg))
}

pub(crate) fn verify_ledger_manifest_coverage() -> Result<()> {
    let manifest = baseline::load_manifest(&common::manifest_path());
    let manifest_paths: HashSet<String> = manifest
        .iter()
        .map(|entry| format!("tests/soundness_gate/{}", entry.path))
        .collect();

    let mut uncovered = Vec::new();
    for entry in ledger() {
        match entry.mode {
            GateMode::FileAccept | GateMode::FileReject => {
                if !manifest_paths.contains(entry.corpus_hint) {
                    uncovered.push((entry.issue, entry.corpus_hint));
                }
            }
            GateMode::ExpressionParity => {}
        }
    }

    if uncovered.is_empty() {
        return Ok(());
    }

    let mut msg = format!(
        "Regression ledger: {} entries not covered by manifest:\n",
        uncovered.len()
    );
    for (issue, path) in &uncovered {
        msg.push_str(&format!("  #{issue}: {path}\n"));
    }
    Err(anyhow!(msg))
}
