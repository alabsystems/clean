// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed regression ledger for the kernel soundness gate.
//!
//! Each `RegressionEntry` ties a closed soundness issue to a specific gate test
//! and corpus file. The ledger tests verify that all referenced artifacts exist,
//! preventing silent rot when tests are renamed, source files move, or corpus
//! files are removed.
//!
//! Mirrors the ay soundness gate ledger pattern.
//!
//! Issue: #2134

use std::path::Path;

/// Which gate lane a regression entry belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GateMode {
    /// Expression-level parity (clean-kernel lean4_parity test).
    ExpressionParity,
    /// File-level accept gate (clean-elab soundness_gate accept lane, trust-free).
    FileAccept,
    /// File-level reject gate (clean-elab soundness_gate reject lane).
    FileReject,
}

/// A ledger entry linking a soundness issue to a gate test.
pub(crate) struct RegressionEntry {
    /// GitHub issue number that reported or fixed the soundness problem.
    pub(crate) issue: u32,
    /// Test binary that covers this regression.
    pub(crate) test_binary: &'static str,
    /// Test function name within the binary.
    pub(crate) test_name: &'static str,
    /// Rust source file declaring `test_name`, relative to the repo root.
    pub(crate) test_source: &'static str,
    /// Which gate lane.
    pub(crate) mode: GateMode,
    /// Corpus file path (relative to repo root) or expression hint.
    pub(crate) corpus_hint: &'static str,
}

/// The regression ledger. Append new entries when closing soundness issues.
pub(crate) fn ledger() -> Vec<RegressionEntry> {
    vec![
        // Seed entry: expression-level parity lane (existing infrastructure)
        RegressionEntry {
            issue: 1485,
            test_binary: "lean4_parity",
            test_name: "lean4_parity_check",
            test_source: "crates/clean-kernel/tests/lean4_parity.rs",
            mode: GateMode::ExpressionParity,
            corpus_hint: "tests/differential/expressions.txt",
        },
        // Seed entry: file-level accept lane (accept + fully_verified)
        RegressionEntry {
            issue: 2134,
            test_binary: "soundness_gate",
            test_name: "soundness_gate_accept",
            test_source: "crates/clean-elab/tests/soundness_gate/accept.rs",
            mode: GateMode::FileAccept,
            corpus_hint: "tests/soundness_gate/accept/basic_identity_const.lean",
        },
        // Trust-aware accept regression: accepted files must remain fully verified.
        RegressionEntry {
            issue: 2512,
            test_binary: "soundness_gate",
            test_name: "soundness_gate_accept",
            test_source: "crates/clean-elab/tests/soundness_gate/accept.rs",
            mode: GateMode::FileAccept,
            corpus_hint: "tests/soundness_gate/accept/basic_identity_const.lean",
        },
        // Seed entry: file-level reject lane
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

/// Verify that every ledger entry's named test still exists in its source file.
#[test]
fn ledger_test_sources_cover_named_tests() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let entries = ledger();
    let mut missing_sources = Vec::new();
    let mut missing_tests = Vec::new();

    for entry in &entries {
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
        return;
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
    panic!("{msg}");
}

#[test]
fn named_test_matcher_requires_a_real_declaration() {
    let source = r#"
// fn soundness_gate_accept(
let fake = "fn soundness_gate_accept(";
"#;

    assert!(
        !source_declares_named_test(source, "soundness_gate_accept"),
        "comments or string literals must not satisfy ledger test coverage"
    );
}

#[test]
fn named_test_matcher_accepts_decl_lines() {
    let source = r#"
#[test]
pub(crate) async fn soundness_gate_accept() {}
"#;

    assert!(
        source_declares_named_test(source, "soundness_gate_accept"),
        "real function declarations should satisfy ledger test coverage"
    );
}

/// Verify that all corpus files referenced by ledger entries exist on disk.
#[test]
fn ledger_corpus_files_exist() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let entries = ledger();
    let mut missing = Vec::new();

    for entry in &entries {
        let full_path = repo_root.join(entry.corpus_hint);
        if !full_path.exists() {
            missing.push((entry.issue, entry.corpus_hint));
        }
    }

    if !missing.is_empty() {
        let mut msg = format!(
            "Regression ledger: {}/{} corpus files missing:\n",
            missing.len(),
            entries.len()
        );
        for (issue, path) in &missing {
            msg.push_str(&format!("  #{issue}: {path}\n"));
        }
        panic!("{msg}");
    }

    eprintln!(
        "Regression ledger: all {}/{} corpus files present",
        entries.len(),
        entries.len()
    );
}

/// Verify that the manifest covers every file-level ledger entry.
#[test]
fn ledger_manifest_coverage() {
    let manifest = crate::baseline::load_manifest(&crate::common::manifest_path());
    let entries = ledger();

    let manifest_paths: std::collections::HashSet<String> = manifest
        .iter()
        .map(|m| format!("tests/soundness_gate/{}", m.path))
        .collect();

    let mut uncovered = Vec::new();

    for entry in &entries {
        match entry.mode {
            GateMode::FileAccept | GateMode::FileReject => {
                if !manifest_paths.contains(entry.corpus_hint) {
                    uncovered.push((entry.issue, entry.corpus_hint));
                }
            }
            GateMode::ExpressionParity => {
                // Expression parity uses a different corpus — skip manifest check.
            }
        }
    }

    if !uncovered.is_empty() {
        let mut msg = format!(
            "Regression ledger: {} entries not covered by manifest:\n",
            uncovered.len()
        );
        for (issue, path) in &uncovered {
            msg.push_str(&format!("  #{issue}: {path}\n"));
        }
        panic!("{msg}");
    }
}
