// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evidence guards for #3707 Lake replacement mode.
//!
//! These tests intentionally document the current blocked state instead of
//! claiming Lake execution is clean-owned. They should be updated when
//! `clean lake run` and `clean lake test` gain a native clean runtime execution
//! bridge.

use std::path::{Path, PathBuf};

fn cli_crate_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).to_path_buf()
}

fn read_cli_source(relative: &str) -> String {
    let path = cli_crate_root().join(relative);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
}

#[test]
fn lake_run_and_test_fail_closed_instead_of_delegating_to_lean_run() {
    let source = read_cli_source("src/cmd_lake/run.rs");

    assert!(
        !source.contains("Command::new(\"lean\")"),
        "#3707 evidence expected Lake run/test to avoid spawning the Lean4 `lean` binary"
    );
    assert!(
        !source.contains(".arg(\"--run\")"),
        "#3707 evidence expected Lake run/test to avoid invoking `lean --run`"
    );
    assert!(
        source.contains("clean lake run is fail-closed"),
        "#3707 evidence expected `clean lake run` to fail closed at the runtime boundary"
    );
    assert!(
        source.contains("clean lake test is fail-closed"),
        "#3707 evidence expected `clean lake test` to fail closed at the runtime boundary"
    );
    assert!(
        source.contains("native clean runtime/interpreter bridge"),
        "#3707 evidence expected the user-facing blocker to name the missing clean runtime bridge"
    );
    assert!(
        source.contains("Refusing to delegate to external `lean --run`"),
        "#3707 evidence expected the failure mode to make Lean4 delegation refusal explicit"
    );
}

#[test]
fn replacement_scorecard_blocks_lake_workflow_while_delegation_remains() {
    let source = read_cli_source("src/cmd_replacement/rows.rs");
    let lake_row_start = source
        .find("\"lake-workflow\"")
        .expect("replacement scorecard must contain the Lake workflow row for #3707");
    let lake_row = &source[lake_row_start..];

    assert!(
        lake_row.contains("IssueRef::new(3707"),
        "Lake workflow replacement row must be tied to #3707"
    );
    assert!(
        lake_row.contains("ReplacementStatus::Blocked"),
        "Lake workflow replacement row must remain blocked while runtime execution is missing"
    );
    assert!(
        lake_row.contains("must not delegate project semantics to Lean4"),
        "Lake workflow replacement blocker must make Lean4 process delegation visible"
    );
    assert!(
        lake_row.contains("clean lake smoke --report reports/lake-replacement-smoke.json"),
        "Lake workflow row's gate command must be the smoke generator that emits the row's \
         evidence artifact"
    );
    assert!(
        lake_row.contains("reports/lake-replacement-smoke.json\","),
        "Lake workflow row must keep naming reports/lake-replacement-smoke.json as its evidence \
         artifact"
    );
}

/// #3707 evidence-generator guard: `clean lake smoke` (src/cmd_lake/smoke.rs)
/// must stay clean-owned (no `lean`/`lake` subprocess) and must record the
/// self-describing artifact schema the lake-workflow row consumes:
/// schema version, per-step verdicts, generating commit, the no-delegation
/// posture, and explicit non-claims.
#[test]
fn lake_smoke_generator_is_clean_owned_and_schema_complete() {
    let source = read_cli_source("src/cmd_lake/smoke.rs");

    assert!(
        !source.contains("Command::new(\"lean\")"),
        "the smoke generator must not spawn the Lean4 `lean` binary"
    );
    assert!(
        !source.contains("Command::new(\"lake\")"),
        "the smoke generator must not spawn the Lean4 `lake` binary"
    );
    assert!(
        source.contains("clean-lake-replacement-smoke-v1"),
        "the smoke artifact must carry a stable schema version"
    );
    assert!(
        source.contains("\"lake-workflow\"") && source.contains("3707"),
        "the smoke artifact must name the replacement row and issue it backs"
    );
    assert!(
        source.contains("generated_at_commit"),
        "the smoke artifact must record the generating commit"
    );
    assert!(
        source.contains("steps"),
        "the smoke artifact must record per-step results"
    );
    assert!(
        source.contains("no_lean4_delegation"),
        "the smoke artifact must record the no-Lean4-delegation posture"
    );
    assert!(
        source.contains("non_claims"),
        "the smoke artifact must record explicit non-claims"
    );
    assert!(
        source.contains("tests/lake_replacement_delegation.rs"),
        "the smoke artifact must cite this source-level delegation gate"
    );
}
