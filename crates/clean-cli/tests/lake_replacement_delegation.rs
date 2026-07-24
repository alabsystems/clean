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
}
