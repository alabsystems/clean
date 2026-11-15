// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "support/rustc.rs"]
mod rustc_support;

#[path = "support/metadata.rs"]
mod metadata_support;

use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_compile_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "clean_auto_encapsulation_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> Output {
    let metadata = metadata_support::clean_auto();
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    // TRUST OPT-OUT — use Cargo's selected `RUSTC` so this snippet and the
    // linked crate metadata always share a compiler ABI. When that compiler is
    // Trust, disable obligation checking for this throwaway API-surface probe;
    // the snippet proves only that a public name is reachable.
    // The compiler is Trust (owner directive 2026-09-28); there is no retry
    // without the opt-out.
    let run_rustc = || {
        let mut cmd = Command::new(rustc_support::cargo_rustc());
        cmd.arg("-Ztrust-verify=off");
        cmd.arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_auto={}", metadata.artifact.display()));
        metadata.configure(&mut cmd);
        cmd.output()
    };
    let output = run_rustc().expect("trustc should be runnable from integration tests");

    let _ = fs::remove_dir_all(&compile_dir);
    output
}

fn assert_external_compile_fails(test_name: &str, source: &str, expected_fragments: &[&str]) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "snippet unexpectedly compiled successfully\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for fragment in expected_fragments {
        assert!(
            stderr.contains(fragment),
            "expected rustc stderr to contain `{fragment}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

#[test]
#[file_serial]
fn test_cdcl_types_stay_private() {
    assert_external_compile_fails(
        "private_cdcl_types",
        r#"
use clean_auto::{CdclSolver, ClauseRef, Lit, SatUnsatCore, SolveResult, SolverStats, Var};
"#,
        &[
            "CdclSolver",
            "ClauseRef",
            "Lit",
            "SatUnsatCore",
            "SolveResult",
            "SolverStats",
            "Var",
            "unresolved imports",
        ],
    );
}

#[test]
#[file_serial]
fn test_cdcl_module_stays_private() {
    assert_external_compile_fails(
        "private_cdcl_module",
        r#"
fn touch() {
    let _ = clean_auto::cdcl::CdclSolver::new(1);
}
"#,
        &["cdcl", "private"],
    );
}

#[test]
#[file_serial]
fn test_theories_module_stays_private() {
    assert_external_compile_fails(
        "private_theories_module",
        r#"
use clean_auto::theories::arithmetic::types::ArithVar;

fn touch() {
    let _ = ArithVar(0);
}
"#,
        &["theories", "private"],
    );
}

#[test]
#[file_serial]
fn test_bridge_internal_types_stay_private() {
    // BridgeResult and HypothesisOpts must remain crate-private.
    // BridgeError, ProofMethod, and SmtProofResult are intentionally public (#2882).
    assert_external_compile_fails(
        "private_bridge_internals",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::{BridgeResult, HypothesisOpts};
"#,
        &["private"],
    );
}

#[test]
#[file_serial]
fn test_trigger_extraction_helpers_stay_private() {
    // extract_triggers and extract_ematch_triggers are bridge-internal helpers
    // that return crate-private types. They must not be callable from outside
    // the crate. (#2858)
    assert_external_compile_fails(
        "private_trigger_helpers",
        r#"
fn touch(bridge: &clean_auto::bridge::SmtBridge<'_>) {
    let _ = bridge.extract_triggers(todo!(), &[0]);
    let _ = bridge.extract_ematch_triggers(todo!(), &[0]);
}
"#,
        &["private"],
    );
}
