// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! G69 through the production parser, file context, elaborator and kernel.

use std::process::Command;

fn check(source: &str) -> (bool, String) {
    let dir = tempfile::tempdir().expect("temporary project");
    let path = dir.path().join("Main.lean");
    std::fs::write(&path, source).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("check")
        .arg(&path)
        .output()
        .expect("run clean check");
    (
        output.status.success(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
    )
}

macro_rules! fixture {
    ($file:literal) => {
        include_str!(concat!("../../../tests/fixtures/recursive_theorem/", $file))
    };
}

#[test]
fn recursive_theorems_and_section_captures_check_without_axioms() {
    let (ok, text) = check(fixture!("positive.lean"));
    assert!(ok, "{text}");
    assert!(!text.contains("sorry"), "{text}");
}

#[test]
fn invalid_recursion_and_wrong_recursive_call_signatures_are_refused() {
    for (source, reason) in [
        (fixture!("cycle.lean"), "constructor field"),
        (fixture!("extra_section_argument.lean"), "mismatch"),
        (fixture!("extra_section_auto_argument.lean"), "mismatch"),
        (fixture!("missing_implicit_argument.lean"), "mismatch"),
        (fixture!("missing_own_after_section_auto.lean"), "mismatch"),
        (fixture!("unsafe.lean"), "'unsafe' theorems are not allowed"),
    ] {
        let (ok, text) = check(source);
        assert!(!ok, "{source}\n{text}");
        assert!(text.to_lowercase().contains(reason), "{text}");
        assert!(!text.contains("synthetic sorry"), "{text}");
    }
}

#[test]
fn recursive_tactic_axiom_census_known_divergence() {
    let (ok, text) = check(fixture!("proof_axioms_gap.lean"));
    assert!(!ok, "known proof-metadata gap closed or changed: {text}");
    assert!(text.contains("does not depend on any axioms"), "{text}");
    assert!(text.contains("guard_msgs"), "{text}");
}
