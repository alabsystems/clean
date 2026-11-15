// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Protected-head assumption selection through the production file checker.

use std::process::Command;

fn check(source: &str) -> (bool, String) {
    eprintln!(
        "assumption-protected-cli executable {}",
        env!("CARGO_BIN_EXE_clean")
    );
    let directory = tempfile::tempdir().expect("temporary project");
    let path = directory.path().join("Main.lean");
    std::fs::write(&path, source).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("check")
        .arg(&path)
        .output()
        .expect("run production clean check");
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
        include_str!(concat!(
            "../../../tests/fixtures/assumption_protected_search/",
            $file
        ))
    };
}

#[test]
fn assumption_and_rwa_keep_the_usable_value_and_empty_axiom_closure() {
    let (ok, text) = check(fixture!("positive.lean"));
    assert!(ok, "{text}");
    assert!(!text.contains("sorry"), "{text}");
}

#[test]
fn assumption_without_a_usable_local_reports_no_match() {
    let (ok, text) = check(fixture!("no_match.lean"));
    assert!(!ok, "{text}");
    assert!(
        text.contains("assumption: no hypothesis matches the goal"),
        "{text}"
    );
    assert!(!text.contains("synthetic sorry"), "{text}");
}

#[test]
fn explicit_and_rewritten_blocked_locals_keep_their_type_refusal() {
    for source in [
        fixture!("exact_blocked.lean"),
        fixture!("rwa_at_blocked.lean"),
    ] {
        let (ok, text) = check(source);
        assert!(!ok, "{source}\n{text}");
        assert!(text.to_lowercase().contains("type mismatch"), "{text}");
        assert!(!text.contains("synthetic sorry"), "{text}");
    }
}
