// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::process::Command;

fn check(source: &str) -> (bool, String) {
    let dir = tempfile::tempdir().expect("temporary project");
    let path = dir.path().join("Main.lean");
    std::fs::write(&path, source).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("check")
        .arg(&path)
        .output()
        .expect("run actual clean check");
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
            "../../../tests/fixtures/section_auto_order/",
            $file
        ))
    };
}

#[test]
fn section_auto_order_accepts_public_and_dependent_telescope_uses() {
    for source in [
        fixture!("positive.lean"),
        fixture!("declaration_kinds.lean"),
        fixture!("ordinary_recursive.lean"),
        fixture!("relative_methods.lean"),
        fixture!("relative_nontoplevel.lean"),
        fixture!("wf_own.lean"),
    ] {
        let (ok, text) = check(source);
        assert!(ok, "{text}");
        assert!(!text.contains("sorry"), "{text}");
    }
}

#[test]
fn section_auto_order_refuses_swapped_external_explicit_arguments() {
    for source in [
        fixture!("wrong_own_order.lean"),
        fixture!("wrong_captured_order.lean"),
        fixture!("wrong_recursive_order.lean"),
    ] {
        let (ok, text) = check(source);
        assert!(!ok, "{source}\n{text}");
        assert!(text.to_lowercase().contains("mismatch"), "{text}");
        assert!(!text.contains("synthetic sorry"), "{text}");
    }
}

#[test]
fn section_auto_order_native_call_preserves_captured_runtime_arguments() {
    let dir = tempfile::tempdir().expect("temporary project");
    let file = dir.path().join("Main.lean");
    std::fs::write(&file, fixture!("native.lean")).expect("write source");
    for (args, expected) in [(&[][..], "3\n2\n"), (&["a", "b"][..], "5\n4\n")] {
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .args(["run", "--decl", "main"])
            .arg(&file)
            .arg("--")
            .args(args)
            .output()
            .expect("run native compiler");
        assert!(
            output.status.success(),
            "stdout={}\nstderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected.as_bytes());
    }
}

#[test]
fn section_auto_order_ordinary_recursive_calls_refuse_captured_arguments() {
    for source in [
        fixture!("ordinary_recursive_extra_section.lean"),
        fixture!("ordinary_recursive_extra_section_ordinary_use.lean"),
        fixture!("ordinary_recursive_extra_implicit_section.lean"),
        fixture!("ordinary_recursive_nondecreasing.lean"),
        fixture!("ordinary_recursive_extra_section_auto.lean"),
        fixture!("wf_extra_section.lean"),
    ] {
        let (ok, text) = check(source);
        assert!(!ok, "{source}\n{text}");
        assert!(!text.contains("synthetic sorry"), "{text}");
    }
}
