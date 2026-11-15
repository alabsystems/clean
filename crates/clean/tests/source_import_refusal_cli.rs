// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! A refused source module cannot supply a partial environment to its importer.

use serde_json::Value;
use std::path::Path;
use std::process::Command;

fn check(root: &Path, permissive: bool) -> (bool, Value) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
    command
        .current_dir(root)
        .args(["check", "Main.lean", "--json"]);
    if permissive {
        command.arg("--permissive-imports");
    }
    let output = command.output().expect("run production clean check");
    let report = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "no check report: {error}; stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output.status.success(), report)
}

fn project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("isolated source project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"source_import_refusal\"\n",
    )
    .expect("package boundary");
    dir
}

fn broken(root: &Path) {
    std::fs::write(
        root.join("Broken.lean"),
        "namespace Broken\ndef good : Nat := 7\ndef bad : Nat := True\nend Broken\n",
    )
    .expect("source with a valid prefix and a refused declaration");
}

#[test]
fn failed_source_import_never_credits_the_importing_declaration() {
    for permissive in [false, true] {
        let dir = project();
        broken(dir.path());
        std::fs::write(
            dir.path().join("Main.lean"),
            "import Broken\ndef answer : Nat := Broken.good\n",
        )
        .expect("importer");
        let (success, report) = check(dir.path(), permissive);
        assert!(!success, "{report}");
        assert_eq!(
            report["success_count"], 0,
            "partial import credited: {report}"
        );
        let errors = report["errors"].as_array().expect("error inventory");
        assert!(
            errors
                .iter()
                .any(|e| e.as_str().is_some_and(|e| e.contains("Broken.bad"))),
            "{report}"
        );
        assert!(
            errors.iter().any(|e| e
                .as_str()
                .is_some_and(|e| e.contains("source elaboration refused"))),
            "{report}"
        );
    }
}

#[test]
fn refusal_propagates_through_a_source_import_chain() {
    let dir = project();
    broken(dir.path());
    std::fs::write(
        dir.path().join("Middle.lean"),
        "import Broken\nnamespace Middle\ndef value : Nat := Broken.good\nend Middle\n",
    )
    .expect("middle import");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Middle\ndef answer : Nat := Middle.value\n",
    )
    .expect("transitive importer");
    let (success, report) = check(dir.path(), false);
    assert!(!success, "{report}");
    assert_eq!(report["success_count"], 0, "{report}");
    assert!(
        report["errors"]
            .as_array()
            .expect("errors")
            .iter()
            .any(|e| e
                .as_str()
                .is_some_and(|e| e.contains("source elaboration refused"))),
        "{report}"
    );
}

#[test]
fn successful_source_import_still_elaborates_and_kernel_checks() {
    let dir = project();
    std::fs::write(
        dir.path().join("Good.lean"),
        "namespace Good\ndef value : Nat := 7\nend Good\n",
    )
    .expect("healthy source import");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Good\ndef answer : Nat := Good.value\n",
    )
    .expect("healthy importer");
    let (success, report) = check(dir.path(), false);
    assert!(success, "{report}");
    assert_eq!(report["status"], "pass", "{report}");
    assert_eq!(report["success_count"], 1, "{report}");
    assert_eq!(report["failed_count"], 0, "{report}");
}

#[test]
fn unfinished_source_imports_remain_no_verdict_without_import_failure_rows() {
    for (module, permissive, prior_sibling, later_refusal) in [
        ("Base", false, false, false),
        ("Base", true, false, false),
        ("Middle", false, true, false),
        ("Base", false, false, true),
    ] {
        let dir = project();
        std::fs::write(dir.path().join("Base.lean"), "def value : Nat := 7\n")
            .expect("valid dependency");
        std::fs::write(
            dir.path().join("Middle.lean"),
            "import Base\ndef middle : Nat := value\n",
        )
        .expect("transitive dependency");
        std::fs::write(
            dir.path().join("Good.lean"),
            "-- An independent empty source module.\n",
        )
        .expect("prior sibling");
        std::fs::write(
            dir.path().join("Later.lean"),
            "-- later parser refusal\nnot_a_command\n",
        )
        .expect("later refused sibling");
        std::fs::write(
            dir.path().join("Main.lean"),
            format!(
                "{}import {module}\n{}def answer : Nat := 7\n",
                if prior_sibling { "import Good\n" } else { "" },
                if later_refusal { "import Later\n" } else { "" }
            ),
        )
        .expect("importer");
        let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
        command.current_dir(dir.path()).args([
            "check",
            "Main.lean",
            "--json",
            "--decl-budget",
            "1",
        ]);
        if permissive {
            command.arg("--permissive-imports");
        }
        let output = command.output().expect("production budget control");
        assert!(!output.status.success());
        let report: Value = serde_json::from_slice(&output.stdout).expect("check report");
        assert_eq!(report["status"], "diverged", "{report}");
        assert_eq!(report["success_count"], 0, "{report}");
        assert_eq!(report["failed_count"], 0, "{report}");
        assert!(
            report["diverged_count"].as_u64().is_some_and(|n| n > 0),
            "{report}"
        );
        for field in [
            "errors",
            "parser_recovery",
            "trust_failures",
            "kernel_failures",
        ] {
            assert!(
                report[field]
                    .as_array()
                    .expect("diagnostic inventory")
                    .is_empty(),
                "{field}: {report}"
            );
        }
    }
}
