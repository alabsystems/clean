// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Class-target refusals must reach the shipping check command as failures.

use std::process::{Command, Output};

fn check(source: &str) -> (Output, serde_json::Value) {
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("class_attribute.lean");
    std::fs::write(&path, source).expect("write class control");
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .current_dir(directory.path())
        .args(["check", "--json"])
        .arg(&path)
        .output()
        .expect("run Clean check");
    let report: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("missing check report: {error}; {output:?}"));
    assert_eq!(report["parser_recovery"], serde_json::json!([]));
    (output, report)
}

fn assert_definition_refused(source: &str, name: &str) {
    let (output, report) = check(source);
    assert_eq!(
        output.status.code(),
        Some(1),
        "{report}; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        report["failed_count"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "{report}"
    );
    let diagnostic = report.to_string();
    assert!(
        diagnostic.contains("invalid 'class'") && diagnostic.contains(name),
        "{report}"
    );
}

#[test]
fn declaration_class_attribute_refuses_definition_through_check_cli() {
    assert_definition_refused("@[class] def Foo (n : Nat) : Prop := n > 2\n", "Foo");
}

#[test]
fn standalone_class_attribute_refuses_definition_through_check_cli() {
    assert_definition_refused(
        "def Bla (n : Nat) : Prop := n > 2\nattribute [class] Bla\n",
        "Bla",
    );
}

#[test]
fn valid_structure_class_and_instance_survive_check_cli() {
    let (output, report) = check(
        "structure ClassAttributeCliCarrier where\n  value : Nat\n\
         attribute [class] ClassAttributeCliCarrier\n\
         instance : ClassAttributeCliCarrier where\n  value := 7\n\
         example : (inferInstance : ClassAttributeCliCarrier).value = 7 := rfl\n",
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "{report}; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(report["failed_count"], 0, "{report}");
    assert!(
        report["success_count"]
            .as_u64()
            .is_some_and(|count| count >= 2),
        "{report}"
    );
    for field in ["errors", "kernel_failures", "trust_failures", "assumptions"] {
        assert_eq!(report[field], serde_json::json!([]), "{field}: {report}");
    }
    assert_eq!(report["trust_summary"]["sorry_axioms"], 0, "{report}");
    assert_eq!(report["trust_summary"]["sorry_terms_minted"], 0, "{report}");
}
