// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Latest Lean v4.35.0 rejects undeclared attribute names. These controls were
//! executed against the official oracle; evidence and source hashes live in
//! reports/unknown-attribute-rejection-2026-11-12/. Test the shipping caller,
//! including structured failures and parser-recovery-free positive controls.

use std::process::Command;

#[test]
fn source_attribute_names_agree_with_lean_through_check_cli() {
    let cases = [
        (
            "unknown_decl",
            "@[notARealAttribute] def bad14 : Nat := 1\n",
            Some("notARealAttribute"),
        ),
        (
            "unknown_cmd",
            "def cmdTarget : Nat := 1\nattribute [notARealAttribute] cmdTarget\n",
            Some("notARealAttribute"),
        ),
        (
            "camel_case",
            "def fast (n : Nat) : Nat := n + 1\n@[implementedBy fast]\ndef slow (n : Nat) : Nat := n + 2\n",
            Some("implementedBy"),
        ),
        (
            "canonical",
            "def fast (n : Nat) : Nat := n + 1\n@[implemented_by fast]\ndef slow (n : Nat) : Nat := n + 2\n",
            None,
        ),
        (
            "modeled",
            "@[simp] theorem attr_simp_eq : (1 : Nat) = 1 := rfl\n@[inline] def attr_inline (n : Nat) : Nat := n + 1\n",
            None,
        ),
    ];
    let directory = tempfile::tempdir().expect("fixture directory");
    for (name, source, unknown) in cases {
        let path = directory.path().join(format!("{name}.lean"));
        std::fs::write(&path, source).expect("write Lean control");
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .current_dir(directory.path())
            .args(["check", "--json"])
            .arg(&path)
            .output()
            .expect("run Clean check");
        let report: serde_json::Value = serde_json::from_slice(&output.stdout)
            .unwrap_or_else(|error| panic!("{name}: missing check report: {error}; {output:?}"));
        assert_eq!(
            output.status.code(),
            Some(i32::from(unknown.is_some())),
            "{name}: {report}; stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(report["parser_recovery"], serde_json::json!([]), "{name}");
        if let Some(attribute) = unknown {
            assert!(
                report["failed_count"].as_u64().is_some_and(|n| n > 0),
                "{name}: {report}"
            );
            let diagnostic = report.to_string();
            assert!(
                diagnostic.contains("Unknown attribute") && diagnostic.contains(attribute),
                "{name}: {report}"
            );
        } else {
            assert_eq!(report["success_count"], 2, "{name}: {report}");
            assert_eq!(report["failed_count"], 0, "{name}: {report}");
            for field in ["errors", "kernel_failures", "trust_failures"] {
                assert_eq!(report[field], serde_json::json!([]), "{name}: {report}");
            }
        }
    }
}
