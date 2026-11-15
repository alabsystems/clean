// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise class registration through the shipping check command. The frozen
//! manifest's expected outcomes were independently checked with Lean v4.35.0.
use std::process::Command;

#[test]
fn class_attribute_cohort_through_check_cli() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reports/class-attribute-2026-11-12");
    let manifest: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(root.join("manifest.json")).unwrap())
            .expect("frozen class cohort");
    let cases = manifest["cases"].as_array().expect("case list");
    assert_eq!(cases.len(), 24);
    let directory = tempfile::tempdir().expect("isolated check directory");
    for case in cases {
        let name = case["name"].as_str().expect("case name");
        let accept = case["accept"].as_bool().expect("oracle outcome");
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .current_dir(directory.path())
            .args(["check", "--json"])
            .arg(root.join("fixtures").join(format!("{name}.lean")))
            .output()
            .expect("execute check");
        let report: serde_json::Value = serde_json::from_slice(&output.stdout)
            .unwrap_or_else(|error| panic!("{name}: {error}; {output:?}"));
        assert_eq!(
            output.status.code(),
            Some(i32::from(!accept)),
            "{name}: {report}"
        );
        assert_eq!(report["parser_recovery"], serde_json::json!([]), "{name}");
        if accept {
            assert_eq!(report["failed_count"], 0, "{name}: {report}");
            assert_eq!(report["errors"], serde_json::json!([]), "{name}");
        } else {
            let expected = if name == "duplicate" {
                "class has already been declared"
            } else if name.contains("bad_outparam") || name == "classBadOutParam" {
                "depends on `outParam`"
            } else {
                "invalid 'class'"
            };
            assert!(report.to_string().contains(expected), "{name}: {report}");
        }
    }
}
