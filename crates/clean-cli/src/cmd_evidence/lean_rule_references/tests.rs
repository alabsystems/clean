// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serde_json::{json, Value};
use std::fs;

const SPEC: &str = "namespace Spec\ninductive Judgment where\n  | sort : Judgment\nend Spec\n";
const CONTROL: &str =
    "namespace Spec\ntheorem sort_control : Refutes .sort True := trivial\nend Spec\n";
const EXTRA_CONTROL: &str =
    "namespace Extra\ntheorem sort_control : Refutes .sort True := trivial\nend Extra\n";

fn write_source(root: &Path, file: &str, text: &str) {
    let path = root.join(file);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn fixture(spec: &str, control: Option<&str>) -> (tempfile::TempDir, Value) {
    let root = tempfile::tempdir().unwrap();
    fs::create_dir(root.path().join("spec")).unwrap();
    fs::write(root.path().join("spec/Rules.lean"), spec).unwrap();
    if let Some(control) = control {
        fs::write(root.path().join("spec/Controls.lean"), control).unwrap();
    }
    let inventory = json!({
        "spec": {"root": "spec", "rule_carriers": ["Spec.Judgment"]},
        "rows": [{
            "id": "sort",
            "cic_l": [{
                "file": "Rules.lean",
                "item": "Spec.Judgment.sort",
                "kind": "constructor",
                "control": {"theorem": "Spec.sort_control", "file": "Controls.lean"}
            }]
        }]
    });
    (root, inventory)
}

fn read_fixture(root: &Path, inventory: Value) -> Report {
    validate(root, &serde_json::from_value(inventory).unwrap()).unwrap()
}

fn assert_unexpected_control(report: &Report, theorem: &str, file: &str) {
    assert_eq!(report.findings.len(), 1, "{:?}", report.findings);
    let finding = &report.findings[0];
    assert!(
        finding.starts_with("CONTROL:") && finding.contains(theorem) && finding.contains(file),
        "{finding}"
    );
}

#[test]
fn exact_constructor_and_named_control_match() {
    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.matched.len(), 1);
    assert_eq!(report.controls.len(), 1);
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);
}

#[test]
fn qualified_head_and_constructor_match_the_same_binding() {
    let changed = CONTROL.replace(
        "Refutes .sort",
        "CICL.NegativeControls.Refutes CICL.NegativeControls.Rule.sort",
    );
    let (root, inventory) = fixture(SPEC, Some(&changed));
    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.controls.len(), 1, "{:?}", report.findings);
    assert!(report.findings.is_empty());
    assert!(report.unreadable.is_empty());
}

#[test]
fn wrong_kind_and_unmapped_constructor_are_refused() {
    let new_rule = SPEC.replace("end Spec", "  | pi : Judgment\nend Spec");
    let (root, mut inventory) = fixture(&new_rule, Some(CONTROL));
    let report = read_fixture(root.path(), inventory.clone());
    assert_eq!(report.findings.len(), 1, "{:?}", report.findings);
    assert!(report.findings[0].contains("Spec.Judgment.pi"));

    inventory["rows"][0]["cic_l"][0]["kind"] = json!("def");
    let report = read_fixture(root.path(), inventory);
    assert!(report.matched.is_empty());
    assert!(report.findings[0].contains("not declared with that kind"));
}

#[test]
fn unsuitable_control_and_unreadable_input_have_distinct_results() {
    let changed = CONTROL.replace("sort_control :", "sort_control (h : False) :");
    let (root, inventory) = fixture(SPEC, Some(&changed));
    let report = read_fixture(root.path(), inventory.clone());
    assert_eq!(report.matched.len(), 1);
    assert!(report.controls.is_empty());
    assert!(report.findings[0].contains("ground Refutes"));

    fs::remove_file(root.path().join("spec/Controls.lean")).unwrap();
    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.matched.len(), 1);
    assert!(report.controls.is_empty());
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert!(report
        .unreadable
        .contains_key(Path::new("spec/Controls.lean")));
}

#[test]
fn reverse_census_reports_a_ground_control_in_an_uncited_file() {
    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    write_source(root.path(), "spec/Uncited.lean", EXTRA_CONTROL);

    let report = read_fixture(root.path(), inventory);
    assert_unexpected_control(&report, "Extra.sort_control", "spec/Uncited.lean");
    assert_eq!(report.controls.len(), 1);
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);
}

#[test]
fn reverse_census_distinguishes_the_same_qualified_theorem_in_two_files() {
    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    write_source(root.path(), "spec/Second.lean", CONTROL);

    let report = read_fixture(root.path(), inventory);
    assert_unexpected_control(&report, "Spec.sort_control", "spec/Second.lean");
    assert_eq!(report.controls.len(), 1);
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);
}

#[test]
fn reverse_census_checks_explicit_exemptions() {
    let (root, mut inventory) = fixture(SPEC, None);
    inventory["rows"][0]["cic_l"][0]["control"] = json!({"none": "No premise to remove"});

    let report = read_fixture(root.path(), inventory.clone());
    assert!(report.controls.is_empty());
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);

    write_source(root.path(), "spec/Uncited.lean", CONTROL);
    let report = read_fixture(root.path(), inventory);
    assert_unexpected_control(&report, "Spec.sort_control", "spec/Uncited.lean");
    assert!(report.controls.is_empty());
}

#[test]
fn reverse_census_uses_cross_package_prefixes_and_excludes_lake_artifacts() {
    let (root, mut inventory) = fixture(SPEC, None);
    inventory["spec"]["control_roots"] = json!({"Model/": "model"});
    inventory["rows"][0]["cic_l"][0]["control"]["file"] = json!("Model/Controls.lean");
    write_source(root.path(), "model/Model/Controls.lean", CONTROL);
    write_source(root.path(), "model/ModelExtra/Controls.lean", EXTRA_CONTROL);
    write_source(
        root.path(),
        "model/Model/.lake/Controls.lean",
        EXTRA_CONTROL,
    );
    write_source(root.path(), "spec/.lake/Controls.lean", EXTRA_CONTROL);

    let report = read_fixture(root.path(), inventory.clone());
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);
    assert_eq!(report.controls.len(), 1);
    assert_eq!(
        report.controls.first().unwrap().file.as_path(),
        Path::new("Model/Controls.lean")
    );

    write_source(root.path(), "model/Model/More.lean", EXTRA_CONTROL);
    let report = read_fixture(root.path(), inventory);
    assert_unexpected_control(&report, "Extra.sort_control", "model/Model/More.lean");
}

#[test]
fn reverse_census_names_a_missing_configured_control_root() {
    let (root, mut inventory) = fixture(SPEC, Some(CONTROL));
    inventory["spec"]["control_roots"] = json!({"Model/": "missing-model"});

    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.controls.len(), 1);
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert_eq!(report.unreadable.len(), 1, "{:?}", report.unreadable);
    assert!(report.unreadable.contains_key(Path::new("missing-model")));
}

#[test]
fn reverse_census_refuses_a_designation_in_an_excluded_directory() {
    let (root, mut inventory) = fixture(SPEC, None);
    inventory["rows"][0]["cic_l"][0]["control"]["file"] = json!(".lake/Controls.lean");
    write_source(root.path(), "spec/.lake/Controls.lean", CONTROL);

    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.findings.len(), 1, "{:?}", report.findings);
    assert!(report.findings[0].contains("outside the control census scope"));
    assert!(report.controls.is_empty());
    assert!(report.unreadable.is_empty(), "{:?}", report.unreadable);
}

#[cfg(unix)]
#[test]
fn reverse_census_keeps_an_unreadable_cited_source_out_of_the_loader() {
    use std::os::unix::fs::symlink;

    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    fs::rename(
        root.path().join("spec/Rules.lean"),
        root.path().join("Rules.lean"),
    )
    .unwrap();
    symlink(
        root.path().join("Rules.lean"),
        root.path().join("spec/Rules.lean"),
    )
    .unwrap();

    let report = read_fixture(root.path(), inventory);
    assert!(report.matched.is_empty());
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert!(report.unreadable[Path::new("spec/Rules.lean")].contains("regular"));
}

#[test]
fn reverse_census_does_not_silently_drop_an_uncited_parser_recovery() {
    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    write_source(root.path(), "spec/Unreadable.lean", "def broken : Nat :=\n");

    let report = read_fixture(root.path(), inventory);
    assert_eq!(report.controls.len(), 1);
    assert!(report.findings.is_empty(), "{:?}", report.findings);
    assert_eq!(report.unreadable.len(), 1, "{:?}", report.unreadable);
    assert!(report.unreadable[Path::new("spec/Unreadable.lean")].contains("parser recovery"));
}

#[test]
fn reverse_census_reports_invalid_evidence_before_unavailable_evidence() {
    let (root, inventory) = fixture(SPEC, Some(CONTROL));
    write_source(root.path(), "spec/Unreadable.lean", "def broken : Nat :=\n");

    assert!(matches!(
        read_fixture(root.path(), inventory.clone()).verdict(),
        Err(EvidenceCheckError::Unavailable(_))
    ));

    write_source(root.path(), "spec/Uncited.lean", EXTRA_CONTROL);
    assert!(matches!(
        read_fixture(root.path(), inventory).verdict(),
        Err(EvidenceCheckError::Invalid(_))
    ));
}
