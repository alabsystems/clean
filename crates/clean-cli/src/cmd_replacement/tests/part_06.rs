// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 6) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use crate::cmd_replacement::*;

#[test]
fn replacement_status_json_is_deterministic_for_rust_first_inventory() {
    let Ok(report1) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present");
        return;
    };
    let Ok(report2) = ReplacementStatusReport::current() else {
        return;
    };
    let first = serde_json::to_string_pretty(&report1).expect("serialize replacement report");
    let second = serde_json::to_string_pretty(&report2).expect("serialize replacement report");
    let value: serde_json::Value =
        serde_json::from_str(&first).expect("replacement status JSON should parse");

    assert_eq!(first, second);
    assert_eq!(
        value["rust_first_tooling"]["schema_version"],
        "clean-rust-first-tooling-migration-v1"
    );
    assert_eq!(value["rust_first_tooling"]["overall_status"], "rust_owned");
    assert_eq!(
        value["readiness_accounting"]["benchmark_launch_gate"]["status"],
        "demoted"
    );
    assert_eq!(
        value["readiness_accounting"]["benchmark_launch_gate"]["launch_blocking"],
        false
    );
    assert!(!value["readiness_accounting"]["product_surfaces"]
        .as_array()
        .expect("product_surfaces should be an array")
        .iter()
        .any(|surface| surface["id"] == "benchmark-publication-launch"));
    assert!(value["readiness_accounting"]["python_wrappers"]
        .as_array()
        .expect("python_wrappers should be an array")
        .iter()
        .any(|wrapper| wrapper["id"] == "release-issue-hygiene"
            && wrapper["launch_blocking"] == false
            && wrapper["target_rust_surface"]
                .as_str()
                .is_some_and(|surface| surface.starts_with("clean replacement"))));
    assert_eq!(
        value["readiness_accounting"]["certification_python_dependency_count"],
        0
    );
    assert_eq!(
        value["readiness_accounting"]["certification_python_dependency_ids"],
        serde_json::json!([])
    );
    assert_eq!(
        value["readiness_accounting"]["non_launch_python_reference_ids"],
        serde_json::json!([
            "docs-metrics-sync",
            "benchmark-publication-check",
            "benchmark-publication-launch"
        ])
    );
    let demoted_proofs = value["readiness_accounting"]["demoted_python_reference_proofs"]
        .as_array()
        .expect("demoted_python_reference_proofs should be an array");
    assert_eq!(demoted_proofs.len(), 3);
    assert!(demoted_proofs
        .iter()
        .all(|proof| proof["certifying"] == false
            && proof["replacement_critical"] == false
            && proof["status"] == "demoted"));
    assert!(demoted_proofs
        .iter()
        .any(|proof| proof["id"] == "docs-metrics-sync"
            && proof["rust_status_surface"]
                .as_str()
                .is_some_and(|surface| surface.contains("non-launch diagnostic"))));
    let rust_owned_proofs = value["readiness_accounting"]["rust_owned_python_wrapper_proofs"]
        .as_array()
        .expect("rust_owned_python_wrapper_proofs should be an array");
    // Commit fc6794736 ("release: remove ghost readiness dependencies") retired the fourth
    // entry, `mathverse-download-pytest`. The Python command it claimed credit for replacing
    // (`PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m pytest
    // tests/test_download_mathverse_library.py`) was never tracked in this repository, so
    // counting it as a replaced Python wrapper was a ghost dependency — a migration proof for
    // a wrapper that never existed. The Rust capability was not lost: the row is still
    // Rust-owned, still replacement-critical, and still exposed as the `clean mathverse
    // download` product surface — pinned by
    // `part_03::retired_ghost_python_wrapper_keeps_its_rust_capability`. Assert survivors by
    // name rather than by count, so a genuine drop reports which row disappeared.
    assert_eq!(
        rust_owned_proofs
            .iter()
            .filter_map(|proof| proof["id"].as_str())
            .collect::<Vec<_>>(),
        vec![
            "system-health-release-json",
            "trust-boundary-audit-report",
            "release-issue-hygiene",
        ]
    );
    assert!(rust_owned_proofs
        .iter()
        .all(|proof| proof["python_path_certifying"] == false
            && proof["replacement_critical"] == true
            && proof["status"] == "rust_owned"
            && proof["rust_certifying_surface"]
                .as_str()
                .is_some_and(|surface| surface.starts_with("clean "))));
    assert_eq!(
        value["readiness_accounting"]["replacement_row_proof_surface_audit"]["status"],
        "passed"
    );
    assert_eq!(
        value["readiness_accounting"]["replacement_row_proof_surface_audit"]
            ["wrapper_gate_row_ids"],
        serde_json::json!([])
    );
    assert_eq!(
        value["readiness_accounting"]["replacement_row_proof_surface_audit"]
            ["wrapper_evidence_artifact_row_ids"],
        serde_json::json!([])
    );
    let command_deck = &value["readiness_accounting"]["reviewer_proof_command_deck"];
    assert_eq!(command_deck["wrapper_dependent_command_count"], 0);
    assert_eq!(
        command_deck["wrapper_dependent_row_ids"],
        serde_json::json!([])
    );
    assert_eq!(
        command_deck["wrapper_free_command_count"],
        command_deck["command_count"]
    );
    assert_eq!(
        command_deck["launch_blocking_row_ids"],
        value["readiness_accounting"]["launch_blocking_row_ids"]
    );
    assert_eq!(
        command_deck["launch_blocking_wrapper_free_command_count"],
        command_deck["launch_blocking_command_count"]
    );
    assert_eq!(
        command_deck["launch_blocking_wrapper_dependent_command_count"],
        0
    );
    assert_eq!(
        command_deck["launch_blocking_wrapper_dependent_row_ids"],
        serde_json::json!([])
    );
    let launch_blocking_commands = command_deck["launch_blocking_commands"]
        .as_array()
        .expect("reviewer command deck launch blocker command subset");
    assert_eq!(
        launch_blocking_commands.len(),
        command_deck["launch_blocking_command_count"]
            .as_u64()
            .expect("launch blocking command count") as usize
    );
    assert!(launch_blocking_commands.iter().all(|command| {
        command["wrapper_free"] == true && command["launch_blocking_until_green"] == true
    }));
    let wrapper_free_gate = &value["readiness_accounting"]["certification_wrapper_free_gate"];
    assert_eq!(wrapper_free_gate["status"], "passed");
    assert_eq!(
        wrapper_free_gate["certifying_python_dependency_count"],
        value["readiness_accounting"]["certification_python_dependency_count"]
    );
    assert_eq!(
        wrapper_free_gate["wrapper_dependent_proof_surface_count"],
        0
    );
    assert_eq!(
        wrapper_free_gate["wrapper_dependent_command_count"],
        command_deck["wrapper_dependent_command_count"]
    );
    assert_eq!(
        wrapper_free_gate["launch_blocking_wrapper_dependent_command_count"],
        command_deck["launch_blocking_wrapper_dependent_command_count"]
    );
    assert_eq!(
        wrapper_free_gate["wrapper_dependency_blocker_ids"],
        serde_json::json!([])
    );
    assert_eq!(
        wrapper_free_gate["rust_reviewer_command"],
        "clean replacement status --json"
    );
    assert_eq!(
        wrapper_free_gate["rust_reviewer_json_pointer"],
        "/readiness_accounting/certification_wrapper_free_gate"
    );
    assert_eq!(
        wrapper_free_gate["rust_reviewer_command_wrapper_free"],
        true
    );
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_schema_version"],
        "clean-certification-wrapper-free-assertions-v1"
    );
    assert_eq!(wrapper_free_gate["required_reviewer_assertion_count"], 7);
    let required_reviewer_assertions = wrapper_free_gate["required_reviewer_assertions"]
        .as_array()
        .expect("certification wrapper-free reviewer assertions");
    assert_eq!(
        required_reviewer_assertions.len(),
        wrapper_free_gate["required_reviewer_assertion_count"]
            .as_u64()
            .expect("required reviewer assertion count") as usize
    );
    assert!(required_reviewer_assertions
        .iter()
        .all(|assertion| assertion["json_pointer"]
            .as_str()
            .is_some_and(|pointer| pointer
                .starts_with("/readiness_accounting/certification_wrapper_free_gate/"))));
    assert!(required_reviewer_assertions.iter().any(|assertion| assertion
            ["json_pointer"]
            == "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependency_blocker_ids"
            && assertion["expected_json"] == "[]"));
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_json_pointers_unique"],
        true
    );
    assert_eq!(
        required_reviewer_assertions
            .iter()
            .filter_map(|assertion| assertion["json_pointer"].as_str())
            .collect::<BTreeSet<_>>()
            .len(),
        required_reviewer_assertions.len()
    );
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_json_pointers_parseable"],
        true
    );
    assert!(required_reviewer_assertions
        .iter()
        .all(|assertion| assertion["json_pointer"]
            .as_str()
            .is_some_and(json_pointer_is_absolute_and_parseable)));
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_json_pointers_dereferenceable"],
        true
    );
    assert!(required_reviewer_assertions.iter().all(|assertion| {
        assertion["json_pointer"].as_str().is_some_and(|pointer| {
            certification_wrapper_free_assertion_actual_json(
                pointer,
                value["readiness_accounting"]["certification_python_dependency_count"]
                    .as_u64()
                    .expect("certification python dependency count") as usize,
                wrapper_free_gate["wrapper_dependent_proof_surface_count"]
                    .as_u64()
                    .expect("wrapper proof surface count") as usize,
                wrapper_free_gate["wrapper_dependent_command_count"]
                    .as_u64()
                    .expect("wrapper command count") as usize,
                wrapper_free_gate["launch_blocking_wrapper_dependent_command_count"]
                    .as_u64()
                    .expect("launch-blocking wrapper command count") as usize,
                wrapper_free_gate["wrapper_dependency_blocker_ids"]
                    .as_array()
                    .expect("wrapper blocker ids")
                    .iter()
                    .filter_map(|id| id.as_str())
                    .collect::<Vec<_>>()
                    .as_slice(),
                wrapper_free_gate["rust_reviewer_command_wrapper_free"]
                    .as_bool()
                    .expect("rust reviewer command wrapper-free"),
            )
            .is_some()
        })
    }));
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_expected_json_parseable"],
        true
    );
    assert!(required_reviewer_assertions
        .iter()
        .all(
            |assertion| assertion["expected_json"].as_str().is_some_and(|expected| {
                serde_json::from_str::<serde_json::Value>(expected).is_ok()
            })
        ));
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_cover_blocking_fields"],
        true
    );
    assert_eq!(
        wrapper_free_gate["missing_required_reviewer_assertion_json_pointers"],
        serde_json::json!([])
    );
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_match_live_values"],
        true
    );
    assert_eq!(
        wrapper_free_gate["required_reviewer_assertions_live_value_mismatch_count"],
        0
    );
    assert_eq!(
        wrapper_free_gate["mismatched_required_reviewer_assertion_json_pointers"],
        serde_json::json!([])
    );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_status"],
        "complete"
    );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_blocker_count"],
        0
    );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_blockers"],
        serde_json::json!([])
    );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_required_json_pointer_count"],
        7
    );
    assert_eq!(
            wrapper_free_gate["reviewer_proof_completeness_required_json_pointers"],
            serde_json::json!([
                "/readiness_accounting/certification_wrapper_free_gate/status",
                "/readiness_accounting/certification_wrapper_free_gate/certifying_python_dependency_count",
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_proof_surface_count",
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependent_command_count",
                "/readiness_accounting/certification_wrapper_free_gate/launch_blocking_wrapper_dependent_command_count",
                "/readiness_accounting/certification_wrapper_free_gate/wrapper_dependency_blocker_ids",
                "/readiness_accounting/certification_wrapper_free_gate/rust_reviewer_command_wrapper_free",
            ])
        );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_required_json_pointers_match_assertions"],
        true
    );
    assert_eq!(
        wrapper_free_gate["reviewer_proof_completeness_required_json_pointers"],
        serde_json::Value::Array(
            required_reviewer_assertions
                .iter()
                .map(|assertion| assertion["json_pointer"].clone())
                .collect()
        )
    );
    assert!(wrapper_free_gate
        ["reviewer_proof_completeness_required_json_pointers_fingerprint_algorithm"]
        .as_str()
        .expect("reviewer proof completeness pointer fingerprint algorithm")
        .contains("json_pointer"));
    let completeness_pointer_fingerprint = wrapper_free_gate
        ["reviewer_proof_completeness_required_json_pointers_fingerprint_sha256"]
        .as_str()
        .expect("reviewer proof completeness pointer fingerprint");
    assert_eq!(completeness_pointer_fingerprint.len(), 64);
    assert!(completeness_pointer_fingerprint
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(
        wrapper_free_gate["reviewer_proof_completeness_fingerprint_algorithm"]
            .as_str()
            .expect("reviewer proof completeness fingerprint algorithm")
            .contains("reviewer_proof_completeness_required_json_pointers_fingerprint_sha256")
    );
    let completeness_fingerprint = wrapper_free_gate
        ["reviewer_proof_completeness_fingerprint_sha256"]
        .as_str()
        .expect("reviewer proof completeness fingerprint");
    assert_eq!(completeness_fingerprint.len(), 64);
    assert!(completeness_fingerprint
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(
        wrapper_free_gate["required_reviewer_assertions_fingerprint_algorithm"]
            .as_str()
            .expect("certification wrapper-free assertions fingerprint algorithm")
            .contains("expected_json")
    );
    let assertions_fingerprint = wrapper_free_gate
        ["required_reviewer_assertions_fingerprint_sha256"]
        .as_str()
        .expect("certification wrapper-free assertions fingerprint");
    assert_eq!(assertions_fingerprint.len(), 64);
    assert!(assertions_fingerprint
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(wrapper_free_gate["fingerprint_algorithm"]
        .as_str()
        .expect("certification wrapper-free gate fingerprint algorithm")
        .contains("required_reviewer_assertions_json_pointers_dereferenceable_bit"));
    let wrapper_free_gate_fingerprint = wrapper_free_gate["fingerprint_sha256"]
        .as_str()
        .expect("certification wrapper-free gate fingerprint");
    assert_eq!(wrapper_free_gate_fingerprint.len(), 64);
    assert!(wrapper_free_gate_fingerprint
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    let launch_blocking_fingerprint = command_deck["launch_blocking_fingerprint_sha256"]
        .as_str()
        .expect("reviewer command deck launch blocker fingerprint");
    assert_eq!(launch_blocking_fingerprint.len(), 64);
    assert!(launch_blocking_fingerprint
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(command_deck["fingerprint_algorithm"]
        .as_str()
        .expect("reviewer command deck fingerprint algorithm")
        .contains("wrapper_free_bit"));
    let fingerprint = command_deck["fingerprint_sha256"]
        .as_str()
        .expect("reviewer command deck fingerprint");
    assert_eq!(fingerprint.len(), 64);
    assert!(fingerprint.chars().all(|ch| ch.is_ascii_hexdigit()));
    assert!(command_deck["commands"]
        .as_array()
        .expect("reviewer command deck commands")
        .iter()
        .any(|command| command["row_id"] == "proof-system-certification"
            && command["wrapper_free"] == true
            && command["launch_blocking_until_green"] == true));
    assert_eq!(
        value["readiness_accounting"]["full_replacement_certification_gate"]["launch_ready"],
        false
    );
    assert!(
        value["readiness_accounting"]["blocker_evidence_requirements"]
            .as_array()
            .expect("blocker evidence requirements should be an array")
            .iter()
            .any(|row| row["row_id"] == "proof-system-certification"
                && row["evidence_artifact"] == TRUST_CORE_EVIDENCE_SCHEMA_VERSION)
    );
}
