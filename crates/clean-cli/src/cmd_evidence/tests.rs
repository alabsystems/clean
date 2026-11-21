// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests of the figure registry, the historical readers and `check`.

use super::elaboration::{ELABORATION_BASELINE, ELABORATION_FIGURE};
use super::island_gaps::{ISLAND_GAPS, ISLAND_GAPS_FIGURE};
use super::rule_families::{RULE_FAMILIES_FIGURE, RULE_INVENTORY};
use super::*;
use serde_json::{json, Value};
use std::collections::HashSet;

#[test]
fn test_catalog_serializes_registry_fields_without_reader_functions() {
    let catalog = serde_json::to_value(FIGURES).expect("serialize figure catalog");
    let entries = catalog.as_array().expect("catalog is an array");
    assert_eq!(entries.len(), FIGURES.len());
    let mut ids = HashSet::new();
    for entry in entries {
        let keys: Vec<&str> = entry
            .as_object()
            .expect("entry is an object")
            .keys()
            .map(String::as_str)
            .filter(|key| *key != "absent_reason")
            .collect();
        assert_eq!(
            keys,
            [
                "cost_class",
                "headline",
                "historical",
                "id",
                "input_scope",
                "lane",
                "plan_unit",
                "producer_module",
                "ratchet_direction"
            ]
        );
        assert!(ids.insert(entry["id"].as_str().unwrap().to_owned()));
        let inputs = entry["input_scope"].as_array().unwrap();
        if let Some(reason) = entry.get("absent_reason") {
            assert!(!reason.as_str().unwrap().trim().is_empty());
            assert!(inputs.is_empty());
            assert!(entry["producer_module"].is_null());
            assert_eq!(entry["headline"], true);
            assert_eq!(entry["historical"], false);
        } else {
            assert!(!inputs.is_empty());
        }
    }
    assert_eq!(
        entries
            .iter()
            .find(|entry| entry["id"] == CLEAN_FIGURE)
            .unwrap(),
        &json!({
            "id": CLEAN_FIGURE,
            "plan_unit": "P3",
            "producer_module": "scripts/patched_kernel_control.py",
            "input_scope": [CLEAN_PINS, SCOREBOARD],
            "cost_class": "offline",
            "headline": true,
            "ratchet_direction": null,
            "lane": "P",
            "historical": true
        })
    );
    for (id, headline) in [
        (k3_scoreboard::DECIDED_FIGURE, true),
        (k3_scoreboard::ACCEPTED_FIGURE, false),
    ] {
        assert_eq!(
            entries.iter().find(|entry| entry["id"] == id).unwrap(),
            &json!({
                "id": id,
                "plan_unit": "K3",
                "producer_module": "scripts/kcheck_coverage.py",
                "input_scope": k3_scoreboard::INPUTS,
                "cost_class": "offline",
                "headline": headline,
                "ratchet_direction": null,
                "lane": "K",
                "historical": true
            })
        );
    }
}

fn example() -> (Value, Value) {
    let measured_at = "2026-11-15T22:23:17Z";
    let report = json!({
        "schema": "clean.p3-trust-leg/v2",
        "measured_at": measured_at,
        "trust": {"commit": "trust-run"},
        "clean_pin_in_trust": "clean-pin",
        "pins": {
            "first": [
                {"site": "a", "mutant": "Minted"},
                {"site": "b", "mutant": "Refused"},
            ],
            "second": [{"site": "c", "mutant": "Minted"}],
        },
    });
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "headline": {"planted_false_mints_trust": {
            "sites": 3,
            "minted_under_mutant": 2,
            "measured_at": measured_at,
            "source": TRUST_PINS,
        }},
    });
    (report, scoreboard)
}

fn check_with(
    figure: &str,
    report_path: &str,
    report: &Value,
    scoreboard: &Value,
) -> anyhow::Result<()> {
    let root = tempfile::tempdir().unwrap();
    write_fixture(root.path(), report_path, report);
    write_fixture(root.path(), SCOREBOARD, scoreboard);
    run(&[figure.to_owned()], false, Some(root.path()))
}

fn write_fixture(root: &Path, name: &str, contents: &Value) {
    let path = root.join(name);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, serde_json::to_vec(contents).unwrap()).unwrap();
}

fn rule_family_example() -> (Value, Value) {
    let inventory = json!({"rows": [
        {"id": "full", "kind": "rule", "status": "specified"},
        {"id": "part", "kind": "rule", "status": "partial"},
        {"id": "gap", "kind": "rule", "status": "unspecified"},
        {"id": "ordering", "kind": "strategy"},
        {"id": "cache", "kind": "infrastructure"}
    ]});
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "headline": "independent from the route row",
        "route": {"lean_kernel_rule_families": {
            "families": 3, "specified": 1, "partial": 1, "unspecified": 1,
            "source": RULE_INVENTORY
        }}
    });
    (inventory, scoreboard)
}

#[test]
fn counts_only_rule_families_and_binds_each_scoreboard_field() {
    let (inventory, scoreboard) = rule_family_example();
    check_with(
        RULE_FAMILIES_FIGURE,
        RULE_INVENTORY,
        &inventory,
        &scoreboard,
    )
    .unwrap();
    for field in ["families", "specified", "partial", "unspecified", "source"] {
        let mut changed = scoreboard.clone();
        changed["route"]["lean_kernel_rule_families"][field] = if field == "source" {
            json!("wrong-inventory.json")
        } else {
            json!(5)
        };
        let error =
            check_with(RULE_FAMILIES_FIGURE, RULE_INVENTORY, &inventory, &changed).unwrap_err();
        assert!(error
            .to_string()
            .contains("route.lean_kernel_rule_families differs"));
    }
}

#[test]
fn rule_inventory_refuses_ambiguous_ids_and_unrecognized_shapes() {
    let (inventory, scoreboard) = rule_family_example();
    for (index, field, changed, diagnostic) in [
        (1, "id", json!("full"), "duplicate row ID"),
        (1, "status", json!(null), "requires a status"),
        (1, "status", json!("done"), "unknown variant `done`"),
        (1, "kind", json!("other"), "unknown variant `other`"),
        (3, "status", json!("specified"), "carries a rule status"),
    ] {
        let mut altered = inventory.clone();
        altered["rows"][index][field] = changed;
        let error =
            check_with(RULE_FAMILIES_FIGURE, RULE_INVENTORY, &altered, &scoreboard).unwrap_err();
        assert!(error.to_string().contains(diagnostic));
    }
}

fn elaboration_example() -> (Value, Value) {
    let report = json!({
        "schema": "self-proof-elab-v2",
        "commit": "historical-binary",
        "complete": true,
        "expected_modules": [["alpha", "Shared"], ["alpha", "Later"], ["beta", "Shared"]],
        "modules": [
            {"package": "alpha", "module": "Shared", "status": "elaborated"},
            {"package": "alpha", "module": "Later", "status": "timed_out"},
            {"package": "beta", "module": "Shared", "status": "refused"}
        ],
        "probes": [{"status": "elaborated"}]
    });
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "headline": "independent from this route row",
        "route": {"clean_elaborates_theories": {
            "modules": 3, "elaborated": 1,
            "by_package": {
                "alpha": {"modules": 2, "elaborated": 1},
                "beta": {"modules": 1, "elaborated": 0}
            },
            "producer_commit": "historical-binary", "source": ELABORATION_BASELINE
        }}
    });
    (report, scoreboard)
}

#[test]
fn elaboration_recounts_timed_out_and_refused_modules_by_package() {
    let (report, scoreboard) = elaboration_example();
    check_with(
        ELABORATION_FIGURE,
        ELABORATION_BASELINE,
        &report,
        &scoreboard,
    )
    .unwrap();
    let wrong_packages = json!({
        "alpha": {"modules": 2, "elaborated": 0},
        "beta": {"modules": 1, "elaborated": 1}
    });
    for (field, changed) in [
        ("by_package", wrong_packages),
        ("producer_commit", json!("different-binary")),
        ("modules", json!(4)),
        ("elaborated", json!(2)),
        ("source", json!("other-baseline.json")),
    ] {
        let mut board = scoreboard.clone();
        board["route"]["clean_elaborates_theories"][field] = changed;
        let error =
            check_with(ELABORATION_FIGURE, ELABORATION_BASELINE, &report, &board).unwrap_err();
        assert!(error
            .to_string()
            .contains("route.clean_elaborates_theories differs"));
    }
}

#[test]
fn elaboration_requires_a_complete_ordered_unique_roster() {
    let (report, scoreboard) = elaboration_example();
    let mut omitted = report.clone();
    omitted["modules"].as_array_mut().unwrap().pop();
    let mut duplicate = report.clone();
    duplicate["modules"][1]["module"] = json!("Shared");
    duplicate["expected_modules"][1][1] = json!("Shared");
    let mut incomplete = report.clone();
    incomplete["complete"] = json!(false);
    let mut invalid = report;
    invalid["modules"][1]["status"] = json!("timeout");
    for (value, diagnostic) in [
        (omitted, "differ from its declared roster"),
        (duplicate, "duplicate package and module"),
        (incomplete, "requires a complete run"),
        (invalid, "unknown variant `timeout`"),
    ] {
        let error = check_with(
            ELABORATION_FIGURE,
            ELABORATION_BASELINE,
            &value,
            &scoreboard,
        )
        .unwrap_err();
        assert!(error.to_string().contains(diagnostic));
    }
}

#[test]
fn checks_island_gaps_and_refuses_stale_counts_or_source() {
    let report = json!({
        "schema": "clean.kcheck_island_gaps.v1",
        "gaps": [
            {"id": "a", "status": "open"},
            {"id": "b", "status": "closed"},
            {"id": "c", "status": "pinned"}
        ]
    });
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "headline": "independent from this route row",
        "route": {"island_gaps": {"rows": 3, "open": 1, "source": ISLAND_GAPS}}
    });
    check_with(ISLAND_GAPS_FIGURE, ISLAND_GAPS, &report, &scoreboard).unwrap();

    for (field, value) in [
        ("rows", json!(4)),
        ("open", json!(3)),
        ("source", json!("other.json")),
    ] {
        let mut changed = scoreboard.clone();
        changed["route"]["island_gaps"][field] = value;
        let error = check_with(ISLAND_GAPS_FIGURE, ISLAND_GAPS, &report, &changed).unwrap_err();
        assert!(error.to_string().contains("route.island_gaps differs"));
    }
}

#[test]
fn accepts_an_empty_island_inventory_and_refuses_unknown_status() {
    let mut report = json!({"schema": "clean.kcheck_island_gaps.v1", "gaps": []});
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "route": {"island_gaps": {"rows": 0, "open": 0, "source": ISLAND_GAPS}}
    });
    check_with(ISLAND_GAPS_FIGURE, ISLAND_GAPS, &report, &scoreboard).unwrap();
    report["gaps"] = json!([{"status": "Open"}]);
    let error = check_with(ISLAND_GAPS_FIGURE, ISLAND_GAPS, &report, &scoreboard).unwrap_err();
    assert!(error.to_string().contains("unknown variant `Open`"));
}

#[test]
fn test_island_gaps_duplicate_gap_id_is_refused_as_denominator() {
    let report = json!({
        "schema": "clean.kcheck_island_gaps.v1",
        "gaps": [{"id": "a", "status": "open"}, {"id": "a", "status": "closed"}]
    });
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "route": {"island_gaps": {"rows": 2, "open": 1, "source": ISLAND_GAPS}}
    });
    let error = check_with(ISLAND_GAPS_FIGURE, ISLAND_GAPS, &report, &scoreboard).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&error), Some(1));
    assert!(error.to_string().contains("duplicate denominator member"));
}

#[test]
fn recounts_sites_across_test_groups() {
    let (report, scoreboard) = example();
    check_with(TRUST_FIGURE, TRUST_PINS, &report, &scoreboard).unwrap();
}

#[test]
fn rejects_drift_in_every_scoreboard_field() {
    let (report, scoreboard) = example();
    for (field, changed) in [
        ("sites", json!(4)),
        ("minted_under_mutant", json!(3)),
        ("measured_at", json!("2026-11-16T22:23:17Z")),
        ("source", json!("elsewhere.json")),
    ] {
        let mut board = scoreboard.clone();
        board["headline"]["planted_false_mints_trust"][field] = changed;
        let error = check_with(TRUST_FIGURE, TRUST_PINS, &report, &board).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(_))
        ));
    }
}

#[test]
fn rejects_changed_or_invalid_pin_rows() {
    let (report, scoreboard) = example();
    for changed in [
        json!([{"site": "c", "mutant": "Refused"}]),
        json!([{"site": "b", "mutant": "Minted"}]),
        json!([{"site": "c", "mutant": "Unknown"}]),
    ] {
        let mut altered = report.clone();
        altered["pins"]["second"] = changed;
        let error = check_with(TRUST_FIGURE, TRUST_PINS, &altered, &scoreboard).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(_))
        ));
    }
}

#[test]
fn refuses_flat_pins_and_a_grouped_pin_without_a_mutant_verdict() {
    let (mut flat, scoreboard) = example();
    let mut missing = flat.clone();
    missing["pins"]["second"] = json!([{"site": "c"}]);
    let pins = flat["pins"]
        .as_object()
        .unwrap()
        .values()
        .flat_map(|group| group.as_array().unwrap())
        .cloned()
        .collect();
    flat["pins"] = Value::Array(pins);
    for (report, diagnostic) in [
        (flat, "a map from test names to site pins"),
        (missing, "missing field `mutant`"),
    ] {
        let error = check_with(TRUST_FIGURE, TRUST_PINS, &report, &scoreboard).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(reason)) if reason.contains(diagnostic)
        ));
    }
}

#[test]
fn rejects_duplicate_test_groups_after_json_unescaping() {
    let text = r#"{
        "schema":"clean.p3-trust-leg/v2", "measured_at":"2026-11-15T22:23:17Z",
        "trust":{"commit":"trust-run"}, "clean_pin_in_trust":"clean-pin",
        "pins":{"first":[],"\u0066irst":[]}
    }"#;
    assert!(serde_json::from_str::<TrustPins>(text)
        .err()
        .unwrap()
        .to_string()
        .contains("duplicate test group"));
}

#[test]
fn distinguishes_unavailable_input_and_bad_usage() {
    let root = tempfile::tempdir().unwrap();
    let missing = run(&[TRUST_FIGURE.to_owned()], false, Some(root.path())).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&missing), Some(3));
    let unknown = run(&["selfproof.unknown".to_owned()], false, Some(root.path())).unwrap_err();
    assert_eq!(crate::forwarded_exit_code(&unknown), Some(2));
}

fn clean_example() -> (Value, Value) {
    let report = json!({
        "schema": "clean.patched_kernel_control.v1",
        "mutation": {"id": "check-type-nat-zero-false"},
        "measured_commit": "clean-run",
        "sites": [
            {"package": "alpha", "site": "a", "mutant": {"verdict": "minted"}},
            {"package": "beta", "site": "a", "mutant": {"verdict": "minted"}},
            {"package": "beta", "site": "b", "mutant": {"verdict": "refused"}},
        ],
        "summary": {"sites": 3, "minted_under_mutant": 2},
    });
    let scoreboard = json!({
        "schema": "clean.self_proof_scoreboard.v1",
        "headline": {
            "planted_false_mints_clean": {
                "sites": 3, "minted_under_mutant": 2,
                "measured_commit": "clean-run", "source": CLEAN_PINS,
            },
            "planted_false_mints_trust": "an unread sibling row",
        },
    });
    (report, scoreboard)
}

#[test]
fn clean_sites_use_package_and_site_identity() {
    let (mut report, scoreboard) = clean_example();
    check_with(CLEAN_FIGURE, CLEAN_PINS, &report, &scoreboard).unwrap();
    report["sites"][1]["package"] = json!("alpha");
    let error = check_with(CLEAN_FIGURE, CLEAN_PINS, &report, &scoreboard).unwrap_err();
    assert!(error.to_string().contains("duplicate package and site"));
}

#[test]
fn clean_check_recounts_even_when_summary_and_board_agree() {
    for (field, wrong) in [("sites", json!(4)), ("minted_under_mutant", json!(3))] {
        let (mut report, mut scoreboard) = clean_example();
        report["summary"][field] = wrong.clone();
        scoreboard["headline"]["planted_false_mints_clean"][field] = wrong;
        let error = check_with(CLEAN_FIGURE, CLEAN_PINS, &report, &scoreboard).unwrap_err();
        assert!(error.to_string().contains("the rows yield 2 of 3"));
    }
}

#[test]
fn clean_check_rejects_stale_provenance_with_matching_counts() {
    for (field, wrong) in [
        ("measured_commit", json!("other-run")),
        ("source", json!("other-report.json")),
    ] {
        let (report, mut scoreboard) = clean_example();
        scoreboard["headline"]["planted_false_mints_clean"][field] = wrong;
        let error = check_with(CLEAN_FIGURE, CLEAN_PINS, &report, &scoreboard).unwrap_err();
        assert!(error
            .to_string()
            .contains("headline.planted_false_mints_clean differs"));
    }
}

#[test]
fn clean_check_binds_the_experiment_and_verdict_format() {
    let (report, scoreboard) = clean_example();
    let mut other_experiment = report.clone();
    other_experiment["mutation"]["id"] = json!("other-mutation");
    let mut upper_case = report;
    upper_case["sites"][0]["mutant"]["verdict"] = json!("Minted");
    for invalid in [other_experiment, upper_case] {
        let error = check_with(CLEAN_FIGURE, CLEAN_PINS, &invalid, &scoreboard).unwrap_err();
        assert_eq!(crate::forwarded_exit_code(&error), Some(1));
        assert!(error.to_string().contains("unknown variant"));
    }
}

mod board;
