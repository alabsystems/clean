// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 3) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn replacement_status_accounts_python_wrappers_and_certification_gate() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let accounting = &report.readiness_accounting;
    let wrapper_ids: Vec<&str> = accounting
        .python_wrappers
        .iter()
        .map(|row| row.id)
        .collect();

    assert_eq!(accounting.python_wrapper_count, wrapper_ids.len());
    assert_eq!(
        accounting.remaining_python_wrapper_count,
        accounting
            .python_wrappers
            .iter()
            .filter(|row| row.status != ToolMigrationStatus::RustOwned)
            .count()
    );
    assert_eq!(
        accounting.launch_blocking_python_wrapper_count,
        accounting
            .python_wrappers
            .iter()
            .filter(|row| row.launch_blocking)
            .count()
    );
    assert_eq!(accounting.replacement_critical_python_wrapper_count, 3);
    assert_eq!(accounting.rust_owned_python_wrapper_count, 3);
    assert_eq!(accounting.demoted_python_reference_count, 3);
    assert_eq!(accounting.certification_python_dependency_count, 0);
    assert!(accounting.certification_python_dependency_ids.is_empty());
    assert_eq!(
        accounting.non_launch_python_reference_ids,
        vec![
            "docs-metrics-sync",
            "benchmark-publication-check",
            "benchmark-publication-launch"
        ]
    );
    assert_eq!(
        accounting.demoted_python_reference_proofs.len(),
        accounting.demoted_python_reference_count
    );
    assert!(accounting
        .demoted_python_reference_proofs
        .iter()
        .all(|proof| !proof.replacement_critical
            && !proof.certifying
            && proof.status == ToolMigrationStatus::Demoted
            && proof
                .exclusion_reason
                .contains("cannot satisfy or block Lean4 replacement readiness")));
    assert!(accounting
        .demoted_python_reference_proofs
        .iter()
        .any(|proof| proof.id == "benchmark-publication-launch"
            && proof
                .rust_status_surface
                .starts_with("clean bench publication-check --launch --json")
            && proof
                .evidence_required_to_reclassify
                .contains("not a Lean4 replacement launch blocker")));
    assert_eq!(
        accounting.rust_owned_python_wrapper_proofs.len(),
        accounting.rust_owned_python_wrapper_count
    );
    assert!(accounting
        .rust_owned_python_wrapper_proofs
        .iter()
        .all(|proof| proof.replacement_critical
            && !proof.python_path_certifying
            && proof.status == ToolMigrationStatus::RustOwned
            && proof.rust_certifying_surface.starts_with("clean ")));
    assert!(accounting
        .rust_owned_python_wrapper_proofs
        .iter()
        .any(|proof| proof.id == "release-issue-hygiene"
            && proof
                .rust_certifying_surface
                .starts_with("clean replacement release-issue-hygiene --fetch --json")
            && proof
                .legacy_python_path_status
                .contains("No Python wrapper is required")));
    assert!(accounting
        .python_wrapper_fail_closed_policy
        .contains("Any Python wrapper needed to generate or certify replacement evidence"));
    for required in [
        "docs-metrics-sync",
        "system-health-release-json",
        "trust-boundary-audit-report",
        "benchmark-publication-check",
        "benchmark-publication-launch",
        "release-issue-hygiene",
    ] {
        assert!(
            wrapper_ids.contains(&required),
            "python wrapper inventory missing {required}"
        );
    }

    let issue_hygiene = accounting
        .python_wrappers
        .iter()
        .find(|row| row.id == "release-issue-hygiene")
        .expect("release issue hygiene wrapper");
    assert_eq!(
        issue_hygiene.command,
        "python3 scripts/release_issue_hygiene.py --fetch"
    );
    assert_eq!(issue_hygiene.status, ToolMigrationStatus::RustOwned);
    assert!(!issue_hygiene.launch_blocking);
    assert!(issue_hygiene
        .target_rust_surface
        .starts_with("clean replacement release-issue-hygiene --fetch --json"));
    assert!(issue_hygiene
        .evidence_required_to_retire
        .contains("Rust-owned launch gate"));

    let benchmark_launch = accounting
        .python_wrappers
        .iter()
        .find(|row| row.id == "benchmark-publication-launch")
        .expect("benchmark launch wrapper");
    assert_eq!(benchmark_launch.status, ToolMigrationStatus::Demoted);
    assert!(!benchmark_launch.launch_blocking);
    assert!(benchmark_launch
        .target_rust_surface
        .starts_with("clean bench publication-check --launch --json"));

    let certification_gate = &accounting.full_replacement_certification_gate;
    assert_eq!(certification_gate.target_claim, TARGET_CLAIM);
    assert!(!certification_gate.launch_ready);
    assert_eq!(
        certification_gate.zero_trust_gates_passed,
        report.zero_trust_gates_passed
    );
    assert!(!certification_gate.replacement_rows_ready);
    assert!(certification_gate.rust_first_tooling_ready);
    assert!(certification_gate.required_conditions.contains(
            &"replacement-critical Python wrappers are Rust-owned or explicitly demoted as non-launch evidence"
        ));
    assert!(certification_gate.required_conditions.contains(
            &"certification_python_dependency_count is zero; any nonzero value blocks external certification"
        ));
    assert!(certification_gate
        .fail_closed_reason
        .contains("clean full Lean4 replacement is not certified"));
}

#[test]
fn replacement_status_surfaces_product_readiness_and_benchmark_direction() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let accounting = &report.readiness_accounting;
    let surfaces: Vec<&str> = accounting
        .product_surfaces
        .iter()
        .map(|surface| surface.surface)
        .collect();

    assert!(surfaces.contains(&"clean factory status --json"));
    assert!(!accounting
        .product_surfaces
        .iter()
        .any(|surface| surface.id == "benchmark-publication-launch"));
    assert!(surfaces
        .iter()
        .any(|surface| surface.starts_with("clean replacement release-issue-hygiene")));
    assert!(surfaces.iter().any(|surface| surface
        .starts_with("clean mathverse download --version <version> --output-dir <dir> --json")));
    for surface in &accounting.product_surfaces {
        assert!(surface.surface.starts_with("clean "));
        assert!(!surface.blocker.is_empty());
    }

    let benchmark_gate = &accounting.benchmark_launch_gate;
    assert_eq!(benchmark_gate.id, "benchmark-publication-launch");
    assert!(benchmark_gate
        .rust_surface
        .starts_with("clean bench publication-check --launch --json"));
    assert_eq!(
        benchmark_gate.python_gate_command,
        "python3 scripts/check_benchmark_publication.py --check --launch"
    );
    assert_eq!(benchmark_gate.status, ToolMigrationStatus::Demoted);
    assert!(!benchmark_gate.launch_blocking);
    assert_eq!(
        benchmark_gate.required_artifact,
        "reports/benchmarks/publication/current.json"
    );
    for required in [
        "accepted for this replacement pass",
        "audit evidence",
        "not launch-blocking replacement evidence",
    ] {
        assert!(
            benchmark_gate.required_parity_claim.contains(required),
            "benchmark launch gate should name {required}"
        );
    }
}

#[test]
fn trust_boundary_audit_groups_expected_and_unexpected_hits() {
    let records = vec![
        TrustBoundaryAuditRecord {
            lane: "auto".to_owned(),
            crate_name: "clean-auto".to_owned(),
            test_name: "test_lra_boundary_expected".to_owned(),
            tactic: "linarith".to_owned(),
            proof_kind: "fallback".to_owned(),
            subsystem: "LRA".to_owned(),
            description: "expected".to_owned(),
            step_index: "0".to_owned(),
            arithmetic_boundary_steps: 1,
            local_gap_steps: 0,
            trust_subterm_count: 2,
        },
        TrustBoundaryAuditRecord {
            lane: "auto".to_owned(),
            crate_name: "clean-auto".to_owned(),
            test_name: "test_lra_boundary_expected".to_owned(),
            tactic: "linarith".to_owned(),
            proof_kind: "fallback".to_owned(),
            subsystem: "LRA".to_owned(),
            description: "expected again".to_owned(),
            step_index: "1".to_owned(),
            arithmetic_boundary_steps: 3,
            local_gap_steps: 1,
            trust_subterm_count: 4,
        },
        TrustBoundaryAuditRecord {
            lane: "elab".to_owned(),
            crate_name: "clean-elab".to_owned(),
            test_name: "test_common_goal_regression".to_owned(),
            tactic: "mathverse".to_owned(),
            proof_kind: "fallback".to_owned(),
            subsystem: "LIA".to_owned(),
            description: "unexpected".to_owned(),
            step_index: "0".to_owned(),
            arithmetic_boundary_steps: 1,
            local_gap_steps: 0,
            trust_subterm_count: 1,
        },
    ];
    let report = TrustBoundaryAuditReport::from_records(
        records,
        &["lra_boundary".to_owned()],
        &[PathBuf::from("/tmp/auto.tsv")],
        Path::new(TRUST_BOUNDARY_EXPECTED_TESTS_PATH),
    );

    assert_eq!(report.schema_version, TRUST_BOUNDARY_AUDIT_SCHEMA_VERSION);
    assert_eq!(report.total_raw_hits, 3);
    assert_eq!(report.expected_boundary_only_hits, 2);
    assert_eq!(report.unexpected_hits, 1);
    assert!(!report.gate2_effectively_met);
    assert_eq!(report.groups.len(), 2);
    assert_eq!(report.expected_groups[0].count, 2);
    assert_eq!(report.expected_groups[0].total_arith, 4);

    let json = serde_json::to_value(&report).expect("json");
    assert_eq!(
        json["generated_by"],
        "clean replacement trust-boundary-audit"
    );
    assert_eq!(
        json["unexpected_groups"][0]["test_name"],
        "test_common_goal_regression"
    );

    let markdown = render_trust_boundary_audit_markdown(&report);
    assert!(markdown.contains("# Gate 2 TrustBoundary Audit Report"));
    assert!(markdown.contains("## Unexpected Hits"));
    assert!(markdown.contains("## Expected Boundary-Only Hits"));
    assert!(markdown.contains("clean replacement trust-boundary-audit"));
}

#[test]
fn trust_boundary_tsv_parser_fails_closed_on_malformed_rows() {
    let dir = tempfile::tempdir().expect("tempdir");
    let malformed = dir.path().join("bad.tsv");
    fs::write(&malformed, "too\tfew\tcolumns\n").expect("write malformed input");

    let error = parse_trust_boundary_tsv(&malformed).expect_err("malformed row fails");
    assert!(error
        .to_string()
        .contains("expected 11 tab-separated columns"));

    let invalid_count = dir.path().join("bad-count.tsv");
    fs::write(
        &invalid_count,
        "lane\tcrate\ttest\ttactic\tproof\tsubsystem\tdesc\t0\tNaN\t0\t1\n",
    )
    .expect("write invalid count");
    let error = parse_trust_boundary_tsv(&invalid_count).expect_err("invalid count fails");
    assert!(error
        .to_string()
        .contains("columns 9-11 must be non-negative integers"));
}
