// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared fixtures and assertion helpers for the `clean replacement` tests.

use crate::cmd_replacement::*;

/// Tail assertions split out of
/// `replacement_status_accounts_launch_blockers_without_green_claims`
/// (same assertions, same order).
pub(super) fn assert_launch_blocker_accounting_tail(report: &ReplacementStatusReport) {
    let accounting = &report.readiness_accounting;
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_expected_json_parseable
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions
        .iter()
        .all(
            |assertion| serde_json::from_str::<serde_json::Value>(assertion.expected_json).is_ok()
        ));
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_cover_blocking_fields
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .missing_required_reviewer_assertion_json_pointers
        .is_empty());
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_match_live_values
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_live_value_mismatch_count,
        0
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .mismatched_required_reviewer_assertion_json_pointers
        .is_empty());
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_status,
        "complete"
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_blocker_count,
        0
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_proof_completeness_blockers
        .is_empty());
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointers,
        certification_wrapper_free_required_assertion_pointers()
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointer_count,
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointers
            .len()
    );
    assert!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointers_match_assertions
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointers
            .to_vec(),
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions
            .iter()
            .map(|assertion| assertion.json_pointer)
            .collect::<Vec<_>>()
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_proof_completeness_required_json_pointers_fingerprint_algorithm
        .contains("json_pointer"));
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_required_json_pointers_fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_proof_completeness_required_json_pointers_fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_proof_completeness_fingerprint_algorithm
        .contains("reviewer_proof_completeness_required_json_pointers_fingerprint_sha256"));
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .reviewer_proof_completeness_fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_proof_completeness_fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions_fingerprint_algorithm
        .contains("expected_json"));
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions_fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .certification_wrapper_free_gate
        .fingerprint_algorithm
        .contains("required_reviewer_assertions_json_pointers_dereferenceable_bit"));
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .certification_wrapper_free_gate
        .reviewer_rule
        .contains("External certification is wrapper-free"));
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .reviewer_proof_command_deck
        .launch_blocking_fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .reviewer_proof_command_deck
        .fingerprint_algorithm
        .contains("sha256(row_id || NUL || status"));
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .fingerprint_sha256
            .len(),
        64
    );
    assert!(accounting
        .reviewer_proof_command_deck
        .fingerprint_sha256
        .chars()
        .all(|ch| ch.is_ascii_hexdigit()));
    assert!(accounting
        .reviewer_proof_command_deck
        .commands
        .iter()
        .all(|command| command.wrapper_free));
    assert!(accounting
        .reviewer_proof_command_deck
        .commands
        .iter()
        .any(|command| command.row_id == "rust-first-tooling"
            && command.command == "clean replacement status --json"
            && command.launch_blocking_until_green));
    let launch_docs_evidence = accounting
        .blocker_evidence_requirements
        .iter()
        .find(|row| row.row_id == "launch-docs")
        .expect("launch docs blocker evidence");
    assert_eq!(
            launch_docs_evidence.gate_command,
            "clean release readiness-smoke --clean-clone-lite --launch --evidence /tmp/clean-release.json"
        );
    assert!(launch_docs_evidence
        .evidence_artifact
        .contains("reports/benchmarks/publication/current.json"));
    assert!(!report.launch_ready);
}

pub(super) fn current_kernel_soundness_inputs() -> (Lean4BaselineArtifact, usize, String) {
    let baseline = load_lean4_baseline().expect("Lean4 baseline");
    let expressions_source = read_repo_artifact(LEAN4_EXPRESSIONS_PATH).expect("expressions");
    let expressions = active_expressions(&expressions_source);
    let expressions_sha256 = sha256_expressions(&expressions);
    (baseline, expressions.len(), expressions_sha256)
}

pub(super) fn valid_kernel_soundness_launch_artifact(
    baseline: &Lean4BaselineArtifact,
    expression_count: usize,
    expressions_sha256: &str,
) -> KernelSoundnessLaunchEvidenceArtifact {
    let mut source_sha256 = BTreeMap::new();
    for path in [
        TRUST_CORE_RUST_SOURCE_PATH,
        LEAN4_BASELINE_PATH,
        LEAN4_EXPRESSIONS_PATH,
    ] {
        source_sha256.insert(
            path.to_string(),
            sha256_repo_artifact(path).expect("source sha256"),
        );
    }
    source_sha256.insert(
        TRUST_CORE_RUST_MODULE_TREE_KEY.to_string(),
        sha256_repo_module_tree(TRUST_CORE_RUST_MODULE_DIR).expect("module tree sha256"),
    );

    KernelSoundnessLaunchEvidenceArtifact {
        schema_version: KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
        generated_by: KERNEL_SOUNDNESS_RUST_GATE_COMMAND.to_string(),
        generated_at: "2026-04-26T00:00:00Z".to_string(),
        gate_command: KERNEL_SOUNDNESS_RUST_GATE_COMMAND.to_string(),
        status: "passed".to_string(),
        summary: KernelSoundnessLaunchEvidenceSummary {
            expected_steps: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            steps: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            passed: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            failed: 0,
        },
        kernel_differential: KernelSoundnessLaunchDifferentialEvidence {
            baseline_path: LEAN4_BASELINE_PATH.to_string(),
            expressions_path: LEAN4_EXPRESSIONS_PATH.to_string(),
            baseline_schema_version: baseline.schema_version,
            normalization_version: baseline.normalization_version,
            baseline_cases: baseline.cases.len(),
            expression_count,
            expressions_sha256: expressions_sha256.to_string(),
            baseline_sha256: sha256_repo_artifact(LEAN4_BASELINE_PATH).expect("baseline sha256"),
            expressions_file_sha256: sha256_repo_artifact(LEAN4_EXPRESSIONS_PATH)
                .expect("expressions sha256"),
        },
        source_sha256,
        lanes: KERNEL_SOUNDNESS_EXPECTED_LANES
            .iter()
            .map(|lane| KernelSoundnessLaunchLaneEvidence {
                id: lane.id.to_string(),
                expected_tests: lane.expected_tests,
                expected_output: lane.expected_output.map(str::to_string),
                matched_expected_count: true,
                matched_expected_output: true,
                status: "passed".to_string(),
            })
            .collect(),
    }
}

/// The checked-in ratchet with its counts, rows, and production sites closed
/// to 0/0. Strict deny-sorry launch-evidence lanes require a closed ratchet
/// (`current ratchet is not closed at 0/0`), so tests exercising the lanes
/// beyond that check use this fixture instead of the live artifact, which may
/// honestly carry open debt (G3 correction, 2026-07-01).
pub(super) fn closed_unchecked_decl_ratchet() -> UncheckedDeclRatchetArtifact {
    let mut ratchet = load_unchecked_decl_ratchet().expect("unchecked-decl ratchet");
    ratchet.add_decl_structural_count = 0;
    ratchet.add_decl_unchecked_count = 0;
    ratchet.add_decl_structural_production_sites = vec![];
    ratchet.add_decl_unchecked_production_sites = vec![];
    ratchet.files = vec![];
    ratchet
}

pub(super) fn valid_deny_sorry_launch_artifact(
    ratchet: &UncheckedDeclRatchetArtifact,
) -> DenySorryLaunchEvidenceArtifact {
    let mut source_sha256 = BTreeMap::new();
    for path in [TRUST_CORE_RUST_SOURCE_PATH, UNCHECKED_DECL_RATCHET_PATH] {
        source_sha256.insert(
            path.to_string(),
            sha256_repo_artifact(path).expect("source sha256"),
        );
    }
    source_sha256.insert(
        TRUST_CORE_RUST_MODULE_TREE_KEY.to_string(),
        sha256_repo_module_tree(TRUST_CORE_RUST_MODULE_DIR).expect("module tree sha256"),
    );

    DenySorryLaunchEvidenceArtifact {
        schema_version: DENY_SORRY_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
        generated_by: DENY_SORRY_RUST_GATE_COMMAND.to_string(),
        generated_at: "2026-04-26T00:00:00Z".to_string(),
        gate_command: DENY_SORRY_RUST_GATE_COMMAND.to_string(),
        status: "passed".to_string(),
        summary: DenySorryLaunchEvidenceSummary {
            expected_steps: DENY_SORRY_EXPECTED_STEPS,
            steps: DENY_SORRY_EXPECTED_STEPS,
            passed: DENY_SORRY_EXPECTED_STEPS,
            failed: 0,
        },
        ratchet: DenySorryLaunchRatchetEvidence {
            path: UNCHECKED_DECL_RATCHET_PATH.to_string(),
            add_decl_structural_count: ratchet.add_decl_structural_count,
            add_decl_unchecked_count: ratchet.add_decl_unchecked_count,
            sha256: sha256_repo_artifact(UNCHECKED_DECL_RATCHET_PATH).expect("ratchet sha256"),
        },
        source_sha256,
        lanes: DENY_SORRY_EXPECTED_LANES
            .iter()
            .map(|lane| DenySorryLaunchLaneEvidence {
                id: lane.id.to_string(),
                expected_tests: lane.expected_tests,
                matched_expected_count: true,
                status: "passed".to_string(),
            })
            .collect(),
    }
}

pub(super) fn valid_axiom_audit_launch_artifact(
    axiom_audit: &AxiomAuditArtifact,
) -> AxiomAuditLaunchEvidenceArtifact {
    let mut source_sha256 = BTreeMap::new();
    for path in [AXIOM_AUDIT_RUST_SOURCE_PATH, AXIOM_AUDIT_PATH] {
        source_sha256.insert(
            path.to_string(),
            sha256_repo_artifact(path).expect("source sha256"),
        );
    }

    AxiomAuditLaunchEvidenceArtifact {
        schema_version: AXIOM_AUDIT_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
        generated_by: AXIOM_AUDIT_GATE_COMMAND.to_string(),
        generated_at: "2026-04-26T00:00:00Z".to_string(),
        gate_command: AXIOM_AUDIT_GATE_COMMAND.to_string(),
        status: "passed".to_string(),
        summary: AxiomAuditLaunchEvidenceSummary {
            expected_steps: AXIOM_AUDIT_EXPECTED_STEPS,
            steps: AXIOM_AUDIT_EXPECTED_STEPS,
            passed: AXIOM_AUDIT_EXPECTED_STEPS,
            failed: 0,
        },
        axiom_audit: AxiomAuditLaunchAuditEvidence {
            path: AXIOM_AUDIT_PATH.to_string(),
            total_domain_axioms: axiom_audit.total_domain_axioms,
            total_all_axioms: axiom_audit.total_all_axioms,
            total_theorems: axiom_audit.total_theorems,
            constructive_theorems: axiom_audit.constructive_theorems,
            conjecture_rows: axiom_audit.conjectures.len(),
            nonzero_axiom_rows: axiom_audit
                .conjectures
                .values()
                .filter(|row| row.axioms > 0)
                .count(),
            sha256: sha256_repo_artifact(AXIOM_AUDIT_PATH).expect("axiom audit sha256"),
        },
        source_sha256,
        lanes: AXIOM_AUDIT_EXPECTED_LANES
            .iter()
            .map(|lane| AxiomAuditLaunchLaneEvidence {
                id: lane.id.to_string(),
                description: match lane.id {
                    "aggregate_consistency" => "Aggregate consistency (data/axiom_audit.json)",
                    "live_row_reconciliation_and_constructive_claims" => {
                        "Zero domain/all axiom debt and zero nonzero conjecture rows"
                    }
                    _ => "",
                }
                .to_string(),
                status: "passed".to_string(),
            })
            .collect(),
    }
}

pub(super) fn tactic_report_row<'a>(
    report: &'a TacticParityReport,
    tactic: &str,
) -> &'a TacticParityRow {
    report
        .tactics
        .iter()
        .find(|row| row.tactic == tactic)
        .unwrap_or_else(|| panic!("tactic parity report missing `{tactic}`"))
}

pub(super) fn strict_reconstruction_row<'a>(
    report: &'a TacticParityReport,
    fragment: &str,
) -> &'a StrictReconstructionRow {
    report
        .strict_reconstruction
        .iter()
        .find(|row| row.fragment == fragment)
        .unwrap_or_else(|| panic!("strict reconstruction report missing `{fragment}`"))
}
