// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic parity report types and full-corpus contract constants.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct RustFirstToolingStatus {
    pub(crate) schema_version: &'static str,
    pub(crate) issue: IssueRef,
    pub(crate) owner_slot: &'static str,
    pub(crate) launch_ready: bool,
    pub(crate) overall_status: ToolMigrationStatus,
    pub(crate) counts: BTreeMap<ToolMigrationStatus, usize>,
    pub(crate) commands: Vec<PythonToolMigrationRow>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct PythonToolMigrationRow {
    pub(crate) id: &'static str,
    pub(crate) command: &'static str,
    pub(crate) source_artifact: &'static str,
    pub(crate) replacement_critical: bool,
    pub(crate) owner_slot: &'static str,
    pub(crate) issue: IssueRef,
    pub(crate) status: ToolMigrationStatus,
    pub(crate) planned_rust_surface: &'static str,
    pub(crate) removal_condition: &'static str,
    pub(crate) blocker: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityReport {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) launch_ready: bool,
    pub(crate) issues: Vec<IssueRef>,
    pub(crate) tactic_counts: BTreeMap<TacticParityStatus, usize>,
    pub(crate) reconstruction_counts: BTreeMap<StrictReconstructionStatus, usize>,
    pub(crate) lean4_vs_clean_tactic_counts: TacticParityCountArtifact,
    pub(crate) strict_solver_fragment_dashboard: StrictSolverFragmentDashboard,
    pub(crate) tactics: Vec<TacticParityRow>,
    pub(crate) strict_reconstruction: Vec<StrictReconstructionRow>,
}

impl TacticParityReport {
    pub(crate) fn current() -> Self {
        let tactics = tactic_parity_rows();
        let strict_solver_fragment_dashboard = StrictSolverFragmentDashboard::current();
        let lean4_vs_clean_tactic_counts =
            TacticParityCountArtifact::current(&tactics, &strict_solver_fragment_dashboard);
        let strict_reconstruction = strict_reconstruction_rows(&strict_solver_fragment_dashboard);
        let full_corpus_acceptance_ready = lean4_vs_clean_tactic_counts
            .full_lean4_corpus_coverage_claimed
            && lean4_vs_clean_tactic_counts.launch_readiness_claimed
            && lean4_vs_clean_tactic_counts.full_corpus_acceptance_gate == "accepted"
            && lean4_vs_clean_tactic_counts.full_corpus_acceptance_evidence_status == "accepted"
            && lean4_vs_clean_tactic_counts.full_corpus_acceptance_artifact_present
            && lean4_vs_clean_tactic_counts.full_corpus_acceptance_artifact_schema_validated
            && lean4_vs_clean_tactic_counts.full_corpus_acceptance_validator_present
            && !lean4_vs_clean_tactic_counts.full_corpus_fixture_counts_as_acceptance_evidence;
        let launch_ready = tactics
            .iter()
            .all(|row| row.lean4_parity_status == TacticParityStatus::ProofCarrying)
            && strict_reconstruction
                .iter()
                .all(|row| row.status == StrictReconstructionStatus::SupportedZeroTrust)
            && full_corpus_acceptance_ready;

        Self {
            schema_version: TACTIC_PARITY_SCHEMA_VERSION,
            generated_by: "clean replacement tactic-parity",
            launch_ready,
            issues: vec![
                IssueRef::new(3711, "Lean4 tactic parity matrix and corpus gates"),
                IssueRef::new(3712, "Strict solver-fragment reconstruction dashboard"),
            ],
            tactic_counts: count_tactic_status(&tactics),
            reconstruction_counts: count_reconstruction_status(&strict_reconstruction),
            lean4_vs_clean_tactic_counts,
            strict_solver_fragment_dashboard,
            tactics,
            strict_reconstruction,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityRow {
    pub(crate) tactic: &'static str,
    pub(crate) registered: bool,
    pub(crate) parser_surface: bool,
    pub(crate) proof_carrying: bool,
    pub(crate) fail_closed: bool,
    pub(crate) strict_zero_trust_tests: bool,
    pub(crate) trusted_arith_count: u32,
    pub(crate) trusted_ay_count: u32,
    pub(crate) lean4_parity_status: TacticParityStatus,
    pub(crate) evidence: &'static str,
    pub(crate) blocker: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityCountArtifact {
    pub(crate) schema_version: &'static str,
    pub(crate) status: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) source_artifact: &'static str,
    pub(crate) reproduction_command: &'static str,
    pub(crate) corpus: &'static str,
    pub(crate) coverage_scope: &'static str,
    pub(crate) full_lean4_corpus_coverage_claimed: bool,
    pub(crate) launch_readiness_claimed: bool,
    pub(crate) remaining_substantive_replacement_blocker: &'static str,
    pub(crate) full_corpus_acceptance_gate: &'static str,
    pub(crate) representative_generated_backing_satisfies_full_corpus_acceptance: bool,
    pub(crate) full_corpus_acceptance_evidence_status: &'static str,
    pub(crate) full_corpus_acceptance_artifact_required: &'static str,
    pub(crate) full_corpus_acceptance_artifact_present: bool,
    pub(crate) full_corpus_acceptance_artifact_schema_required: &'static str,
    pub(crate) full_corpus_acceptance_artifact_schema_validated: bool,
    pub(crate) full_corpus_acceptance_validator_required: &'static str,
    pub(crate) full_corpus_acceptance_validator_present: bool,
    pub(crate) full_corpus_input_discovery_command: &'static str,
    pub(crate) full_corpus_fixture_generator_command: &'static str,
    pub(crate) full_corpus_fixture_counts_as_acceptance_evidence: bool,
    pub(crate) full_corpus_fixture_acceptance_blocker: &'static str,
    pub(crate) full_corpus_acceptance_minimum_tactic_outcome_rows: u32,
    pub(crate) full_corpus_acceptance_tactic_outcome_row_contract: &'static str,
    pub(crate) full_corpus_acceptance_manifest_required_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_reviewer_evidence_required_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_fields_fingerprint_algorithm: &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_fields_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_required_summary_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_summary_fields_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_summary_fields_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_required_tactic_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_tactic_fields_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_required_evidence_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_evidence_fields_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_required_blocker_fields: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_blocker_fields_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_required_invariants: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_required_invariants_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_required_invariants_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_artifact_allowed_evidence_kinds: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_algorithm:
        &'static str,
    pub(crate) full_corpus_acceptance_artifact_allowed_evidence_kinds_fingerprint_sha256: String,
    pub(crate) full_corpus_acceptance_criteria_required: Vec<&'static str>,
    pub(crate) full_corpus_acceptance_criteria_fingerprint_algorithm: &'static str,
    pub(crate) full_corpus_acceptance_criteria_fingerprint_sha256: String,
    pub(crate) full_corpus_reviewer_evidence_required: Vec<&'static str>,
    pub(crate) full_corpus_reviewer_evidence_fingerprint_algorithm: &'static str,
    pub(crate) full_corpus_reviewer_evidence_fingerprint_sha256: String,
    pub(crate) summary: TacticParityCountSummary,
    pub(crate) tactics: Vec<TacticParityCountRow>,
    pub(crate) strict_solver_fragments: StrictSolverFragmentCountSummary,
}

pub(crate) const TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_REQUIRED: &[&str] = &[
    "full Lean4 tactic corpus enumeration with stable source fixture IDs",
    "generated Lean4-vs-clean execution results for every enumerated tactic fixture",
    "diagnostic and syntax parity review for tactic forms outside representative generated cases",
];
pub(crate) const TACTIC_FULL_CORPUS_REVIEWER_EVIDENCE_FINGERPRINT_ALGORITHM: &str =
    "sha256(evidence || LF) for each full_corpus_reviewer_evidence_required entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_GATE: &str =
    "blocked_until_full_corpus_reviewer_evidence_is_present_and_validated";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_EVIDENCE_STATUS: &str = "not_submitted";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED: &str =
    "reports/tactic-parity-full-corpus.json";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_SCHEMA_REQUIRED: &str =
    "clean-tactic-parity-full-corpus-v1";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_VALIDATOR_REQUIRED: &str =
    "clean replacement tactic-parity validate-full-corpus --report reports/tactic-parity-full-corpus.json --json";
pub(crate) const TACTIC_FULL_CORPUS_INPUT_DISCOVERY_COMMAND: &str =
    "clean replacement tactic-parity discover-full-corpus-inputs --json";
pub(crate) const TACTIC_FULL_CORPUS_FIXTURE_GENERATOR_COMMAND: &str =
    "clean replacement tactic-parity generate-full-corpus-fixture --output /tmp/tactic-parity-full-corpus.json --json";
pub(crate) const TACTIC_GENERATED_COUNT_RUNNER_ARTIFACT_CONTRACT: &str =
    "clean-tactic-generated-count-runner-artifact-v1";
pub(crate) const TACTIC_GENERATED_COUNT_SOURCE_CORPUS_SCHEMA_VERSION: &str =
    "clean-tactic-generated-count-source-corpus-v1";
pub(crate) const TACTIC_GENERATED_COUNT_FAIL_CLOSED_STATUS: &str =
    "fail-closed-missing-lean4-runner-artifact";
pub(crate) const TACTIC_FULL_CORPUS_FIXTURE_ACCEPTANCE_BLOCKER: &str =
    "Generated full-corpus schema fixtures are validator scaffolding only; they contain zero enumerated Lean4 tactic fixtures and cannot satisfy full-corpus acceptance.";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_MINIMUM_TACTIC_OUTCOME_ROWS: u32 = 1;
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_TACTIC_OUTCOME_ROW_CONTRACT: &str =
    "Every tactics[] row must include Lean4-vs-clean outcome fields: tactic, fixture_id, lean4_fixture, clean_fixture, lean4_result, clean_result, matched, evidence, reviewed_blocker.";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_MANIFEST_REQUIRED_FIELDS: &[&str] = &[
    "manifest_id",
    "source",
    "fixture_count",
    "generated_at",
    "source_digest_sha256",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_REVIEWER_EVIDENCE_REQUIRED_FIELDS: &[&str] = &[
    "reviewer",
    "reviewed_at",
    "scope",
    "decision",
    "notes",
    "manifest_id",
    "source_digest_sha256",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(field || LF) for each full_corpus_acceptance_artifact_required_fields entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_FIELDS: &[&str] = &[
    "schema_version",
    "generated_by",
    "source_corpus",
    "full_lean4_corpus_coverage_claimed",
    "launch_readiness_claimed",
    "summary",
    "tactics",
    "blockers",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(field || LF) for each full_corpus_acceptance_artifact_required_summary_fields entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_SUMMARY_FIELDS: &[&str] = &[
    "enumerated_fixture_total",
    "matched_fixture_total",
    "clean_gap_total",
    "reviewed_blocker_total",
    "unreviewed_blocker_total",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(field || LF) for each full_corpus_acceptance_artifact_required_tactic_fields entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_TACTIC_FIELDS: &[&str] = &[
    "tactic",
    "fixture_id",
    "lean4_fixture",
    "clean_fixture",
    "lean4_result",
    "clean_result",
    "matched",
    "evidence",
    "reviewed_blocker",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(field || LF) for each full_corpus_acceptance_artifact_required_evidence_fields entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_EVIDENCE_FIELDS: &[&str] = &[
    "evidence_id",
    "kind",
    "path",
    "command",
    "exit_status",
    "stdout_digest_sha256",
    "reviewed_at",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(field || LF) for each full_corpus_acceptance_artifact_required_blocker_fields entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_BLOCKER_FIELDS: &[&str] = &[
    "blocker_id",
    "fixture_id",
    "tactic",
    "category",
    "diagnostic",
    "lean4_behavior",
    "clean_behavior",
    "reviewer",
    "reviewed_at",
    "resolution_required",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS_FINGERPRINT_ALGORITHM: &str =
    "sha256(invariant || LF) for each full_corpus_acceptance_artifact_required_invariants entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED_INVARIANTS: &[&str] = &[
    "enumerated_fixture_total == matched_fixture_total + clean_gap_total",
    "clean_gap_total == reviewed_blocker_total + unreviewed_blocker_total",
    "full_lean4_corpus_coverage_claimed implies unreviewed_blocker_total == 0",
    "launch_readiness_claimed implies full_lean4_corpus_coverage_claimed",
    "each matched=false tactic row has reviewed_blocker or contributes to unreviewed_blocker_total",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS_FINGERPRINT_ALGORITHM: &str =
    "sha256(kind || LF) for each full_corpus_acceptance_artifact_allowed_evidence_kinds entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_ALLOWED_EVIDENCE_KINDS: &[&str] = &[
    "generated_fixture_execution",
    "rust_cli_json_report",
    "rust_unit_test",
    "pytest_validator",
    "reviewed_diagnostic_parity",
];
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_FINGERPRINT_ALGORITHM: &str =
    "sha256(criteria || LF) for each full_corpus_acceptance_criteria_required entry in emitted order";
pub(crate) const TACTIC_FULL_CORPUS_ACCEPTANCE_CRITERIA_REQUIRED: &[&str] = &[
    "every enumerated Lean4 tactic fixture has a matched clean result or a reviewed explicit blocker",
    "aggregate full-corpus matched/gap totals are recomputed from fixture rows",
    "representative generated backing remains a subset of the full-corpus evidence, not a replacement for it",
];
