// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic-parity full-corpus input discovery.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusInputDiscovery {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) registry_path: String,
    pub(crate) registry_present: bool,
    pub(crate) registry_valid: bool,
    pub(crate) full_corpus_artifact_required: &'static str,
    pub(crate) full_corpus_artifact_present: bool,
    pub(crate) representative_generated_backing_counts_as_acceptance_evidence: bool,
    pub(crate) full_lean4_corpus_coverage_claimed: bool,
    pub(crate) launch_readiness_claimed: bool,
    pub(crate) lane_count: usize,
    pub(crate) expected_real_artifact_count: usize,
    pub(crate) discovered_real_artifact_count: usize,
    pub(crate) missing_real_artifact_count: usize,
    pub(crate) missing_outcome_evidence_count: usize,
    pub(crate) acceptance_evidence_candidate: bool,
    pub(crate) discovery_status: &'static str,
    pub(crate) checks: Vec<ReplacementReportValidationCheck>,
    pub(crate) blockers: Vec<String>,
    pub(crate) lanes: Vec<TacticParityFullCorpusInputLane>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct TacticParityFullCorpusInputLane {
    pub(crate) tactic_lane: String,
    pub(crate) bucket: String,
    pub(crate) source_corpus_path: String,
    pub(crate) source_corpus_present: bool,
    pub(crate) source_corpus_valid: bool,
    pub(crate) source_corpus_sha256: Option<String>,
    pub(crate) source_case_count: usize,
    pub(crate) source_case_ids: Vec<String>,
    pub(crate) runner_path: String,
    pub(crate) runner_present: bool,
    pub(crate) runner_command: String,
    pub(crate) expected_generated_count_artifact_path: String,
    pub(crate) discovered_generated_count_artifact_paths: Vec<String>,
    pub(crate) real_generated_count_artifact_present: bool,
    pub(crate) missing_generated_count_evidence: bool,
    pub(crate) expected_full_corpus_outcome_artifact_path: &'static str,
    pub(crate) missing_full_corpus_outcome_evidence: bool,
    pub(crate) parity_status: String,
    pub(crate) readiness_effect: String,
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct TacticParityGeneratedCountManifest {
    pub(crate) tactic_lane: String,
    pub(crate) bucket: String,
    pub(crate) generated: bool,
    pub(crate) source_corpus_path: String,
    pub(crate) runner_path: String,
    pub(crate) runner_command: String,
    pub(crate) runner_artifact_contract: String,
    pub(crate) expected_lean4_runner_artifact_path: String,
    pub(crate) missing_runner_status: String,
    pub(crate) parity_status: String,
    pub(crate) readiness_effect: String,
}

#[derive(Debug, Clone)]
pub(crate) struct TacticParitySourceCorpusDiscovery {
    pub(crate) present: bool,
    pub(crate) valid: bool,
    pub(crate) sha256: Option<String>,
    pub(crate) case_ids: Vec<String>,
    pub(crate) blockers: Vec<String>,
}

impl TacticParityFullCorpusInputDiscovery {
    pub(crate) fn from_registry_path(registry: &Path) -> Self {
        let registry_path = registry.display().to_string();
        let mut checks = Vec::new();
        let mut check_failures = Vec::new();
        let mut blockers = Vec::new();
        let mut lanes = Vec::new();
        // A `{"stub": true}` placeholder is not outcome evidence; counting it
        // as present would launder the stub into full-corpus acceptance.
        let full_corpus_artifact_present = fs::read_to_string(repo_artifact_path_dynamic(
            TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED,
        ))
        .map(|contents| !is_stub_evidence(&contents))
        .unwrap_or(false);

        let registry_raw = fs::read_to_string(registry);
        let registry_present = registry_raw.is_ok();
        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "registry-readable",
            registry_present,
            if registry_present {
                format!("read {registry_path}")
            } else {
                format!("failed to read {registry_path}")
            },
        );

        let manifests = match registry_raw {
            Ok(raw) => parse_tactic_generated_count_manifests(&raw),
            Err(error) => Err(vec![format!("failed to read {registry_path}: {error}")]),
        };
        let registry_valid = manifests.is_ok();
        let manifests = match manifests {
            Ok(manifests) => manifests,
            Err(errors) => {
                blockers.extend(errors);
                Vec::new()
            }
        };
        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "registry-generated-count-manifests",
            registry_valid && !manifests.is_empty(),
            if registry_valid && !manifests.is_empty() {
                format!("found {} generated-count manifests", manifests.len())
            } else {
                "missing valid generated_count_manifests".to_owned()
            },
        );

        for manifest in manifests {
            let corpus = discover_tactic_source_corpus(&manifest);
            let runner_present = repo_artifact_path_dynamic(&manifest.runner_path).is_file();
            let discovered_artifacts = discover_tactic_generated_count_artifacts(
                &manifest.expected_lean4_runner_artifact_path,
            );
            let real_artifact_present = !discovered_artifacts.is_empty();
            let mut lane_blockers = corpus.blockers.clone();

            if !runner_present {
                lane_blockers.push(format!(
                    "{} runner_path missing: {}",
                    manifest.tactic_lane, manifest.runner_path
                ));
            }
            if !real_artifact_present {
                lane_blockers.push(format!(
                    "{} missing generated-count artifact matching {}",
                    manifest.tactic_lane, manifest.expected_lean4_runner_artifact_path
                ));
            }
            if !full_corpus_artifact_present {
                lane_blockers.push(format!(
                    "{} missing full-corpus outcome rows in {}",
                    manifest.tactic_lane, TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED
                ));
            }
            if manifest.generated {
                lane_blockers.push(format!(
                    "{} generated-count manifest must remain generated: false until real artifacts exist",
                    manifest.tactic_lane
                ));
            }
            if manifest.runner_artifact_contract != TACTIC_GENERATED_COUNT_RUNNER_ARTIFACT_CONTRACT
            {
                lane_blockers.push(format!(
                    "{} runner_artifact_contract must be {}",
                    manifest.tactic_lane, TACTIC_GENERATED_COUNT_RUNNER_ARTIFACT_CONTRACT
                ));
            }
            if manifest.missing_runner_status != TACTIC_GENERATED_COUNT_FAIL_CLOSED_STATUS {
                lane_blockers.push(format!(
                    "{} missing_runner_status must be {}",
                    manifest.tactic_lane, TACTIC_GENERATED_COUNT_FAIL_CLOSED_STATUS
                ));
            }

            blockers.extend(lane_blockers.iter().cloned());
            lanes.push(TacticParityFullCorpusInputLane {
                tactic_lane: manifest.tactic_lane,
                bucket: manifest.bucket,
                source_corpus_path: manifest.source_corpus_path,
                source_corpus_present: corpus.present,
                source_corpus_valid: corpus.valid,
                source_corpus_sha256: corpus.sha256,
                source_case_count: corpus.case_ids.len(),
                source_case_ids: corpus.case_ids,
                runner_path: manifest.runner_path,
                runner_present,
                runner_command: manifest.runner_command,
                expected_generated_count_artifact_path: manifest
                    .expected_lean4_runner_artifact_path,
                discovered_generated_count_artifact_paths: discovered_artifacts,
                real_generated_count_artifact_present: real_artifact_present,
                missing_generated_count_evidence: !real_artifact_present,
                expected_full_corpus_outcome_artifact_path:
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED,
                missing_full_corpus_outcome_evidence: !full_corpus_artifact_present,
                parity_status: manifest.parity_status,
                readiness_effect: manifest.readiness_effect,
                blockers: lane_blockers,
            });
        }

        let expected_real_artifact_count = lanes.len();
        let discovered_real_artifact_count = lanes
            .iter()
            .filter(|lane| lane.real_generated_count_artifact_present)
            .count();
        let missing_real_artifact_count = lanes
            .iter()
            .filter(|lane| lane.missing_generated_count_evidence)
            .count();
        let missing_outcome_evidence_count = lanes
            .iter()
            .filter(|lane| lane.missing_full_corpus_outcome_evidence)
            .count();
        let corpus_manifests_valid = !lanes.is_empty()
            && lanes
                .iter()
                .all(|lane| lane.source_corpus_present && lane.source_corpus_valid);
        let all_runners_present = !lanes.is_empty() && lanes.iter().all(|lane| lane.runner_present);

        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "source-corpus-manifests",
            corpus_manifests_valid,
            if corpus_manifests_valid {
                "all generated-count source corpora are present and valid".to_owned()
            } else {
                "one or more generated-count source corpora are missing or invalid".to_owned()
            },
        );
        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "generated-count-runner-paths",
            all_runners_present,
            if all_runners_present {
                "all generated-count runner paths exist".to_owned()
            } else {
                "one or more generated-count runner paths are missing".to_owned()
            },
        );
        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "real-generated-count-artifacts",
            missing_real_artifact_count == 0 && expected_real_artifact_count > 0,
            if missing_real_artifact_count == 0 && expected_real_artifact_count > 0 {
                "all expected real generated-count artifacts are present".to_owned()
            } else {
                format!(
                    "{} of {} expected real generated-count artifacts are missing",
                    missing_real_artifact_count, expected_real_artifact_count
                )
            },
        );
        push_report_validation_check(
            &mut checks,
            &mut check_failures,
            "full-corpus-outcome-artifact",
            full_corpus_artifact_present,
            if full_corpus_artifact_present {
                format!("found {}", TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED)
            } else {
                format!(
                    "{} is absent; discovery cannot count representative fixtures as acceptance evidence",
                    TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED
                )
            },
        );

        let acceptance_evidence_candidate = false;
        let discovery_status = if !registry_valid {
            "invalid_registry"
        } else if missing_real_artifact_count == 0
            && missing_outcome_evidence_count == 0
            && expected_real_artifact_count > 0
        {
            "inputs_present_pending_full_corpus_validation"
        } else {
            "blocked_missing_real_artifacts"
        };

        Self {
            schema_version: "clean-tactic-parity-full-corpus-input-discovery-v1",
            generated_by: "clean replacement tactic-parity discover-full-corpus-inputs",
            registry_path,
            registry_present,
            registry_valid,
            full_corpus_artifact_required: TACTIC_FULL_CORPUS_ACCEPTANCE_ARTIFACT_REQUIRED,
            full_corpus_artifact_present,
            representative_generated_backing_counts_as_acceptance_evidence: false,
            full_lean4_corpus_coverage_claimed: false,
            launch_readiness_claimed: false,
            lane_count: lanes.len(),
            expected_real_artifact_count,
            discovered_real_artifact_count,
            missing_real_artifact_count,
            missing_outcome_evidence_count,
            acceptance_evidence_candidate,
            discovery_status,
            checks,
            blockers,
            lanes,
        }
    }
}
