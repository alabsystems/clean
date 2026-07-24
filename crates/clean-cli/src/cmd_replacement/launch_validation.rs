// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-soundness and deny-sorry launch evidence validation.

use super::*;

pub(crate) fn validate_kernel_soundness_launch_evidence(
    artifact: &KernelSoundnessLaunchEvidenceArtifact,
    baseline: &Lean4BaselineArtifact,
    expression_count: usize,
    expressions_sha256: &str,
) -> Result<(), String> {
    if artifact.schema_version != KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_SCHEMA_VERSION {
        return Err(format!(
            "schema_version {:?} != {KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_SCHEMA_VERSION}",
            artifact.schema_version
        ));
    }
    if artifact.generated_by != KERNEL_SOUNDNESS_RUST_GATE_COMMAND {
        return Err(format!(
            "generated_by {:?} != {KERNEL_SOUNDNESS_RUST_GATE_COMMAND}",
            artifact.generated_by
        ));
    }
    if artifact.gate_command != KERNEL_SOUNDNESS_RUST_GATE_COMMAND {
        return Err(format!(
            "gate_command {:?} != {KERNEL_SOUNDNESS_RUST_GATE_COMMAND}",
            artifact.gate_command
        ));
    }
    if artifact.generated_at.trim().is_empty() {
        return Err("generated_at is empty".to_string());
    }
    if artifact.status != "passed" {
        return Err(format!("status {:?} is not passed", artifact.status));
    }
    if artifact.summary.expected_steps != KERNEL_SOUNDNESS_EXPECTED_STEPS {
        return Err(format!(
            "summary.expected_steps={} != {KERNEL_SOUNDNESS_EXPECTED_STEPS}",
            artifact.summary.expected_steps
        ));
    }
    if artifact.summary.steps != KERNEL_SOUNDNESS_EXPECTED_STEPS
        || artifact.summary.passed != KERNEL_SOUNDNESS_EXPECTED_STEPS
        || artifact.summary.failed != 0
    {
        return Err(format!(
            "summary must record {KERNEL_SOUNDNESS_EXPECTED_STEPS} steps, {KERNEL_SOUNDNESS_EXPECTED_STEPS} passed, 0 failed; got steps={}, passed={}, failed={}",
            artifact.summary.steps, artifact.summary.passed, artifact.summary.failed
        ));
    }
    if artifact.summary.steps as usize != artifact.lanes.len() {
        return Err(format!(
            "summary.steps={} but lanes length is {}",
            artifact.summary.steps,
            artifact.lanes.len()
        ));
    }

    let differential = &artifact.kernel_differential;
    if differential.baseline_path != LEAN4_BASELINE_PATH {
        return Err(format!(
            "kernel_differential.baseline_path {:?} != {LEAN4_BASELINE_PATH}",
            differential.baseline_path
        ));
    }
    if differential.expressions_path != LEAN4_EXPRESSIONS_PATH {
        return Err(format!(
            "kernel_differential.expressions_path {:?} != {LEAN4_EXPRESSIONS_PATH}",
            differential.expressions_path
        ));
    }
    if differential.baseline_schema_version != baseline.schema_version {
        return Err(format!(
            "kernel_differential.baseline_schema_version={} != current {}",
            differential.baseline_schema_version, baseline.schema_version
        ));
    }
    if differential.normalization_version != baseline.normalization_version {
        return Err(format!(
            "kernel_differential.normalization_version={} != current {}",
            differential.normalization_version, baseline.normalization_version
        ));
    }
    if differential.baseline_cases != baseline.cases.len() {
        return Err(format!(
            "kernel_differential.baseline_cases={} != current {}",
            differential.baseline_cases,
            baseline.cases.len()
        ));
    }
    if differential.expression_count != expression_count {
        return Err(format!(
            "kernel_differential.expression_count={} != current {expression_count}",
            differential.expression_count
        ));
    }
    if differential.expressions_sha256 != expressions_sha256 {
        return Err(format!(
            "kernel_differential.expressions_sha256 {} != current {expressions_sha256}",
            differential.expressions_sha256
        ));
    }
    if baseline.expressions_sha256 != expressions_sha256 {
        return Err(format!(
            "current baseline expressions_sha256 {} != current expressions {expressions_sha256}",
            baseline.expressions_sha256
        ));
    }

    let baseline_sha =
        sha256_repo_artifact(LEAN4_BASELINE_PATH).map_err(|error| error.to_string())?;
    if differential.baseline_sha256 != baseline_sha {
        return Err(format!(
            "kernel_differential.baseline_sha256 {} != current {baseline_sha}",
            differential.baseline_sha256
        ));
    }
    let expressions_file_sha =
        sha256_repo_artifact(LEAN4_EXPRESSIONS_PATH).map_err(|error| error.to_string())?;
    if differential.expressions_file_sha256 != expressions_file_sha {
        return Err(format!(
            "kernel_differential.expressions_file_sha256 {} != current {expressions_file_sha}",
            differential.expressions_file_sha256
        ));
    }

    for path in [
        TRUST_CORE_RUST_SOURCE_PATH,
        LEAN4_BASELINE_PATH,
        LEAN4_EXPRESSIONS_PATH,
    ] {
        let expected_sha = sha256_repo_artifact(path).map_err(|error| error.to_string())?;
        match artifact.source_sha256.get(path) {
            Some(actual_sha) if actual_sha == &expected_sha => {}
            Some(actual_sha) => {
                return Err(format!(
                    "source_sha256[{path}] {actual_sha} != current {expected_sha}"
                ));
            }
            None => return Err(format!("source_sha256 is missing {path}")),
        }
    }

    if artifact.source_sha256.len() != 3 {
        return Err(format!(
            "source_sha256 must contain exactly 3 source artifacts, got {}",
            artifact.source_sha256.len()
        ));
    }

    let lanes: BTreeMap<&str, &KernelSoundnessLaunchLaneEvidence> = artifact
        .lanes
        .iter()
        .map(|lane| (lane.id.as_str(), lane))
        .collect();
    if lanes.len() != artifact.lanes.len() {
        return Err("lanes contain duplicate ids".to_string());
    }
    if lanes.len() != KERNEL_SOUNDNESS_EXPECTED_LANES.len() {
        return Err(format!(
            "lanes length {} != expected {}",
            lanes.len(),
            KERNEL_SOUNDNESS_EXPECTED_LANES.len()
        ));
    }
    for expected in KERNEL_SOUNDNESS_EXPECTED_LANES {
        let Some(lane) = lanes.get(expected.id) else {
            return Err(format!("missing lane {}", expected.id));
        };
        if lane.status != "passed" {
            return Err(format!(
                "lane {} status {:?} is not passed",
                expected.id, lane.status
            ));
        }
        if lane.expected_tests != expected.expected_tests {
            return Err(format!(
                "lane {} expected_tests {:?} != {:?}",
                expected.id, lane.expected_tests, expected.expected_tests
            ));
        }
        if lane.expected_output.as_deref() != expected.expected_output {
            return Err(format!(
                "lane {} expected_output {:?} != {:?}",
                expected.id, lane.expected_output, expected.expected_output
            ));
        }
        if !lane.matched_expected_count {
            return Err(format!(
                "lane {} did not match its expected output count",
                expected.id
            ));
        }
        if !lane.matched_expected_output {
            return Err(format!(
                "lane {} did not match its expected output text",
                expected.id
            ));
        }
    }

    Ok(())
}

pub(crate) fn validate_deny_sorry_launch_evidence(
    artifact: &DenySorryLaunchEvidenceArtifact,
    ratchet: &UncheckedDeclRatchetArtifact,
) -> Result<(), String> {
    if artifact.schema_version != DENY_SORRY_LAUNCH_EVIDENCE_SCHEMA_VERSION {
        return Err(format!(
            "schema_version {:?} != {DENY_SORRY_LAUNCH_EVIDENCE_SCHEMA_VERSION}",
            artifact.schema_version
        ));
    }
    if artifact.generated_by != DENY_SORRY_RUST_GATE_COMMAND {
        return Err(format!(
            "generated_by {:?} != {DENY_SORRY_RUST_GATE_COMMAND}",
            artifact.generated_by
        ));
    }
    if artifact.gate_command != DENY_SORRY_RUST_GATE_COMMAND {
        return Err(format!(
            "gate_command {:?} != {DENY_SORRY_RUST_GATE_COMMAND}",
            artifact.gate_command
        ));
    }
    if artifact.generated_at.trim().is_empty() {
        return Err("generated_at is empty".to_string());
    }
    if artifact.status != "passed" {
        return Err(format!("status {:?} is not passed", artifact.status));
    }
    if artifact.summary.expected_steps != DENY_SORRY_EXPECTED_STEPS {
        return Err(format!(
            "summary.expected_steps={} != {DENY_SORRY_EXPECTED_STEPS}",
            artifact.summary.expected_steps
        ));
    }
    if artifact.summary.steps != DENY_SORRY_EXPECTED_STEPS
        || artifact.summary.passed != DENY_SORRY_EXPECTED_STEPS
        || artifact.summary.failed != 0
    {
        return Err(format!(
            "summary must record {DENY_SORRY_EXPECTED_STEPS} steps, {DENY_SORRY_EXPECTED_STEPS} passed, 0 failed; got steps={}, passed={}, failed={}",
            artifact.summary.steps, artifact.summary.passed, artifact.summary.failed
        ));
    }
    if artifact.summary.steps as usize != artifact.lanes.len() {
        return Err(format!(
            "summary.steps={} but lanes length is {}",
            artifact.summary.steps,
            artifact.lanes.len()
        ));
    }
    if artifact.ratchet.path != UNCHECKED_DECL_RATCHET_PATH {
        return Err(format!(
            "ratchet.path {:?} != {UNCHECKED_DECL_RATCHET_PATH}",
            artifact.ratchet.path
        ));
    }
    if artifact.ratchet.add_decl_structural_count != ratchet.add_decl_structural_count
        || artifact.ratchet.add_decl_unchecked_count != ratchet.add_decl_unchecked_count
    {
        return Err(format!(
            "ratchet counts {}/{} do not match current {}/{}",
            artifact.ratchet.add_decl_structural_count,
            artifact.ratchet.add_decl_unchecked_count,
            ratchet.add_decl_structural_count,
            ratchet.add_decl_unchecked_count
        ));
    }
    if ratchet.add_decl_structural_count != 0 || ratchet.add_decl_unchecked_count != 0 {
        return Err(format!(
            "current ratchet is not closed at 0/0: structural={}, unchecked={}",
            ratchet.add_decl_structural_count, ratchet.add_decl_unchecked_count
        ));
    }

    let ratchet_sha =
        sha256_repo_artifact(UNCHECKED_DECL_RATCHET_PATH).map_err(|error| error.to_string())?;
    if artifact.ratchet.sha256 != ratchet_sha {
        return Err(format!(
            "ratchet sha256 {} != current {ratchet_sha}",
            artifact.ratchet.sha256
        ));
    }

    for path in [TRUST_CORE_RUST_SOURCE_PATH, UNCHECKED_DECL_RATCHET_PATH] {
        let expected_sha = sha256_repo_artifact(path).map_err(|error| error.to_string())?;
        match artifact.source_sha256.get(path) {
            Some(actual_sha) if actual_sha == &expected_sha => {}
            Some(actual_sha) => {
                return Err(format!(
                    "source_sha256[{path}] {actual_sha} != current {expected_sha}"
                ));
            }
            None => return Err(format!("source_sha256 is missing {path}")),
        }
    }

    if artifact.source_sha256.len() != 2 {
        return Err(format!(
            "source_sha256 must contain exactly 2 source artifacts, got {}",
            artifact.source_sha256.len()
        ));
    }

    let lanes: BTreeMap<&str, &DenySorryLaunchLaneEvidence> = artifact
        .lanes
        .iter()
        .map(|lane| (lane.id.as_str(), lane))
        .collect();
    if lanes.len() != artifact.lanes.len() {
        return Err("lanes contain duplicate ids".to_string());
    }
    if lanes.len() != DENY_SORRY_EXPECTED_LANES.len() {
        return Err(format!(
            "lanes length {} != expected {}",
            lanes.len(),
            DENY_SORRY_EXPECTED_LANES.len()
        ));
    }
    for expected in DENY_SORRY_EXPECTED_LANES {
        let Some(lane) = lanes.get(expected.id) else {
            return Err(format!("missing lane {}", expected.id));
        };
        if lane.status != "passed" {
            return Err(format!(
                "lane {} status {:?} is not passed",
                expected.id, lane.status
            ));
        }
        if lane.expected_tests != expected.expected_tests {
            return Err(format!(
                "lane {} expected_tests {:?} != {:?}",
                expected.id, lane.expected_tests, expected.expected_tests
            ));
        }
        if !lane.matched_expected_count {
            return Err(format!(
                "lane {} did not match its expected output count",
                expected.id
            ));
        }
    }

    Ok(())
}
