// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Axiom-audit launch validation, gate preflight, and ratchet checks.

use super::*;

pub(crate) fn validate_axiom_audit_launch_evidence(
    artifact: &AxiomAuditLaunchEvidenceArtifact,
    axiom_audit: &AxiomAuditArtifact,
) -> Result<(), String> {
    if artifact.schema_version != AXIOM_AUDIT_LAUNCH_EVIDENCE_SCHEMA_VERSION {
        return Err(format!(
            "schema_version {:?} != {AXIOM_AUDIT_LAUNCH_EVIDENCE_SCHEMA_VERSION}",
            artifact.schema_version
        ));
    }
    if artifact.generated_by != AXIOM_AUDIT_GATE_COMMAND {
        return Err(format!(
            "generated_by {:?} != {AXIOM_AUDIT_GATE_COMMAND}",
            artifact.generated_by
        ));
    }
    if artifact.gate_command != AXIOM_AUDIT_GATE_COMMAND {
        return Err(format!(
            "gate_command {:?} != {AXIOM_AUDIT_GATE_COMMAND}",
            artifact.gate_command
        ));
    }
    if artifact.generated_at.trim().is_empty() {
        return Err("generated_at is empty".to_string());
    }
    if artifact.status != "passed" {
        return Err(format!("status {:?} is not passed", artifact.status));
    }
    if artifact.summary.expected_steps != AXIOM_AUDIT_EXPECTED_STEPS {
        return Err(format!(
            "summary.expected_steps={} != {AXIOM_AUDIT_EXPECTED_STEPS}",
            artifact.summary.expected_steps
        ));
    }
    if artifact.summary.steps != AXIOM_AUDIT_EXPECTED_STEPS
        || artifact.summary.passed != AXIOM_AUDIT_EXPECTED_STEPS
        || artifact.summary.failed != 0
    {
        return Err(format!(
            "summary must record {AXIOM_AUDIT_EXPECTED_STEPS} steps, {AXIOM_AUDIT_EXPECTED_STEPS} passed, 0 failed; got steps={}, passed={}, failed={}",
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
    if artifact.axiom_audit.path != AXIOM_AUDIT_PATH {
        return Err(format!(
            "axiom_audit.path {:?} != {AXIOM_AUDIT_PATH}",
            artifact.axiom_audit.path
        ));
    }
    if artifact.axiom_audit.total_domain_axioms != axiom_audit.total_domain_axioms
        || artifact.axiom_audit.total_all_axioms != axiom_audit.total_all_axioms
        || artifact.axiom_audit.total_theorems != axiom_audit.total_theorems
        || artifact.axiom_audit.constructive_theorems != axiom_audit.constructive_theorems
        || artifact.axiom_audit.conjecture_rows != axiom_audit.conjectures.len()
    {
        return Err(format!(
            "axiom-audit evidence counts do not match current {}",
            AXIOM_AUDIT_PATH
        ));
    }

    let current_nonzero_rows = axiom_audit
        .conjectures
        .values()
        .filter(|row| row.axioms > 0)
        .count();
    if artifact.axiom_audit.nonzero_axiom_rows != current_nonzero_rows {
        return Err(format!(
            "axiom_audit.nonzero_axiom_rows={} != current {}",
            artifact.axiom_audit.nonzero_axiom_rows, current_nonzero_rows
        ));
    }
    if axiom_audit.total_domain_axioms != 0
        || axiom_audit.total_all_axioms != 0
        || current_nonzero_rows != 0
    {
        return Err(format!(
            "current axiom audit is not closed at 0/0 with zero nonzero rows: total_domain_axioms={}, total_all_axioms={}, nonzero_axiom_rows={}",
            axiom_audit.total_domain_axioms, axiom_audit.total_all_axioms, current_nonzero_rows
        ));
    }

    let audit_sha = sha256_repo_artifact(AXIOM_AUDIT_PATH).map_err(|error| error.to_string())?;
    if artifact.axiom_audit.sha256 != audit_sha {
        return Err(format!(
            "axiom_audit sha256 {} != current {audit_sha}",
            artifact.axiom_audit.sha256
        ));
    }

    for path in [AXIOM_AUDIT_RUST_SOURCE_PATH, AXIOM_AUDIT_PATH] {
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

    let lanes: BTreeMap<&str, &AxiomAuditLaunchLaneEvidence> = artifact
        .lanes
        .iter()
        .map(|lane| (lane.id.as_str(), lane))
        .collect();
    if lanes.len() != artifact.lanes.len() {
        return Err("lanes contain duplicate ids".to_string());
    }
    if lanes.len() != AXIOM_AUDIT_EXPECTED_LANES.len() {
        return Err(format!(
            "lanes length {} != expected {}",
            lanes.len(),
            AXIOM_AUDIT_EXPECTED_LANES.len()
        ));
    }
    for expected in AXIOM_AUDIT_EXPECTED_LANES {
        let Some(lane) = lanes.get(expected.id) else {
            return Err(format!("missing lane {}", expected.id));
        };
        if lane.status != "passed" {
            return Err(format!(
                "lane {} status {:?} is not passed",
                expected.id, lane.status
            ));
        }
    }

    Ok(())
}

pub(crate) fn validate_kernel_differential_artifacts(
    baseline: &Lean4BaselineArtifact,
    expression_count: usize,
    expressions_sha256: &str,
) -> Result<(), ReplacementError> {
    if baseline.cases.len() != expression_count {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{LEAN4_BASELINE_PATH} has {} cases but {LEAN4_EXPRESSIONS_PATH} has {expression_count} active expressions",
                baseline.cases.len()
            ),
        });
    }

    if baseline.expressions_sha256 != expressions_sha256 {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{LEAN4_BASELINE_PATH} expects expressions_sha256={} but {LEAN4_EXPRESSIONS_PATH} hashes to {expressions_sha256}",
                baseline.expressions_sha256
            ),
        });
    }

    Ok(())
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn validate_kernel_soundness_gate_preflight() -> Result<(), ReplacementError> {
    let source = read_repo_artifact(KERNEL_SOUNDNESS_GATE_PATH)?;
    validate_kernel_soundness_gate_preflight_source(&source)
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn validate_kernel_soundness_gate_preflight_source(
    source: &str,
) -> Result<(), ReplacementError> {
    for marker in KERNEL_GATE_PREFLIGHT_MARKERS {
        if !source.contains(marker) {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{KERNEL_SOUNDNESS_GATE_PATH} is missing hardened differential preflight marker `{marker}`"
                ),
            });
        }
    }

    Ok(())
}

pub(crate) fn zero_trust_gate_rows(
    ratchet: &UncheckedDeclRatchetArtifact,
    axiom_audit: &AxiomAuditArtifact,
    kernel_soundness_launch_evidence: &KernelSoundnessLaunchEvidence,
    deny_sorry_launch_evidence: &DenySorryLaunchEvidence,
    axiom_audit_launch_evidence: &AxiomAuditLaunchEvidence,
) -> Vec<ZeroTrustGateRow> {
    let (kernel_status, kernel_reason) = if kernel_soundness_launch_evidence.is_passed() {
        (
            ZeroTrustGateStatus::Passed,
            "fresh kernel soundness launch-gate evidence passed.".to_string(),
        )
    } else {
        (
            ZeroTrustGateStatus::PendingEvidence,
            format!(
                "kernel differential artifacts are current, but replacement status requires a fresh kernel soundness gate pass: {}",
                kernel_soundness_launch_evidence.summary()
            ),
        )
    };
    let fallback_debt = ratchet
        .add_decl_structural_count
        .saturating_add(ratchet.add_decl_unchecked_count);
    let (fallback_status, fallback_reason) = if fallback_debt == 0 {
        if deny_sorry_launch_evidence.is_passed() {
            (
                ZeroTrustGateStatus::Passed,
                "unchecked-decl ratchet is zero and fresh DENY_SORRY launch evidence passed."
                    .to_string(),
            )
        } else {
            (
                ZeroTrustGateStatus::PendingEvidence,
                "unchecked-decl ratchet is zero, but DENY_SORRY still needs a fresh launch-gate evidence artifact before replacement readiness."
                    .to_string(),
            )
        }
    } else {
        (
            ZeroTrustGateStatus::Blocked,
            "unchecked-decl ratchet records remaining structural/unchecked trusted fallback callsites; replacement scope stays blocked."
                .to_string(),
        )
    };
    let axiom_audit_debt = axiom_audit
        .total_domain_axioms
        .saturating_add(axiom_audit.total_all_axioms);
    let (axiom_audit_status, axiom_audit_reason) = if axiom_audit_debt == 0 {
        if axiom_audit_launch_evidence.is_passed() {
            (
                ZeroTrustGateStatus::Passed,
                "checked-in axiom audit records zero axiom debt and fresh axiom-audit launch evidence passed."
                    .to_string(),
            )
        } else {
            (
                ZeroTrustGateStatus::PendingEvidence,
                format!(
                    "checked-in axiom audit records zero axiom debt, but replacement status requires a fresh axiom-audit gate pass: {}",
                    axiom_audit_launch_evidence.summary()
                ),
            )
        }
    } else {
        (
            ZeroTrustGateStatus::Blocked,
            "checked-in axiom audit records remaining domain/all axiom debt; axiom-audit release gate stays blocked."
                .to_string(),
        )
    };

    vec![
        ZeroTrustGateRow {
            id: "kernel-soundness",
            issue: IssueRef::new(
                3699,
                "Proof-system replacement certification and zero-trust gates",
            ),
            debt_class: ZeroTrustDebtClass::KernelSoundness,
            required_for_launch: true,
            command: KERNEL_SOUNDNESS_RUST_GATE_COMMAND,
            source_artifacts: vec![
                TRUST_CORE_RUST_SOURCE_PATH,
                LEAN4_BASELINE_PATH,
                LEAN4_EXPRESSIONS_PATH,
            ],
            active_debt_count: 0,
            evidence_summary: format!(
                "kernel differential artifacts are current; {}",
                kernel_soundness_launch_evidence.summary()
            ),
            status: kernel_status,
            fail_closed_reason: kernel_reason,
        },
        ZeroTrustGateRow {
            id: "deny-sorry",
            issue: IssueRef::new(
                3705,
                "Zero-trust gate forbids sorryAx and trusted fallback constructors",
            ),
            debt_class: ZeroTrustDebtClass::SorryAndTrustedFallback,
            required_for_launch: true,
            command: DENY_SORRY_RUST_GATE_COMMAND,
            source_artifacts: vec![TRUST_CORE_RUST_SOURCE_PATH, UNCHECKED_DECL_RATCHET_PATH],
            active_debt_count: fallback_debt,
            evidence_summary: format!(
                "add_decl_structural_count={}, add_decl_unchecked_count={}, total={fallback_debt}; {}",
                ratchet.add_decl_structural_count,
                ratchet.add_decl_unchecked_count,
                deny_sorry_launch_evidence.summary()
            ),
            status: fallback_status,
            fail_closed_reason: fallback_reason,
        },
        ZeroTrustGateRow {
            id: "axiom-audit",
            issue: IssueRef::new(
                3699,
                "Proof-system replacement certification and zero-trust gates",
            ),
            debt_class: ZeroTrustDebtClass::AxiomAudit,
            required_for_launch: true,
            command: AXIOM_AUDIT_GATE_COMMAND,
            source_artifacts: vec![
                AXIOM_AUDIT_RUST_SOURCE_PATH,
                AXIOM_AUDIT_PATH,
                AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH,
                VERIFICATION_AUDIT_PATH,
            ],
            active_debt_count: axiom_audit_debt,
            evidence_summary: format!(
                "total_domain_axioms={}, total_all_axioms={}, total={axiom_audit_debt}; {}",
                axiom_audit.total_domain_axioms,
                axiom_audit.total_all_axioms,
                axiom_audit_launch_evidence.summary()
            ),
            status: axiom_audit_status,
            fail_closed_reason: axiom_audit_reason,
        },
    ]
}

pub(crate) fn validate_unchecked_decl_ratchet(
    ratchet: &UncheckedDeclRatchetArtifact,
) -> Result<(), ReplacementError> {
    for entry in &ratchet.files {
        if entry.method != "add_decl_structural" && entry.method != "add_decl_unchecked" {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{UNCHECKED_DECL_RATCHET_PATH} contains unsupported unchecked-decl method `{}`",
                    entry.method
                ),
            });
        }

        if entry.count == 0 {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{UNCHECKED_DECL_RATCHET_PATH} contains zero-count unchecked-decl row for `{}`",
                    entry.method
                ),
            });
        }
    }

    for (sites, expected_method) in [
        (
            &ratchet.add_decl_structural_production_sites,
            "add_decl_structural",
        ),
        (
            &ratchet.add_decl_unchecked_production_sites,
            "add_decl_unchecked",
        ),
    ] {
        for site in sites {
            if site.method != expected_method {
                return Err(ReplacementError::StaleTrustCoreArtifact {
                    message: format!(
                        "{UNCHECKED_DECL_RATCHET_PATH} production site `{}` records method `{}` under {expected_method}_production_sites",
                        site.file, site.method
                    ),
                });
            }
            if site.trust.trim().is_empty() {
                return Err(ReplacementError::StaleTrustCoreArtifact {
                    message: format!(
                        "{UNCHECKED_DECL_RATCHET_PATH} production site `{}` is missing its SOUNDNESS trust justification",
                        site.file
                    ),
                });
            }
            if site.occurrences == Some(0) {
                return Err(ReplacementError::StaleTrustCoreArtifact {
                    message: format!(
                        "{UNCHECKED_DECL_RATCHET_PATH} production site `{}` records zero occurrences",
                        site.file
                    ),
                });
            }
        }
    }

    let site_sum = |sites: &[UncheckedDeclProductionSite]| -> u32 {
        sites.iter().map(|site| site.occurrences.unwrap_or(1)).sum()
    };
    let structural_sum: u32 = ratchet
        .files
        .iter()
        .filter(|entry| entry.method == "add_decl_structural")
        .map(|entry| entry.count)
        .sum::<u32>()
        .saturating_add(site_sum(&ratchet.add_decl_structural_production_sites));
    let unchecked_sum: u32 = ratchet
        .files
        .iter()
        .filter(|entry| entry.method == "add_decl_unchecked")
        .map(|entry| entry.count)
        .sum::<u32>()
        .saturating_add(site_sum(&ratchet.add_decl_unchecked_production_sites));

    if structural_sum != ratchet.add_decl_structural_count {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{UNCHECKED_DECL_RATCHET_PATH} declares add_decl_structural_count={} but file rows + production sites sum to {structural_sum}",
                ratchet.add_decl_structural_count
            ),
        });
    }

    if unchecked_sum != ratchet.add_decl_unchecked_count {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{UNCHECKED_DECL_RATCHET_PATH} declares add_decl_unchecked_count={} but file rows + production sites sum to {unchecked_sum}",
                ratchet.add_decl_unchecked_count
            ),
        });
    }

    Ok(())
}

pub(crate) fn active_expressions(source: &str) -> Vec<&str> {
    source
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect()
}

pub(crate) fn sha256_expressions(expressions: &[&str]) -> String {
    let mut hasher = Sha256::new();
    for expression in expressions {
        hasher.update(expression.as_bytes());
        hasher.update(b"\n");
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}
