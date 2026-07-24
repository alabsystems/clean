// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

use clean_elab::cert::external::verify_alethe_certificate;
use clean_elab::cert::{
    verify_entailment_certificate, verify_farkas_certificate, ExternalCertError,
    ExternalCertErrorCode, ExternalCertificate,
};
use clean_mathverse::decision_certs::{parse_drat_text, parse_lrat_text};
use clean_verify::proof_artifact_v1::{CertificatePayloadEncoding, ProofArtifactV1};
use clean_verify::sat_verify::lrat_kernel_bridge::verify_competition_proof;
use clean_verify::sat_verify::pipeline::{verify_competition_entry, ProofFormat};
use serde::Serialize;

use super::error::MathError;
use crate::math_project::{
    executable_replay_dispatch_descriptor, ArtifactReplayAdapterDescriptor,
    ArtifactReplayDiagnostic, ArtifactReplayReport, DomainProfile, MathProjectError,
    ARTIFACT_REPLAY_SCHEMA_VERSION,
};

const UNSUPPORTED_PROFILE_ADAPTER_DIAGNOSTIC: &str = "AR001";
const NO_EXECUTABLE_ADAPTER_DIAGNOSTIC: &str = "AR002";

pub(super) fn load_artifact(path: &Path) -> Result<ProofArtifactV1, MathError> {
    let json = std::fs::read_to_string(path).map_err(|source| MathProjectError::Io {
        path: path.to_owned(),
        source,
    })?;
    ProofArtifactV1::from_json(&json).map_err(|source| MathError::Artifact {
        path: path.to_owned(),
        source,
    })
}

pub(super) fn replay_artifact(
    path: &Path,
    project: Option<String>,
    artifact: &ProofArtifactV1,
    profile: Option<&DomainProfile>,
) -> ArtifactReplayReport {
    let mut report = ArtifactReplayReport {
        schema_version: ARTIFACT_REPLAY_SCHEMA_VERSION,
        artifact_path: path.display().to_string(),
        project,
        source_system: artifact.source_system.clone(),
        artifact_kind: artifact.artifact_kind.clone(),
        problem_hash: artifact.problem_hash.clone(),
        proof_hash: artifact.proof_hash.clone(),
        certificate_format: artifact.certificate.format.clone(),
        evidence_kind: "replay_only",
        kernel_certified: false,
        replay_status: "blocked",
        replay_adapter: "none".to_owned(),
        adapter_descriptor_id: None,
        adapter_lifecycle: None,
        linked_obligations: Vec::new(),
        trusted_assumptions: Vec::new(),
        details: Vec::new(),
        diagnostics: Vec::new(),
        cache: None,
    };

    let profile_adapter = if let Some(profile) = profile {
        match profile_adapter_for_artifact(profile, artifact) {
            Some(adapter) => {
                report.adapter_descriptor_id = Some(adapter.id.clone());
                report.adapter_lifecycle = Some(adapter.status.lifecycle.clone());
                Some(adapter)
            }
            None => {
                push_diagnostic(
                    &mut report,
                    UNSUPPORTED_PROFILE_ADAPTER_DIAGNOSTIC,
                    format!(
                        "domain profile `{}` has no replay adapter for source_system `{}`, artifact_kind `{}`, certificate_format `{}`",
                        profile.name,
                        artifact.source_system,
                        artifact.artifact_kind,
                        artifact.certificate.format
                    ),
                );
                return report;
            }
        }
    } else {
        None
    };

    if let Some(adapter) = profile_adapter {
        if !descriptor_has_executable_adapter(adapter) {
            push_diagnostic(
                &mut report,
                NO_EXECUTABLE_ADAPTER_DIAGNOSTIC,
                format!(
                    "adapter descriptor `{}` is registered for domain profile `{}` but has no executable replay adapter wired into this CLI",
                    adapter.id, adapter.domain_profile
                ),
            );
            return report;
        }
    }

    if let Some(adapter) = adapter_for_declared_envelope(artifact) {
        if let Some(report) = replay_declared_adapter(artifact, adapter, &mut report) {
            return report;
        }
    }

    if artifact.certificate.encoding != CertificatePayloadEncoding::Json {
        report.details.push(format!(
            "payload encoding {:?} is envelope-valid but not replayed by this adapter",
            artifact.certificate.encoding
        ));
        return report;
    }

    let parsed =
        serde_json::from_value::<ExternalCertificate>(artifact.certificate.payload.clone());
    let certificate = match parsed {
        Ok(certificate) => certificate,
        Err(err) => {
            report.replay_status = "fail";
            report.details.push(format!(
                "certificate payload did not match a known adapter: {err}"
            ));
            return report;
        }
    };

    let adapter = adapter_for_certificate(&certificate);
    if artifact.source_system != adapter.source_system
        || artifact.artifact_kind != adapter.artifact_kind
        || artifact.certificate.format != adapter.certificate_format
    {
        report.replay_status = "fail";
        report.replay_adapter = adapter.name.to_owned();
        report.details.push(format!(
            "semantic mismatch: envelope declares source_system={}, artifact_kind={}, certificate_format={} but payload replays as source_system={}, artifact_kind={}, certificate_format={}",
            artifact.source_system,
            artifact.artifact_kind,
            artifact.certificate.format,
            adapter.source_system,
            adapter.artifact_kind,
            adapter.certificate_format
        ));
        return report;
    }

    match certificate {
        ExternalCertificate::Farkas(cert) => match verify_farkas_certificate(&cert) {
            Ok(constant) => {
                report.replay_status = "pass";
                report.replay_adapter = "gamma-crown-farkas-v1".to_owned();
                report
                    .details
                    .push(format!("verified Farkas contradiction constant {constant}"));
            }
            Err(err) => {
                report.replay_status = "fail";
                report.replay_adapter = "gamma-crown-farkas-v1".to_owned();
                report.details.push(err.to_string());
            }
        },
        ExternalCertificate::Entailment(cert) => match verify_entailment_certificate(&cert) {
            Ok((derived, claimed)) => {
                report.replay_status = "pass";
                report.replay_adapter = "gamma-crown-linear-entailment-v1".to_owned();
                report.details.push(format!(
                    "verified entailment derived bound {derived} implies claimed bound {claimed}"
                ));
            }
            Err(err) => {
                report.replay_status = "fail";
                report.replay_adapter = "gamma-crown-linear-entailment-v1".to_owned();
                report.details.push(err.to_string());
            }
        },
        ExternalCertificate::Alethe(cert) => match verify_alethe_certificate(&cert) {
            Ok(true) => {
                report.replay_status = "pass";
                report.replay_adapter = "ay-alethe-v1".to_owned();
                report
                    .details
                    .push("Alethe verifier accepted the proof".to_owned());
            }
            Ok(false) => {
                report.replay_status = "blocked";
                report.replay_adapter = "ay-alethe-v1".to_owned();
                report
                    .details
                    .push("Alethe verifier accepted only a holey/incomplete proof".to_owned());
            }
            Err(err) => {
                report.replay_status = if is_alethe_adapter_unavailable(&err) {
                    "blocked"
                } else {
                    "fail"
                };
                report.replay_adapter = "ay-alethe-v1".to_owned();
                report.details.push(err.to_string());
            }
        },
    }
    report
}

fn profile_adapter_for_artifact<'a>(
    profile: &'a DomainProfile,
    artifact: &ProofArtifactV1,
) -> Option<&'a ArtifactReplayAdapterDescriptor> {
    let source_system = artifact.source_system.as_str();
    let artifact_kind = artifact.artifact_kind.as_str();
    let certificate_format = artifact.certificate.format.as_str();

    profile.artifact_replay_adapters.iter().find(|adapter| {
        adapter_matches_source(adapter, source_system)
            && adapter.matches_artifact_kind(artifact_kind)
            && adapter.matches_artifact_format(certificate_format)
    })
}

fn adapter_matches_source(adapter: &ArtifactReplayAdapterDescriptor, source_system: &str) -> bool {
    adapter
        .source_systems
        .iter()
        .any(|source| source == source_system)
}

fn descriptor_has_executable_adapter(adapter: &ArtifactReplayAdapterDescriptor) -> bool {
    executable_replay_dispatch_descriptor(&adapter.id).is_some()
}

fn push_diagnostic(report: &mut ArtifactReplayReport, code: &'static str, message: String) {
    report.details.push(format!("{code}: {message}"));
    report.diagnostics.push(ArtifactReplayDiagnostic {
        code,
        severity: "error",
        message,
    });
}

fn replay_declared_adapter(
    artifact: &ProofArtifactV1,
    adapter: ReplayAdapter,
    report: &mut ArtifactReplayReport,
) -> Option<ArtifactReplayReport> {
    if artifact.certificate.encoding != adapter.encoding {
        report.replay_status = "blocked";
        report.replay_adapter = adapter.name.to_owned();
        report.details.push(format!(
            "{} expects {:?} payloads; envelope declared {:?}",
            adapter.name, adapter.encoding, artifact.certificate.encoding
        ));
        return Some(report.clone());
    }

    match adapter.kind {
        ReplayAdapterKind::ExternalJson => None,
        ReplayAdapterKind::DratText => {
            let Some(payload) = text_payload(artifact, report, adapter.name) else {
                return Some(report.clone());
            };
            match parse_drat_text(payload) {
                Ok(steps) if steps.is_empty() => {
                    report.replay_status = "fail";
                    report.replay_adapter = adapter.name.to_owned();
                    report.details.push(
                        "DRAT proof text parsed successfully but contains no steps".to_owned(),
                    );
                }
                Ok(steps) => {
                    report.replay_adapter = adapter.name.to_owned();
                    let Some(dimacs) = dimacs_metadata(artifact) else {
                        report.replay_status = "blocked";
                        report.details.push(format!(
                            "parsed {} DRAT step(s); checked DRAT replay requires metadata.dimacs",
                            steps.len()
                        ));
                        return Some(report.clone());
                    };
                    match verify_competition_entry(dimacs, payload.as_bytes()) {
                        Ok(result)
                            if result.valid && result.format_detected == ProofFormat::Drat =>
                        {
                            report.replay_status = "pass";
                            report.details.push(format!(
                                "verified DRAT refutation with {} parsed step(s) and {} verifier step(s)",
                                steps.len(),
                                result.stats.steps_verified
                            ));
                        }
                        Ok(result) if result.valid => {
                            report.replay_status = "fail";
                            report.details.push(format!(
                                "DRAT replay detected unexpected proof format {}",
                                result.format_detected
                            ));
                        }
                        Ok(result) => {
                            report.replay_status = "fail";
                            let detail = if result.errors.is_empty() {
                                "DRAT replay rejected the proof".to_owned()
                            } else {
                                format!(
                                    "DRAT replay rejected the proof: {}",
                                    result.errors.join("; ")
                                )
                            };
                            report.details.push(detail);
                        }
                        Err(err) => {
                            report.replay_status = "fail";
                            report.details.push(format!("DRAT replay failed: {err}"));
                        }
                    }
                }
                Err(err) => {
                    report.replay_status = "fail";
                    report.replay_adapter = adapter.name.to_owned();
                    report
                        .details
                        .push(format!("DRAT payload is malformed: {err}"));
                }
            }
            Some(report.clone())
        }
        ReplayAdapterKind::LratText => {
            let Some(payload) = text_payload(artifact, report, adapter.name) else {
                return Some(report.clone());
            };
            match parse_lrat_text(payload) {
                Ok(steps) if steps.is_empty() => {
                    report.replay_status = "fail";
                    report.replay_adapter = adapter.name.to_owned();
                    report.details.push(
                        "LRAT proof text parsed successfully but contains no steps".to_owned(),
                    );
                }
                Ok(steps) => {
                    report.replay_adapter = adapter.name.to_owned();
                    let Some(dimacs) = dimacs_metadata(artifact) else {
                        report.replay_status = "blocked";
                        report.details.push(format!(
                            "parsed {} LRAT step(s); checked LRAT replay requires metadata.dimacs",
                            steps.len()
                        ));
                        return Some(report.clone());
                    };
                    match verify_competition_proof(dimacs, payload) {
                        Ok(proof) => {
                            report.replay_status = "pass";
                            report.details.push(format!(
                                "verified LRAT refutation with {} original clause(s), {} variable(s), and {} proof step(s)",
                                proof.clause_count, proof.num_vars, proof.step_count
                            ));
                        }
                        Err(err) => {
                            report.replay_status = "fail";
                            report.details.push(format!("LRAT replay failed: {err}"));
                        }
                    }
                }
                Err(err) => {
                    report.replay_status = "fail";
                    report.replay_adapter = adapter.name.to_owned();
                    report
                        .details
                        .push(format!("LRAT payload is malformed: {err}"));
                }
            }
            Some(report.clone())
        }
        ReplayAdapterKind::VeriPbText => {
            let Some(payload) = text_payload(artifact, report, adapter.name) else {
                return Some(report.clone());
            };
            let non_comment_lines = payload
                .lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('*') && !line.starts_with('c'))
                .count();
            if non_comment_lines == 0 {
                report.replay_status = "fail";
                report.replay_adapter = adapter.name.to_owned();
                report
                    .details
                    .push("VeriPB proof text contains no proof commands".to_owned());
            } else {
                report.replay_status = "blocked";
                report.replay_adapter = adapter.name.to_owned();
                report.details.push(format!(
                    "found {non_comment_lines} VeriPB command line(s); full SAT/PB VeriPB replay adapter is not available"
                ));
            }
            Some(report.clone())
        }
    }
}

fn text_payload<'a>(
    artifact: &'a ProofArtifactV1,
    report: &mut ArtifactReplayReport,
    adapter_name: &str,
) -> Option<&'a str> {
    let Some(payload) = artifact.certificate.payload.as_str() else {
        report.replay_status = "fail";
        report.replay_adapter = adapter_name.to_owned();
        report
            .details
            .push("declared text adapter received a non-string payload".to_owned());
        return None;
    };
    if payload.trim().is_empty() {
        report.replay_status = "fail";
        report.replay_adapter = adapter_name.to_owned();
        report
            .details
            .push("proof payload must not be empty".to_owned());
        return None;
    }
    Some(payload)
}

fn dimacs_metadata(artifact: &ProofArtifactV1) -> Option<&str> {
    artifact
        .metadata
        .get("dimacs")
        .map(String::as_str)
        .filter(|dimacs| !dimacs.trim().is_empty())
}

fn is_alethe_adapter_unavailable(err: &ExternalCertError) -> bool {
    err.code == ExternalCertErrorCode::VerifierNotAvailable
        || (err.code == ExternalCertErrorCode::ProofVerificationFailed
            && err.detail.contains("carcara-verify feature required"))
}

struct ReplayAdapter {
    name: &'static str,
    source_system: &'static str,
    artifact_kind: &'static str,
    certificate_format: &'static str,
    encoding: CertificatePayloadEncoding,
    kind: ReplayAdapterKind,
}

#[derive(Clone, Copy)]
enum ReplayAdapterKind {
    ExternalJson,
    DratText,
    LratText,
    VeriPbText,
}

fn adapter_for_declared_envelope(artifact: &ProofArtifactV1) -> Option<ReplayAdapter> {
    match (
        artifact.source_system.as_str(),
        artifact.artifact_kind.as_str(),
        artifact.certificate.format.as_str(),
    ) {
        ("sat-pb", "drat", "drat") => Some(ReplayAdapter {
            name: "sat-pb-drat-v1",
            source_system: "sat-pb",
            artifact_kind: "drat",
            certificate_format: "drat",
            encoding: CertificatePayloadEncoding::Text,
            kind: ReplayAdapterKind::DratText,
        }),
        ("sat-pb", "lrat", "lrat") => Some(ReplayAdapter {
            name: "sat-pb-lrat-v1",
            source_system: "sat-pb",
            artifact_kind: "lrat",
            certificate_format: "lrat",
            encoding: CertificatePayloadEncoding::Text,
            kind: ReplayAdapterKind::LratText,
        }),
        ("sat-pb", "veripb", "veripb") => Some(ReplayAdapter {
            name: "sat-pb-veripb-v1",
            source_system: "sat-pb",
            artifact_kind: "veripb",
            certificate_format: "veripb",
            encoding: CertificatePayloadEncoding::Text,
            kind: ReplayAdapterKind::VeriPbText,
        }),
        _ => None,
    }
}

fn adapter_for_certificate(certificate: &ExternalCertificate) -> ReplayAdapter {
    match certificate {
        ExternalCertificate::Farkas(_) => ReplayAdapter {
            name: "gamma-crown-farkas-v1",
            source_system: "gamma-crown",
            artifact_kind: "gamma_crown_farkas",
            certificate_format: "gamma-crown-farkas-v1",
            encoding: CertificatePayloadEncoding::Json,
            kind: ReplayAdapterKind::ExternalJson,
        },
        ExternalCertificate::Entailment(_) => ReplayAdapter {
            name: "gamma-crown-linear-entailment-v1",
            source_system: "gamma-crown",
            artifact_kind: "gamma_crown_entailment",
            certificate_format: "gamma-crown-linear-entailment-v1",
            encoding: CertificatePayloadEncoding::Json,
            kind: ReplayAdapterKind::ExternalJson,
        },
        ExternalCertificate::Alethe(_) => ReplayAdapter {
            name: "ay-alethe-v1",
            source_system: "ay",
            artifact_kind: "ay_alethe_envelope",
            certificate_format: "ay-alethe-envelope-v1",
            encoding: CertificatePayloadEncoding::Json,
            kind: ReplayAdapterKind::ExternalJson,
        },
    }
}

#[derive(Debug, Serialize)]
pub(super) struct ArtifactEnvelopeReport {
    pub(super) schema_version: &'static str,
    pub(super) path: String,
    pub(super) source_system: String,
    pub(super) artifact_kind: String,
    pub(super) problem_hash: String,
    pub(super) model_hash: String,
    pub(super) proof_hash: String,
    pub(super) certificate_format: String,
    pub(super) verifier_constants: usize,
    pub(super) metadata: usize,
    pub(super) status: &'static str,
}

impl ArtifactEnvelopeReport {
    pub(super) fn from_artifact(path: &Path, artifact: &ProofArtifactV1) -> Self {
        Self {
            schema_version: "clean-artifact-envelope-report-v1",
            path: path.display().to_string(),
            source_system: artifact.source_system.clone(),
            artifact_kind: artifact.artifact_kind.clone(),
            problem_hash: artifact.problem_hash.clone(),
            model_hash: artifact.model_hash.clone(),
            proof_hash: artifact.proof_hash.clone(),
            certificate_format: artifact.certificate.format.clone(),
            verifier_constants: artifact.verifier_constants.len(),
            metadata: artifact.metadata.len(),
            status: "pass",
        }
    }
}
