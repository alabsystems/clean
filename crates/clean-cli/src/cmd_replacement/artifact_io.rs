// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Repo artifact discovery, hashing, and JSON IO helpers.

use super::*;

pub(crate) fn repo_artifact_path(path: &'static str) -> PathBuf {
    let cwd_path = Path::new(path);
    if cwd_path.exists() {
        return cwd_path.to_path_buf();
    }

    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(path)
}

pub(crate) fn normalize_repo_path(path: &Path) -> String {
    if path.is_absolute() {
        let repo_root = repo_artifact_path("Cargo.toml")
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf();
        path.strip_prefix(repo_root)
            .unwrap_or(path)
            .to_string_lossy()
            .replace('\\', "/")
    } else {
        path.to_string_lossy().replace('\\', "/")
    }
}

pub(crate) fn dynamic_artifact_path(path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() || path.exists() {
        path.to_path_buf()
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(path)
    }
}

pub(crate) fn read_dynamic_artifact(path: &str) -> Result<String, ReplacementError> {
    fs::read_to_string(dynamic_artifact_path(path)).map_err(|source| ReplacementError::ReadReport {
        path: path.to_string(),
        source,
    })
}

pub(crate) fn sha256_dynamic_artifact(path: &str) -> Result<String, ReplacementError> {
    let bytes =
        fs::read(dynamic_artifact_path(path)).map_err(|source| ReplacementError::ReadReport {
            path: path.to_string(),
            source,
        })?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    Ok(hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>())
}

pub(crate) fn write_json_path<T: Serialize>(
    path: &Path,
    value: &T,
) -> Result<(), ReplacementError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let text = serde_json::to_string_pretty(value).map_err(ReplacementError::Serialize)?;
    fs::write(path, format!("{text}\n"))?;
    Ok(())
}

pub(crate) fn read_repo_artifact(path: &'static str) -> Result<String, ReplacementError> {
    fs::read_to_string(repo_artifact_path(path))
        .map_err(|source| ReplacementError::ReadArtifact { path, source })
}

pub(crate) fn read_optional_repo_artifact(
    path: &'static str,
) -> Result<Option<String>, ReplacementError> {
    match fs::read_to_string(repo_artifact_path(path)) {
        Ok(source) => Ok(Some(source)),
        Err(source) if source.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(source) => Err(ReplacementError::ReadArtifact { path, source }),
    }
}

pub(crate) fn sha256_repo_artifact(path: &'static str) -> Result<String, ReplacementError> {
    let bytes = fs::read(repo_artifact_path(path))
        .map_err(|source| ReplacementError::ReadArtifact { path, source })?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    Ok(hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>())
}

pub(crate) fn parse_repo_json<T: for<'de> Deserialize<'de>>(
    path: &'static str,
) -> Result<T, ReplacementError> {
    let source = read_repo_artifact(path)?;
    serde_json::from_str(&source).map_err(|source| ReplacementError::ParseArtifact { path, source })
}

pub(crate) fn load_lean4_baseline() -> Result<Lean4BaselineArtifact, ReplacementError> {
    parse_repo_json(LEAN4_BASELINE_PATH)
}

pub(crate) fn load_unchecked_decl_ratchet() -> Result<UncheckedDeclRatchetArtifact, ReplacementError>
{
    parse_repo_json(UNCHECKED_DECL_RATCHET_PATH)
}

pub(crate) fn load_axiom_audit() -> Result<AxiomAuditArtifact, ReplacementError> {
    parse_repo_json(AXIOM_AUDIT_PATH)
}

pub(crate) fn load_kernel_soundness_launch_evidence(
    baseline: &Lean4BaselineArtifact,
    expression_count: usize,
    expressions_sha256: &str,
) -> Result<KernelSoundnessLaunchEvidence, ReplacementError> {
    let Some(source) = read_optional_repo_artifact(KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_PATH)? else {
        return Ok(KernelSoundnessLaunchEvidence::missing());
    };

    let artifact = match serde_json::from_str::<KernelSoundnessLaunchEvidenceArtifact>(&source) {
        Ok(artifact) => artifact,
        Err(error) => {
            return Ok(KernelSoundnessLaunchEvidence::stale(format!(
                "invalid JSON: {error}"
            )));
        }
    };

    match validate_kernel_soundness_launch_evidence(
        &artifact,
        baseline,
        expression_count,
        expressions_sha256,
    ) {
        Ok(()) => Ok(KernelSoundnessLaunchEvidence::passed()),
        Err(message) => Ok(KernelSoundnessLaunchEvidence::stale(message)),
    }
}

pub(crate) fn load_deny_sorry_launch_evidence(
    ratchet: &UncheckedDeclRatchetArtifact,
) -> Result<DenySorryLaunchEvidence, ReplacementError> {
    let Some(source) = read_optional_repo_artifact(DENY_SORRY_LAUNCH_EVIDENCE_PATH)? else {
        return Ok(DenySorryLaunchEvidence::missing());
    };

    let artifact = match serde_json::from_str::<DenySorryLaunchEvidenceArtifact>(&source) {
        Ok(artifact) => artifact,
        Err(error) => {
            return Ok(DenySorryLaunchEvidence::stale(format!(
                "invalid JSON: {error}"
            )));
        }
    };

    match validate_deny_sorry_launch_evidence(&artifact, ratchet) {
        Ok(()) => Ok(DenySorryLaunchEvidence::passed()),
        Err(message) => Ok(DenySorryLaunchEvidence::stale(message)),
    }
}

pub(crate) fn load_axiom_audit_launch_evidence(
    axiom_audit: &AxiomAuditArtifact,
) -> Result<AxiomAuditLaunchEvidence, ReplacementError> {
    let Some(source) = read_optional_repo_artifact(AXIOM_AUDIT_LAUNCH_EVIDENCE_PATH)? else {
        return Ok(AxiomAuditLaunchEvidence::missing());
    };

    let artifact = match serde_json::from_str::<AxiomAuditLaunchEvidenceArtifact>(&source) {
        Ok(artifact) => artifact,
        Err(error) => {
            return Ok(AxiomAuditLaunchEvidence::stale(format!(
                "invalid JSON: {error}"
            )));
        }
    };

    match validate_axiom_audit_launch_evidence(&artifact, axiom_audit) {
        Ok(()) => Ok(AxiomAuditLaunchEvidence::passed()),
        Err(message) => Ok(AxiomAuditLaunchEvidence::stale(message)),
    }
}

pub(crate) fn trust_core_source_artifacts() -> Vec<&'static str> {
    vec![
        TRUST_CORE_RUST_SOURCE_PATH,
        LEAN4_BASELINE_PATH,
        LEAN4_EXPRESSIONS_PATH,
        UNCHECKED_DECL_RATCHET_PATH,
        AXIOM_AUDIT_RUST_SOURCE_PATH,
        AXIOM_AUDIT_PATH,
        VERIFICATION_AUDIT_PATH,
        VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH,
        PROOF_SYSTEM_CERTIFICATION_BLOCKER_REPORT_PATH,
    ]
}

/// The git-tracked subset of [`trust_core_source_artifacts`]: absence of any
/// of these is repo corruption and hard-fails the report. The two
/// `reports/2026-04-27-*` snapshots are machine-local gh evidence and degrade
/// the certification row instead (see
/// `ProofSystemCertificationEvidence::missing_issue_state_snapshot`).
pub(crate) const REQUIRED_TRUST_CORE_SOURCE_ARTIFACTS: &[&str] = &[
    TRUST_CORE_RUST_SOURCE_PATH,
    LEAN4_BASELINE_PATH,
    LEAN4_EXPRESSIONS_PATH,
    UNCHECKED_DECL_RATCHET_PATH,
    AXIOM_AUDIT_RUST_SOURCE_PATH,
    AXIOM_AUDIT_PATH,
    VERIFICATION_AUDIT_PATH,
];
