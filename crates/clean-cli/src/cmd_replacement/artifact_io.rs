// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Repo artifact discovery, hashing, and JSON IO helpers.

use super::*;

/// Where declared repo artifacts are resolved from, and on whose authority.
///
/// Recorded in the scorecard output so a reader can tell which tree was scored.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum RepoRootSource {
    /// `CLEAN_REPLACEMENT_REPO_ROOT` named it. The only supported override.
    EnvOverride,
    /// The tree this binary was built from. The default.
    BuildTimeRepo,
    /// The build tree is gone (a relocated binary), so the process working
    /// directory is the last resort. Reported, never silent.
    WorkingDirectoryFallback,
}

impl RepoRootSource {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::EnvOverride => "env:CLEAN_REPLACEMENT_REPO_ROOT",
            Self::BuildTimeRepo => "build-time-repo",
            Self::WorkingDirectoryFallback => "working-directory-fallback",
        }
    }
}

/// Resolve the repo root ONCE, deterministically, and say where it came from.
///
/// This replaces a cwd-**first** lookup with a silent fallback to the build-time
/// repo. That order was exploitable and was measured to be: run from a `/tmp`
/// directory holding three EMPTY files named `reports/tactic-parity-counts.json`,
/// `reports/strict-solver-fragment-dashboard.json` and
/// `reports/compile-runtime-smoke.json`, the informational gate scored all three
/// rows `green/present` — three of its four effectively-green rows — off files
/// in a directory it never named in its output.
///
/// A declared evidence path names a file in *this repo*; resolving it against
/// whatever directory the process happens to sit in is not a feature. The
/// working directory is consulted only when the build tree no longer exists,
/// and that case is reported rather than assumed.
pub(crate) fn repo_root_provenance() -> (PathBuf, RepoRootSource) {
    if let Some(root) = std::env::var_os("CLEAN_REPLACEMENT_REPO_ROOT") {
        let root = PathBuf::from(root);
        if root.is_dir() {
            return (root, RepoRootSource::EnvOverride);
        }
    }
    let build_time_repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    if build_time_repo.is_dir() {
        return (build_time_repo, RepoRootSource::BuildTimeRepo);
    }
    (
        std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
        RepoRootSource::WorkingDirectoryFallback,
    )
}

/// The repo root every declared artifact resolves against.
pub(crate) fn repo_root() -> PathBuf {
    repo_root_provenance().0
}

pub(crate) fn repo_artifact_path(path: &str) -> PathBuf {
    repo_root().join(path)
}

pub(crate) fn normalize_repo_path(path: &Path) -> String {
    if path.is_absolute() {
        path.strip_prefix(repo_root())
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

/// Digest every non-test `.rs` file under `dir`, so the trust-core evidence is
/// pinned to the gate logic that produced it.
///
/// `TRUST_CORE_RUST_SOURCE_PATH` alone pins only `cmd_replacement.rs`, which is
/// just `mod`/`use` declarations: the gate's actual behaviour lives in the
/// submodules, so a change there would leave a stale artifact reading as fresh.
///
/// The `tests/` subtree is excluded deliberately. It cannot change what the
/// gate does at runtime, and including it would invalidate a genuinely current
/// artifact on every unrelated test edit.
pub(crate) fn sha256_repo_module_tree(dir: &'static str) -> Result<String, ReplacementError> {
    let root = repo_artifact_path(dir);
    let mut entries: Vec<(String, Vec<u8>)> = Vec::new();
    for entry in WalkDir::new(&root).into_iter().filter_map(Result::ok) {
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("rs")
        {
            continue;
        }
        let relative = entry
            .path()
            .strip_prefix(&root)
            .unwrap_or(entry.path())
            .to_string_lossy()
            .replace('\\', "/");
        if relative.starts_with("tests/") {
            continue;
        }
        let bytes = fs::read(entry.path())
            .map_err(|source| ReplacementError::ReadArtifact { path: dir, source })?;
        entries.push((relative, bytes));
    }
    // WalkDir order is filesystem-dependent; sort so the digest is stable.
    entries.sort_by(|left, right| left.0.cmp(&right.0));

    let mut hasher = Sha256::new();
    for (relative, bytes) in entries {
        // Length-delimit so no rename/content shuffle can collide.
        hasher.update(relative.as_bytes());
        hasher.update([0u8]);
        hasher.update(bytes.len().to_le_bytes());
        hasher.update(&bytes);
    }
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
