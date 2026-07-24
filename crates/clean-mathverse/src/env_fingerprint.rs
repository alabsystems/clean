// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reproducible execution fingerprints for Mathverse attempts.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::error::{MathverseError, MathverseResult};

/// Dirty-state fingerprint for a git worktree used by an attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GitDirtyState {
    /// Whether `repo_root` is inside a git worktree.
    pub is_git_worktree: bool,
    /// `Some(true)` when git status is clean, `Some(false)` when dirty, or
    /// `None` when `repo_root` is not a git worktree.
    pub git_status_clean: Option<bool>,
    /// Number of dirty porcelain entries, including untracked files.
    pub dirty_entry_count: usize,
    /// SHA-256 digest of normalized porcelain entries when dirty.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dirty_entries_sha256: Option<String>,
}

/// Metadata for an external solver binary used by an attempt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverBinaryFingerprint {
    /// Stable solver name, for example `z3` or `cadical`.
    pub name: String,
    /// Captured `--version` output.
    pub version: String,
    /// SHA-256 digest of the executable bytes.
    pub sha256: String,
}

impl SolverBinaryFingerprint {
    /// Build a canonical solver-binary fingerprint.
    pub fn new(
        name: impl Into<String>,
        version: impl Into<String>,
        sha256: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            sha256: sha256.into(),
        }
    }
}

/// Solver binary capture request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverBinarySpec {
    /// Stable solver name.
    pub name: String,
    /// Executable path.
    pub path: PathBuf,
    /// Arguments used to print version information.
    pub version_args: Vec<String>,
}

impl SolverBinarySpec {
    /// Build a solver spec that captures version information with `--version`.
    pub fn new(name: impl Into<String>, path: impl Into<PathBuf>) -> Self {
        Self {
            name: name.into(),
            path: path.into(),
            version_args: vec!["--version".to_owned()],
        }
    }

    /// Override the arguments used to capture the solver version.
    pub fn with_version_args(mut self, args: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.version_args = args.into_iter().map(Into::into).collect();
        self
    }
}

/// Canonical environment pinning for reproducible Mathverse attempts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvFingerprint {
    /// Lean toolchain string from `lean-toolchain`, or `missing` when absent.
    pub lean_toolchain: String,
    /// Clean repository commit from `git rev-parse HEAD`, or `unknown`.
    pub clean_commit: String,
    /// ay dependency revision, if discoverable from Cargo metadata files.
    #[serde(default)]
    pub ay_revision: Option<String>,
    /// llvm2 dependency revision, if discoverable from Cargo metadata files.
    #[serde(default)]
    pub llvm2_revision: Option<String>,
    /// Host CPU architecture.
    pub host_arch: String,
    /// Host operating system.
    pub host_os: String,
    /// Exact solver binaries used by the attempt.
    #[serde(default)]
    pub solver_binaries: Vec<SolverBinaryFingerprint>,
}

impl EnvFingerprint {
    /// Build a fingerprint for the current host from caller-supplied revisions.
    pub fn from_host(
        lean_toolchain: impl Into<String>,
        clean_commit: impl Into<String>,
        ay_revision: Option<String>,
        llvm2_revision: Option<String>,
        solver_binaries: Vec<SolverBinaryFingerprint>,
    ) -> Self {
        Self {
            lean_toolchain: lean_toolchain.into(),
            clean_commit: clean_commit.into(),
            ay_revision,
            llvm2_revision,
            host_arch: std::env::consts::ARCH.to_owned(),
            host_os: std::env::consts::OS.to_owned(),
            solver_binaries,
        }
    }

    /// Build a fingerprint for the current host without dependency revisions.
    pub fn from_host_toolchain(
        lean_toolchain: impl Into<String>,
        clean_commit: impl Into<String>,
    ) -> Self {
        Self::from_host(lean_toolchain, clean_commit, None, None, Vec::new())
    }

    /// Capture the local Clean/Lean environment without solver binaries.
    pub fn capture(repo_root: impl AsRef<Path>) -> MathverseResult<Self> {
        Self::capture_with_solver_binaries(repo_root, &[])
    }

    /// Capture the local Clean/Lean environment and the supplied solver binaries.
    ///
    /// Solver capture is fail-closed: a missing binary, non-zero version
    /// command, empty version output, or unreadable executable returns an error.
    pub fn capture_with_solver_binaries(
        repo_root: impl AsRef<Path>,
        solver_specs: &[SolverBinarySpec],
    ) -> MathverseResult<Self> {
        let root = repo_root.as_ref();
        let solver_binaries = solver_specs
            .iter()
            .map(capture_solver_binary)
            .collect::<MathverseResult<Vec<_>>>()?;

        Ok(Self::from_host(
            read_lean_toolchain(root),
            read_clean_commit(root),
            dependency_revision(root, &["ay", "ay-core", "ay-proof"]),
            dependency_revision(root, &["llvm2"]),
            solver_binaries,
        ))
    }

    /// Capture git dirty-state metadata adjacent to this environment
    /// fingerprint. This is intentionally separate from `EnvFingerprint` so old
    /// attempt logs and existing struct literals remain source-compatible while
    /// gate layers start rejecting dirty accepted attempts.
    pub fn capture_git_dirty_state(repo_root: impl AsRef<Path>) -> MathverseResult<GitDirtyState> {
        capture_git_dirty_state(repo_root)
    }
}

/// Capture whether `repo_root` is a clean git worktree, including untracked
/// files in the dirty count and digest.
pub fn capture_git_dirty_state(repo_root: impl AsRef<Path>) -> MathverseResult<GitDirtyState> {
    let root = repo_root.as_ref();
    if !is_git_worktree(root)? {
        return Ok(GitDirtyState {
            is_git_worktree: false,
            git_status_clean: None,
            dirty_entry_count: 0,
            dirty_entries_sha256: None,
        });
    }

    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["status", "--porcelain=v1", "--untracked-files=normal"])
        .output()
        .map_err(|source| {
            MathverseError::Kernel(format!(
                "failed to capture git status for `{}`: {source}",
                root.display()
            ))
        })?;

    if !output.status.success() {
        return Err(MathverseError::Kernel(format!(
            "git status failed for `{}` with status {}: {}",
            root.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }

    Ok(git_dirty_state_from_porcelain(&String::from_utf8_lossy(
        &output.stdout,
    )))
}

/// Capture version and executable digest for one solver binary.
pub fn capture_solver_binary(spec: &SolverBinarySpec) -> MathverseResult<SolverBinaryFingerprint> {
    let output = Command::new(&spec.path)
        .args(&spec.version_args)
        .output()
        .map_err(|source| {
            MathverseError::Kernel(format!(
                "failed to execute solver `{}` at `{}` for version capture: {source}",
                spec.name,
                spec.path.display()
            ))
        })?;

    if !output.status.success() {
        return Err(MathverseError::Kernel(format!(
            "solver `{}` version command exited with status {}",
            spec.name, output.status
        )));
    }

    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    let version = match (stdout.is_empty(), stderr.is_empty()) {
        (false, false) => format!("{stdout}\n{stderr}"),
        (false, true) => stdout,
        (true, false) => stderr,
        (true, true) => {
            return Err(MathverseError::Kernel(format!(
                "solver `{}` produced empty version output",
                spec.name
            )))
        }
    };

    let bytes = fs::read(&spec.path).map_err(|source| {
        MathverseError::Kernel(format!(
            "failed to read solver `{}` at `{}` for sha256 capture: {source}",
            spec.name,
            spec.path.display()
        ))
    })?;

    Ok(SolverBinaryFingerprint::new(
        spec.name.clone(),
        version,
        sha256_hex(&bytes),
    ))
}

fn read_lean_toolchain(root: &Path) -> String {
    let path = root.join("lean-toolchain");
    fs::read_to_string(path)
        .ok()
        .map(|s| s.trim().to_owned())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "missing".to_owned())
}

fn read_clean_commit(root: &Path) -> String {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .arg("rev-parse")
        .arg("HEAD")
        .output();

    output
        .ok()
        .filter(|out| out.status.success())
        .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_owned())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".to_owned())
}

fn is_git_worktree(root: &Path) -> MathverseResult<bool> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "--is-inside-work-tree"])
        .output()
        .map_err(|source| {
            MathverseError::Kernel(format!(
                "failed to query git worktree for `{}`: {source}",
                root.display()
            ))
        })?;

    if !output.status.success() {
        return Ok(false);
    }

    Ok(String::from_utf8_lossy(&output.stdout).trim() == "true")
}

fn git_dirty_state_from_porcelain(porcelain: &str) -> GitDirtyState {
    let mut entries = porcelain
        .lines()
        .map(str::trim_end)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    entries.sort();

    let dirty_entry_count = entries.len();
    let dirty_entries_sha256 = if entries.is_empty() {
        None
    } else {
        Some(sha256_hex(entries.join("\n").as_bytes()))
    };

    GitDirtyState {
        is_git_worktree: true,
        git_status_clean: Some(entries.is_empty()),
        dirty_entry_count,
        dirty_entries_sha256,
    }
}

fn dependency_revision(root: &Path, package_names: &[&str]) -> Option<String> {
    let lock_revision = fs::read_to_string(root.join("Cargo.lock"))
        .ok()
        .and_then(|content| revision_from_lock(&content, package_names));
    if lock_revision.is_some() {
        return lock_revision;
    }

    fs::read_to_string(root.join("Cargo.toml"))
        .ok()
        .and_then(|content| revision_from_manifest(&content, package_names))
}

fn revision_from_lock(content: &str, package_names: &[&str]) -> Option<String> {
    for block in content.split("\n\n") {
        let mut matched = false;
        let mut source = None;
        let mut version = None;

        for line in block.lines().map(str::trim) {
            if package_names
                .iter()
                .any(|name| line == format!("name = \"{name}\""))
            {
                matched = true;
            } else if let Some(value) = line.strip_prefix("source = ") {
                source = Some(trim_toml_string(value).to_owned());
            } else if let Some(value) = line.strip_prefix("version = ") {
                version = Some(format!("version:{}", trim_toml_string(value)));
            }
        }

        if matched {
            return source.or(version);
        }
    }

    None
}

fn revision_from_manifest(content: &str, package_names: &[&str]) -> Option<String> {
    for line in content.lines().map(str::trim) {
        for name in package_names {
            let prefix = format!("{name} =");
            if line.starts_with(&prefix) {
                return Some(extract_revision_from_spec(line));
            }
        }
    }
    None
}

fn extract_revision_from_spec(spec: &str) -> String {
    for key in ["rev", "tag", "branch", "version"] {
        let pattern = format!("{key} = \"");
        if let Some(start) = spec.find(&pattern) {
            let value_start = start + pattern.len();
            if let Some(end) = spec[value_start..].find('"') {
                return format!("{key}:{}", &spec[value_start..value_start + end]);
            }
        }
    }

    spec.to_owned()
}

fn trim_toml_string(value: &str) -> &str {
    value.trim().trim_matches('"')
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    hex_lower(&digest[..])
}

fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_fingerprint_json_shape_is_stable() {
        let env = EnvFingerprint {
            lean_toolchain: "leanprover/lean4:v4.15.0".to_owned(),
            clean_commit: "0123456789abcdef".to_owned(),
            ay_revision: Some("rev:ayabc".to_owned()),
            llvm2_revision: Some("tag:llvm2-1.0".to_owned()),
            host_arch: "x86_64".to_owned(),
            host_os: "linux".to_owned(),
            solver_binaries: vec![SolverBinaryFingerprint::new(
                "z3",
                "Z3 version 4.13.0",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            )],
        };

        let json = serde_json::to_string(&env).expect("serialize env fingerprint");

        assert_eq!(
            json,
            "{\"lean_toolchain\":\"leanprover/lean4:v4.15.0\",\"clean_commit\":\"0123456789abcdef\",\"ay_revision\":\"rev:ayabc\",\"llvm2_revision\":\"tag:llvm2-1.0\",\"host_arch\":\"x86_64\",\"host_os\":\"linux\",\"solver_binaries\":[{\"name\":\"z3\",\"version\":\"Z3 version 4.13.0\",\"sha256\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}"
        );
    }

    #[test]
    fn solver_binary_json_shape_is_stable() {
        let solver = SolverBinaryFingerprint::new(
            "cadical",
            "CaDiCaL 1.9.5",
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        );

        let json = serde_json::to_string(&solver).expect("serialize solver fingerprint");

        assert_eq!(
            json,
            "{\"name\":\"cadical\",\"version\":\"CaDiCaL 1.9.5\",\"sha256\":\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"}"
        );
    }

    #[test]
    fn env_fingerprint_deserializes_attempt_logs_without_solver_binaries() {
        let json = "{\"lean_toolchain\":\"leanprover/lean4:v4.15.0\",\"clean_commit\":\"0123456789abcdef\",\"host_arch\":\"aarch64\",\"host_os\":\"macos\"}";

        let env: EnvFingerprint =
            serde_json::from_str(json).expect("deserialize old env fingerprint");

        assert_eq!(env.ay_revision, None);
        assert_eq!(env.llvm2_revision, None);
        assert_eq!(env.solver_binaries, Vec::new());
    }

    #[test]
    fn git_dirty_state_from_empty_porcelain_is_clean() {
        let state = git_dirty_state_from_porcelain("");

        assert!(state.is_git_worktree);
        assert_eq!(state.git_status_clean, Some(true));
        assert_eq!(state.dirty_entry_count, 0);
        assert_eq!(state.dirty_entries_sha256, None);
    }

    #[test]
    fn git_dirty_state_digest_is_deterministic_over_sorted_porcelain_entries() {
        let first = git_dirty_state_from_porcelain(" M src/lib.rs\n?? notes.txt\n");
        let second = git_dirty_state_from_porcelain("?? notes.txt\n M src/lib.rs\n");

        assert!(first.is_git_worktree);
        assert_eq!(first.git_status_clean, Some(false));
        assert_eq!(first.dirty_entry_count, 2);
        assert_eq!(first, second);
        let expected_digest = sha256_hex(" M src/lib.rs\n?? notes.txt".as_bytes());
        assert_eq!(
            first.dirty_entries_sha256.as_deref(),
            Some(expected_digest.as_str())
        );
    }

    #[test]
    fn capture_git_dirty_state_tracks_untracked_files_in_git_repo() {
        let repo = tempfile::tempdir().expect("temp git repo");
        let init = Command::new("git")
            .arg("-C")
            .arg(repo.path())
            .arg("init")
            .output()
            .expect("run git init");
        if !init.status.success() {
            eprintln!(
                "skipping git dirty-state smoke test: git init failed: {}",
                String::from_utf8_lossy(&init.stderr)
            );
            return;
        }

        let clean = capture_git_dirty_state(repo.path()).expect("capture clean git state");
        assert!(clean.is_git_worktree);
        assert_eq!(clean.git_status_clean, Some(true));
        assert_eq!(clean.dirty_entry_count, 0);
        assert_eq!(clean.dirty_entries_sha256, None);

        fs::write(repo.path().join("untracked.txt"), "dirty\n").expect("write untracked file");
        let dirty =
            EnvFingerprint::capture_git_dirty_state(repo.path()).expect("capture dirty git state");
        assert!(dirty.is_git_worktree);
        assert_eq!(dirty.git_status_clean, Some(false));
        assert_eq!(dirty.dirty_entry_count, 1);
        assert!(dirty.dirty_entries_sha256.is_some());
    }

    #[test]
    fn capture_git_dirty_state_reports_non_git_roots_without_dirty_digest() {
        let dir = tempfile::tempdir().expect("temp non-git dir");

        let state = capture_git_dirty_state(dir.path()).expect("capture non-git state");

        assert!(!state.is_git_worktree);
        assert_eq!(state.git_status_clean, None);
        assert_eq!(state.dirty_entry_count, 0);
        assert_eq!(state.dirty_entries_sha256, None);
    }

    #[test]
    fn solver_binary_deserializes_legacy_path_field() {
        let json = "{\"name\":\"z3\",\"path\":\"/usr/bin/z3\",\"version\":\"Z3 version 4.13.0\",\"sha256\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}";

        let solver: SolverBinaryFingerprint =
            serde_json::from_str(json).expect("deserialize legacy solver fingerprint");

        assert_eq!(
            solver,
            SolverBinaryFingerprint::new(
                "z3",
                "Z3 version 4.13.0",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
            )
        );
    }

    #[test]
    fn from_host_captures_current_arch_and_os() {
        let env = EnvFingerprint::from_host_toolchain("lean", "commit");

        assert_eq!(env.lean_toolchain, "lean");
        assert_eq!(env.clean_commit, "commit");
        assert_eq!(env.host_arch, std::env::consts::ARCH);
        assert_eq!(env.host_os, std::env::consts::OS);
        assert_eq!(env.solver_binaries, Vec::new());
    }
}
