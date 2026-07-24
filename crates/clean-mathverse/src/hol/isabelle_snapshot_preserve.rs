// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Snapshot ↔ binary preservation** — the one-command replacement for the
//! operator's manual "`cp` the harness binary somewhere durable" dance.
//!
//! A replay snapshot is only resumable by a binary whose ENV-LAYOUT matches the
//! one that wrote it (see [`super::isabelle_pure_verify::snapshot`]); upstream
//! kernel serde churn silently invalidates that pairing. To make a snapshot
//! durably resumable, the operator must keep a copy of the exact binary that
//! built it. This module copies the CURRENT running binary (`current_exe`) into
//! a durable "binaries dir", named by its git SHA, so the pairing is preserved
//! with one command:
//!
//! ```text
//! clean mathverse isabelle-snapshot-preserve --snapshot <s> --binaries-dir <d>
//! ```
//!
//! # Limitation: test-harness binaries
//!
//! `current_exe` is whatever process is running. Invoked as the real `clean`
//! binary it copies `clean`; invoked under a `cargo test` / integration harness
//! it copies the TEST binary (not the release harness that produced the
//! snapshot). In that case the operator must still copy the real harness binary
//! manually — this command cannot reach across process identities.

use std::path::{Path, PathBuf};

use super::isabelle_doctor::BuildIdentity;
use super::isabelle_pure_verify::snapshot;

/// Errors from the snapshot-preserve helper.
#[derive(Debug, thiserror::Error)]
pub enum PreserveError {
    /// The running binary could not be resolved (`std::env::current_exe`).
    #[error("could not resolve the current binary (current_exe): {0}")]
    CurrentExe(#[source] std::io::Error),
    /// The durable binaries directory could not be created.
    #[error("failed to create binaries dir {path}: {source}")]
    MakeDir {
        /// The directory that could not be created.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },
    /// Copying the binary into the durable directory failed.
    #[error("failed to copy binary {from} -> {to}: {source}")]
    Copy {
        /// Source binary (`current_exe`).
        from: PathBuf,
        /// Destination path (`<binaries-dir>/clean-<sha>`).
        to: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },
}

/// The result of a preserve run, for the CLI to render.
#[derive(Debug, Clone)]
pub struct PreserveReport {
    /// The binary that was copied (`current_exe`).
    pub source: PathBuf,
    /// Where it was copied to (`<binaries-dir>/clean-<sha>`).
    pub dest: PathBuf,
    /// The git SHA the destination was named by (`"unknown"` if not embedded).
    pub sha: String,
    /// The snapshot the operator named (for the pairing report).
    pub snapshot: PathBuf,
    /// Human pairing note: does this binary match the snapshot's builder?
    pub pairing: String,
}

/// The 7-char short prefix of a SHA-like string (`"unknown"` passes through).
fn short_sha(s: &str) -> &str {
    &s[..s.len().min(7)]
}

/// Copy `source` into `binaries_dir`, naming the copy `clean-<sha>`. Creates the
/// directory if needed. `std::fs::copy` carries the permission (exec) bits, so
/// the preserved copy stays runnable.
///
/// # Errors
/// [`PreserveError::MakeDir`] / [`PreserveError::Copy`] on I/O failure.
pub fn copy_binary_as_sha(
    source: &Path,
    sha: &str,
    binaries_dir: &Path,
) -> Result<PathBuf, PreserveError> {
    std::fs::create_dir_all(binaries_dir).map_err(|e| PreserveError::MakeDir {
        path: binaries_dir.to_path_buf(),
        source: e,
    })?;
    let dest = binaries_dir.join(format!("clean-{sha}"));
    std::fs::copy(source, &dest).map_err(|e| PreserveError::Copy {
        from: source.to_path_buf(),
        to: dest.clone(),
        source: e,
    })?;
    Ok(dest)
}

/// Human pairing note comparing `current_sha` against the snapshot's provenance
/// sidecar (if any). Pure over the on-disk sidecar so it is unit-testable.
fn pairing_note(snapshot_path: &Path, current_sha: &str) -> String {
    match snapshot::read_provenance_sidecar(snapshot_path) {
        Some(p) => {
            let verdict = if p.binary_git_sha != "unknown"
                && !p.binary_git_sha.is_empty()
                && current_sha != "unknown"
            {
                if p.binary_git_sha == current_sha {
                    "MATCH — this binary built the snapshot"
                } else {
                    "MISMATCH — this is NOT the snapshot's builder binary"
                }
            } else {
                "UNVERIFIABLE (a SHA is unknown)"
            };
            format!(
                "snapshot {} built by {} — {verdict}",
                snapshot_path.display(),
                short_sha(&p.binary_git_sha)
            )
        }
        None => format!(
            "snapshot {} has no provenance sidecar — pairing unverifiable",
            snapshot_path.display()
        ),
    }
}

/// Preserve the CURRENT running binary into `binaries_dir` named by its SHA, and
/// report its pairing against `snapshot`'s provenance sidecar.
///
/// # Errors
/// See [`PreserveError`].
pub fn run_preserve(
    snapshot_path: &Path,
    binaries_dir: &Path,
    build: &BuildIdentity,
) -> Result<PreserveReport, PreserveError> {
    let source = std::env::current_exe().map_err(PreserveError::CurrentExe)?;
    let sha = build
        .git_sha
        .clone()
        .unwrap_or_else(|| "unknown".to_string());
    let dest = copy_binary_as_sha(&source, &sha, binaries_dir)?;
    let pairing = pairing_note(snapshot_path, &sha);
    Ok(PreserveReport {
        source,
        dest,
        sha,
        snapshot: snapshot_path.to_path_buf(),
        pairing,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::isabelle_pure_verify::snapshot::SnapshotProvenance;

    fn tmpdir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("isa_preserve_{tag}_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("mk tmpdir");
        dir
    }

    #[test]
    fn test_copy_binary_as_sha_copies_and_names() {
        let dir = tmpdir("copy");
        let src = dir.join("fake-clean");
        std::fs::write(&src, b"BINARY-CONTENT").expect("write source");
        let bindir = dir.join("bins");

        let dest = copy_binary_as_sha(&src, "abc1234", &bindir).expect("copy");
        assert_eq!(dest, bindir.join("clean-abc1234"), "named by its sha");
        assert!(dest.exists(), "destination binary exists");
        assert_eq!(
            std::fs::read(&dest).expect("read dest"),
            b"BINARY-CONTENT",
            "contents copied byte-for-byte"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_copy_binary_as_sha_creates_missing_dir() {
        let dir = tmpdir("mkdir");
        let src = dir.join("fake-clean");
        std::fs::write(&src, b"X").expect("write source");
        let bindir = dir.join("a").join("b").join("c"); // nested, absent

        let dest = copy_binary_as_sha(&src, "deadbee", &bindir).expect("copy into fresh dir");
        assert!(dest.exists(), "nested binaries dir created and file copied");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_pairing_note_matches_when_sidecar_sha_equals_current() {
        let dir = tmpdir("pair_match");
        let snap = dir.join("s.snap");
        let prov = SnapshotProvenance {
            binary_git_sha: "abc123def456".to_string(),
            binary_path: "/opt/clean/bin/clean".to_string(),
            env_layout_fp: "ff".to_string(),
            corpus_fingerprint: "aa".to_string(),
            created_unix: 1,
        };
        snapshot::write_provenance_sidecar(&snap, &prov).expect("write sidecar");

        let note = pairing_note(&snap, "abc123def456");
        assert!(note.contains("MATCH"), "{note}");
        assert!(!note.contains("MISMATCH"), "{note}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_pairing_note_no_sidecar_is_unverifiable() {
        let dir = tmpdir("pair_none");
        let snap = dir.join("s.snap");
        let note = pairing_note(&snap, "abc123def456");
        assert!(note.contains("no provenance sidecar"), "{note}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_run_preserve_copies_current_exe() {
        let dir = tmpdir("run");
        let snap = dir.join("s.snap");
        let bindir = dir.join("bins");
        let build = BuildIdentity::new(Some("cafef00dbabe".to_string()), Some(1));

        let report = run_preserve(&snap, &bindir, &build).expect("preserve");
        assert_eq!(report.sha, "cafef00dbabe");
        assert_eq!(report.dest, bindir.join("clean-cafef00dbabe"));
        assert!(report.dest.exists(), "current_exe copied to sha-named path");
        assert!(
            report.pairing.contains("no provenance sidecar"),
            "no sidecar written => unverifiable pairing: {}",
            report.pairing
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
