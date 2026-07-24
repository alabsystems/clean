// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed source-state guards for authority evidence recording.

use std::path::{Path, PathBuf};

use anyhow::bail;
use clean_mathverse::env_fingerprint::{EnvFingerprint, GitDirtyState};

#[derive(Debug, Clone)]
pub(crate) struct AuthoritySourceGuard {
    source_root: PathBuf,
    command: &'static str,
    start_state: GitDirtyState,
}

impl AuthoritySourceGuard {
    pub(crate) fn capture_clean(
        source_root: impl AsRef<Path>,
        command: &'static str,
    ) -> anyhow::Result<Self> {
        let source_root = source_root.as_ref().to_path_buf();
        let start_state = EnvFingerprint::capture_git_dirty_state(&source_root)?;
        reject_dirty_state(&source_root, command, "start", &start_state)?;
        Ok(Self {
            source_root,
            command,
            start_state,
        })
    }

    pub(crate) fn ensure_unchanged(&self, phase: &'static str) -> anyhow::Result<()> {
        let current = EnvFingerprint::capture_git_dirty_state(&self.source_root)?;
        reject_dirty_state(&self.source_root, self.command, phase, &current)?;
        if current != self.start_state {
            bail!(
                "{} refused to record authority evidence because source state under `{}` changed between command start and {phase}",
                self.command,
                self.source_root.display()
            );
        }
        Ok(())
    }
}

fn reject_dirty_state(
    source_root: &Path,
    command: &str,
    phase: &str,
    state: &GitDirtyState,
) -> anyhow::Result<()> {
    if state.git_status_clean == Some(false) {
        let digest = state
            .dirty_entries_sha256
            .as_deref()
            .unwrap_or("missing-dirty-entry-digest");
        bail!(
            "{command} refused to record authority evidence because source root `{}` is a dirty git worktree at {phase} (dirty_entries={}, dirty_entries_sha256={digest})",
            source_root.display(),
            state.dirty_entry_count
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::process::Command;

    use super::*;

    fn git(args: &[&str], root: &Path) {
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(args)
            .output()
            .expect("run git");
        assert!(
            output.status.success(),
            "git {:?} failed: {}",
            args,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn clean_git_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        git(&["init"], dir.path());
        git(
            &["config", "user.email", "clean@example.invalid"],
            dir.path(),
        );
        git(&["config", "user.name", "Clean Test"], dir.path());
        fs::write(
            dir.path().join("lean-toolchain"),
            "leanprover/lean4:v4.0.0\n",
        )
        .expect("write toolchain");
        git(&["add", "lean-toolchain"], dir.path());
        git(&["commit", "-m", "initial"], dir.path());
        dir
    }

    #[test]
    fn authority_source_guard_rejects_dirty_git_start_state() {
        let dir = clean_git_repo();
        fs::write(dir.path().join("dirty.lean"), "-- dirty\n").expect("write dirty file");

        let err = AuthoritySourceGuard::capture_clean(dir.path(), "clean test")
            .expect_err("dirty authority source must fail closed");

        let message = err.to_string();
        assert!(message.contains("dirty git worktree"));
        assert!(message.contains("dirty_entries="));
    }

    #[test]
    fn authority_source_guard_rejects_changed_source_before_recording() {
        let dir = clean_git_repo();
        let guard =
            AuthoritySourceGuard::capture_clean(dir.path(), "clean test").expect("clean start");

        fs::write(dir.path().join("changed.lean"), "-- changed\n").expect("write changed file");

        let err = guard
            .ensure_unchanged("authority evidence write")
            .expect_err("changed authority source must fail closed");
        assert!(err.to_string().contains("dirty git worktree"));
    }
}
