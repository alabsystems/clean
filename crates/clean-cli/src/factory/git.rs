// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small Git wrapper used by the Rust-owned factory queue.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::TempDir;

use super::FactoryOpsError;

pub(crate) fn run_git<I, S>(
    repo_root: &Path,
    args: I,
    cwd: Option<&Path>,
    action: impl Into<String>,
) -> Result<String, FactoryOpsError>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new("git");
    command.arg("-C").arg(repo_root);
    command.args(args);
    if let Some(cwd) = cwd {
        command.current_dir(cwd);
    }

    let output = command.output().map_err(|source| FactoryOpsError::Io {
        path: repo_root.to_owned(),
        source,
    })?;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    if output.status.success() {
        Ok(stdout.trim().to_owned())
    } else {
        let message = format!("{}{}", stdout, stderr).trim().to_owned();
        Err(FactoryOpsError::Git {
            action: action.into(),
            message: if message.is_empty() {
                format!("git exited with {}", output.status)
            } else {
                message
            },
        })
    }
}

pub(crate) fn resolve_commit(repo_root: &Path, rev: &str) -> Result<String, FactoryOpsError> {
    let spec = format!("{rev}^{{commit}}");
    run_git(
        repo_root,
        ["rev-parse", "--verify", spec.as_str()],
        None,
        format!("resolving commit {rev}"),
    )
}

pub(crate) fn symbolic_full_ref(repo_root: &Path, rev: &str) -> Result<String, FactoryOpsError> {
    run_git(
        repo_root,
        ["rev-parse", "--symbolic-full-name", rev],
        None,
        format!("resolving symbolic ref {rev}"),
    )
}

pub(crate) fn status_porcelain(repo_root: &Path) -> Result<Vec<String>, FactoryOpsError> {
    let text = run_git(
        repo_root,
        ["status", "--porcelain=v1", "--untracked-files=normal"],
        None,
        "checking worktree dirtiness",
    )?;
    Ok(text
        .lines()
        .map(str::trim_end)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect())
}

pub(crate) fn changed_files(
    repo_root: &Path,
    base_commit: &str,
    candidate_commit: &str,
) -> Result<Vec<PathBuf>, FactoryOpsError> {
    let range = format!("{base_commit}..{candidate_commit}");
    let text = run_git(
        repo_root,
        [
            "diff",
            "--name-only",
            "--diff-filter=ACDMRT",
            range.as_str(),
        ],
        None,
        "listing changed files",
    )?;
    let mut files = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    files.sort();
    files.dedup();
    Ok(files)
}

pub(crate) fn is_ancestor(
    repo_root: &Path,
    ancestor: &str,
    descendant: &str,
) -> Result<bool, FactoryOpsError> {
    let mut command = Command::new("git");
    command
        .arg("-C")
        .arg(repo_root)
        .args(["merge-base", "--is-ancestor", ancestor, descendant]);
    let output = command.output().map_err(|source| FactoryOpsError::Io {
        path: repo_root.to_owned(),
        source,
    })?;
    match output.status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        _ => {
            let message = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
            .trim()
            .to_owned();
            Err(FactoryOpsError::Git {
                action: "checking merge ancestry".to_owned(),
                message: if message.is_empty() {
                    format!("git exited with {}", output.status)
                } else {
                    message
                },
            })
        }
    }
}

pub(crate) fn update_ref(
    repo_root: &Path,
    full_ref: &str,
    new_commit: &str,
    old_commit: &str,
) -> Result<(), FactoryOpsError> {
    run_git(
        repo_root,
        ["update-ref", full_ref, new_commit, old_commit],
        None,
        format!("updating {full_ref}"),
    )?;
    Ok(())
}

pub(crate) struct WorktreeGuard {
    repo_root: PathBuf,
    _tempdir: TempDir,
    path: PathBuf,
}

impl WorktreeGuard {
    pub(crate) fn create(
        repo_root: &Path,
        label: &str,
        commit: &str,
    ) -> Result<Self, FactoryOpsError> {
        let tempdir = tempfile::tempdir().map_err(|source| FactoryOpsError::Io {
            path: repo_root.to_owned(),
            source,
        })?;
        let path = tempdir.path().join(label);
        let path_arg = path.to_string_lossy().into_owned();
        run_git(
            repo_root,
            ["worktree", "add", "--detach", path_arg.as_str(), commit],
            None,
            format!("creating {label} worktree"),
        )?;
        Ok(Self {
            repo_root: repo_root.to_owned(),
            _tempdir: tempdir,
            path,
        })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for WorktreeGuard {
    fn drop(&mut self) {
        let path_arg = self.path.to_string_lossy().into_owned();
        let _ = Command::new("git")
            .arg("-C")
            .arg(&self.repo_root)
            .args(["worktree", "remove", "--force", path_arg.as_str()])
            .output();
    }
}
