// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned transactional merge queue for Lean declaration changes.

use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};

use super::git;
use super::merge_check::{run_merge_check_to_report, MergeCheckReport};
use super::{FactoryOpsError, QueueCommands, QueueProcessNextArgs, QueuePushArgs, QueueStatusArgs};

pub(crate) const DEFAULT_QUEUE_PATH: &str = "data/merge_queue.json";

const QUEUE_SCHEMA_VERSION: &str = "clean-factory-merge-queue-v1";
const STATUS_QUEUED: &str = "queued";
const STATUS_PROCESSING: &str = "processing";
const STATUS_FAILED: &str = "failed";
const STATUS_MERGED: &str = "merged";

/// Durable queue state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct QueueState {
    pub(crate) schema_version: String,
    pub(crate) next_id: u64,
    pub(crate) updated_at: String,
    pub(crate) entries: Vec<QueueEntry>,
}

impl QueueState {
    fn empty() -> Self {
        Self {
            schema_version: QUEUE_SCHEMA_VERSION.to_owned(),
            next_id: 1,
            updated_at: now_string(),
            entries: Vec::new(),
        }
    }
}

/// One queued candidate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct QueueEntry {
    pub(crate) id: String,
    pub(crate) target_ref: String,
    pub(crate) target_commit: String,
    pub(crate) base_ref: String,
    pub(crate) priority: i64,
    pub(crate) note: Option<String>,
    pub(crate) status: String,
    pub(crate) attempts: u32,
    pub(crate) queued_at: String,
    pub(crate) updated_at: String,
    pub(crate) processing_started_at: Option<String>,
    pub(crate) validated_commit: Option<String>,
    pub(crate) merged_commit: Option<String>,
    pub(crate) diagnostic_path: Option<String>,
    pub(crate) last_error: Option<String>,
}

/// Result emitted by `queue process-next`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct QueueProcessResult {
    schema_version: String,
    status: String,
    entry: QueueEntry,
    merge_summary: Option<String>,
}

pub(crate) fn run_queue_command(command: QueueCommands) -> Result<(), FactoryOpsError> {
    match command {
        QueueCommands::Push(args) => queue_push(args),
        QueueCommands::Status(args) => queue_status(args),
        QueueCommands::ProcessNext(args) => queue_process_next(args),
    }
}

fn queue_push(args: QueuePushArgs) -> Result<(), FactoryOpsError> {
    let repo_root = normalize_root(&args.repo_root);
    let queue_path = normalize_root(&args.queue);
    let _lock = QueueLock::acquire(&queue_path)?;
    let mut state = read_state(&queue_path)?;
    let target_commit = git::resolve_commit(&repo_root, &args.target)?;
    let id = format!("mq-{}", state.next_id);
    state.next_id += 1;
    let now = now_string();
    let entry = QueueEntry {
        id,
        target_ref: args.target,
        target_commit,
        base_ref: args.base,
        priority: args.priority,
        note: args.note,
        status: STATUS_QUEUED.to_owned(),
        attempts: 0,
        queued_at: now.clone(),
        updated_at: now,
        processing_started_at: None,
        validated_commit: None,
        merged_commit: None,
        diagnostic_path: None,
        last_error: None,
    };
    state.entries.push(entry.clone());
    state.updated_at = now_string();
    write_state(&queue_path, &state)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    writeln!(
        out,
        "queued {} {} -> {}",
        entry.id, entry.target_ref, entry.base_ref
    )?;
    Ok(())
}

fn queue_status(args: QueueStatusArgs) -> Result<(), FactoryOpsError> {
    let queue_path = normalize_root(&args.queue);
    let state = read_state(&queue_path)?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&state)?)?;
    } else {
        render_human_status(&mut out, &state)?;
    }
    Ok(())
}

fn queue_process_next(args: QueueProcessNextArgs) -> Result<(), FactoryOpsError> {
    let repo_root = normalize_root(&args.repo_root);
    let queue_path = normalize_root(&args.queue);
    let _lock = QueueLock::acquire(&queue_path)?;
    let mut state = read_state(&queue_path)?;
    let selected = select_next_entry(&state).ok_or(FactoryOpsError::QueueEmpty)?;

    let now = now_string();
    state.entries[selected].status = STATUS_PROCESSING.to_owned();
    state.entries[selected].attempts += 1;
    state.entries[selected].updated_at = now.clone();
    state.entries[selected].processing_started_at = Some(now);
    state.entries[selected].last_error = None;
    let entry = state.entries[selected].clone();
    state.updated_at = now_string();
    write_state(&queue_path, &state)?;

    let outcome = process_entry(
        &repo_root,
        &queue_path,
        &entry,
        &args.profile,
        &args.verify_cmd,
        &args.math_projects,
    );
    apply_outcome(&mut state.entries[selected], outcome);
    state.updated_at = now_string();
    write_state(&queue_path, &state)?;

    let result = QueueProcessResult {
        schema_version: QUEUE_SCHEMA_VERSION.to_owned(),
        status: state.entries[selected].status.clone(),
        entry: state.entries[selected].clone(),
        merge_summary: state.entries[selected].last_error.clone(),
    };
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&result)?)?;
    } else {
        writeln!(out, "{} {}", result.entry.id, result.entry.status)?;
        if let Some(error) = &result.entry.last_error {
            writeln!(out, "error: {error}")?;
        }
        if let Some(path) = &result.entry.diagnostic_path {
            writeln!(out, "diagnostic: {path}")?;
        }
    }

    if result.status == STATUS_FAILED {
        return Err(FactoryOpsError::MergeRejected(
            result
                .entry
                .last_error
                .unwrap_or_else(|| "queue entry failed".to_owned()),
        ));
    }
    Ok(())
}

#[derive(Debug)]
struct ProcessOutcome {
    status: String,
    validated_commit: Option<String>,
    merged_commit: Option<String>,
    diagnostic_path: Option<String>,
    last_error: Option<String>,
}

fn process_entry(
    repo_root: &Path,
    queue_path: &Path,
    entry: &QueueEntry,
    profile: &str,
    verify_cmd: &Option<String>,
    math_projects: &[PathBuf],
) -> ProcessOutcome {
    match try_process_entry(
        repo_root,
        queue_path,
        entry,
        profile,
        verify_cmd,
        math_projects,
    ) {
        Ok(outcome) => outcome,
        Err(error) => ProcessOutcome {
            status: STATUS_FAILED.to_owned(),
            validated_commit: None,
            merged_commit: None,
            diagnostic_path: None,
            last_error: Some(error.to_string()),
        },
    }
}

fn try_process_entry(
    repo_root: &Path,
    queue_path: &Path,
    entry: &QueueEntry,
    profile: &str,
    verify_cmd: &Option<String>,
    math_projects: &[PathBuf],
) -> Result<ProcessOutcome, FactoryOpsError> {
    let base_commit = git::resolve_commit(repo_root, &entry.base_ref)?;
    if !git::is_ancestor(repo_root, &base_commit, &entry.target_commit)? {
        return Ok(ProcessOutcome {
            status: STATUS_FAILED.to_owned(),
            validated_commit: None,
            merged_commit: None,
            diagnostic_path: None,
            last_error: Some(format!(
                "candidate {} is not a fast-forward descendant of base {} ({base_commit})",
                entry.target_commit, entry.base_ref
            )),
        });
    }

    let report = run_merge_check_to_report(
        repo_root,
        &base_commit,
        &entry.target_commit,
        profile,
        false,
        math_projects,
    )?;
    let diagnostic_path = write_diagnostic(queue_path, entry, &report)?;
    if !report.accepted() {
        return Ok(ProcessOutcome {
            status: STATUS_FAILED.to_owned(),
            validated_commit: Some(entry.target_commit.clone()),
            merged_commit: None,
            diagnostic_path: Some(diagnostic_path),
            last_error: Some("merge check rejected candidate".to_owned()),
        });
    }

    if let Some(command) = verify_cmd {
        run_verify_command(repo_root, &entry.target_commit, command)?;
    }

    let full_ref = git::symbolic_full_ref(repo_root, &entry.base_ref)?;
    git::update_ref(repo_root, &full_ref, &entry.target_commit, &base_commit)?;
    Ok(ProcessOutcome {
        status: STATUS_MERGED.to_owned(),
        validated_commit: Some(entry.target_commit.clone()),
        merged_commit: Some(entry.target_commit.clone()),
        diagnostic_path: Some(diagnostic_path),
        last_error: None,
    })
}

fn apply_outcome(entry: &mut QueueEntry, outcome: ProcessOutcome) {
    entry.status = outcome.status;
    entry.validated_commit = outcome.validated_commit;
    entry.merged_commit = outcome.merged_commit;
    entry.diagnostic_path = outcome.diagnostic_path;
    entry.last_error = outcome.last_error;
    entry.updated_at = now_string();
}

fn run_verify_command(
    repo_root: &Path,
    target_commit: &str,
    command: &str,
) -> Result<(), FactoryOpsError> {
    let worktree = git::WorktreeGuard::create(repo_root, "verify", target_commit)?;
    let output = Command::new("sh")
        .arg("-lc")
        .arg(command)
        .current_dir(worktree.path())
        .output()
        .map_err(|source| FactoryOpsError::Io {
            path: worktree.path().to_owned(),
            source,
        })?;
    if output.status.success() {
        Ok(())
    } else {
        let message = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
        .trim()
        .to_owned();
        Err(FactoryOpsError::Git {
            action: "running queue verify command".to_owned(),
            message: if message.is_empty() {
                format!("verify command exited with {}", output.status)
            } else {
                message
            },
        })
    }
}

fn write_diagnostic(
    queue_path: &Path,
    entry: &QueueEntry,
    report: &MergeCheckReport,
) -> Result<String, FactoryOpsError> {
    let dir = queue_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("merge_queue_diagnostics");
    fs::create_dir_all(&dir).map_err(|source| FactoryOpsError::Io {
        path: dir.clone(),
        source,
    })?;
    let path = dir.join(format!("{}-attempt-{}.json", entry.id, entry.attempts));
    fs::write(&path, serde_json::to_vec_pretty(report)?).map_err(|source| FactoryOpsError::Io {
        path: path.clone(),
        source,
    })?;
    Ok(path.to_string_lossy().into_owned())
}

fn select_next_entry(state: &QueueState) -> Option<usize> {
    state
        .entries
        .iter()
        .enumerate()
        .filter(|(_, entry)| entry.status == STATUS_QUEUED)
        .min_by(|(_, left), (_, right)| {
            left.priority
                .cmp(&right.priority)
                .then_with(|| left.queued_at.cmp(&right.queued_at))
                .then_with(|| left.id.cmp(&right.id))
        })
        .map(|(idx, _)| idx)
}

fn read_state(path: &Path) -> Result<QueueState, FactoryOpsError> {
    if !path.exists() {
        return Ok(QueueState::empty());
    }
    let text = fs::read_to_string(path).map_err(|source| FactoryOpsError::Io {
        path: path.to_owned(),
        source,
    })?;
    if text.trim().is_empty() {
        return Ok(QueueState::empty());
    }
    let state: QueueState = serde_json::from_str(&text)?;
    if state.schema_version != QUEUE_SCHEMA_VERSION {
        return Err(FactoryOpsError::QueueState(format!(
            "expected schema {QUEUE_SCHEMA_VERSION}, found {}",
            state.schema_version
        )));
    }
    Ok(state)
}

fn write_state(path: &Path, state: &QueueState) -> Result<(), FactoryOpsError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| FactoryOpsError::Io {
            path: parent.to_owned(),
            source,
        })?;
    }
    fs::write(path, serde_json::to_vec_pretty(state)?).map_err(|source| FactoryOpsError::Io {
        path: path.to_owned(),
        source,
    })
}

fn render_human_status(out: &mut impl Write, state: &QueueState) -> io::Result<()> {
    writeln!(out, "schema: {}", state.schema_version)?;
    writeln!(out, "entries: {}", state.entries.len())?;
    for entry in &state.entries {
        writeln!(
            out,
            "{} {} priority={} {} -> {}",
            entry.id, entry.status, entry.priority, entry.target_ref, entry.base_ref
        )?;
    }
    Ok(())
}

struct QueueLock {
    path: PathBuf,
}

impl QueueLock {
    fn acquire(queue_path: &Path) -> Result<Self, FactoryOpsError> {
        if let Some(parent) = queue_path.parent() {
            fs::create_dir_all(parent).map_err(|source| FactoryOpsError::Io {
                path: parent.to_owned(),
                source,
            })?;
        }
        let lock_path = queue_path.with_extension("json.lock");
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&lock_path)
            .map_err(|source| {
                if source.kind() == io::ErrorKind::AlreadyExists {
                    FactoryOpsError::QueueLocked {
                        path: lock_path.clone(),
                    }
                } else {
                    FactoryOpsError::Io {
                        path: lock_path.clone(),
                        source,
                    }
                }
            })?;
        writeln!(
            file,
            "pid={} acquired_at={}",
            std::process::id(),
            now_string()
        )
        .map_err(|source| FactoryOpsError::Io {
            path: lock_path.clone(),
            source,
        })?;
        Ok(Self { path: lock_path })
    }
}

impl Drop for QueueLock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn normalize_root(path: &Path) -> PathBuf {
    let path = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    };
    fs::canonicalize(&path).unwrap_or(path)
}

fn now_string() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or_default();
    secs.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::process::Command;

    fn git_output(repo: &Path, args: &[&str]) -> String {
        let output = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(args)
            .output()
            .expect("git");
        assert!(
            output.status.success(),
            "git {:?} failed\nstdout:\n{}\nstderr:\n{}",
            args,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    }

    fn git(repo: &Path, args: &[&str]) {
        let _ = git_output(repo, args);
    }

    fn commit_all(repo: &Path, message: &str) {
        git(repo, &["add", "."]);
        git(
            repo,
            &[
                "-c",
                "user.name=clean Test",
                "-c",
                "user.email=clean@example.invalid",
                "commit",
                "-m",
                message,
            ],
        );
    }

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().expect("tempdir");
        git(dir.path(), &["init", "-b", "main"]);
        dir
    }

    fn write_blocking_math_project(repo: &Path, path: &str) {
        let project_path = repo.join(path);
        fs::create_dir_all(project_path.parent().expect("project parent")).expect("mkdir");
        fs::write(
            project_path,
            r#"{
  "schema_version": "clean-math-project-v1",
  "project": "queue-blocked",
  "domain_profile": "sat-pb",
  "owner": "factory-tests",
  "trust_policy": {
    "name": "test-policy",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": true
  }
}
"#,
        )
        .expect("write math project");
    }

    #[test]
    fn selects_lowest_priority_queued_entry() {
        let mut state = QueueState::empty();
        state.entries.push(QueueEntry {
            id: "mq-1".to_owned(),
            target_ref: "a".to_owned(),
            target_commit: "a".to_owned(),
            base_ref: "main".to_owned(),
            priority: 100,
            note: None,
            status: STATUS_QUEUED.to_owned(),
            attempts: 0,
            queued_at: "1".to_owned(),
            updated_at: "1".to_owned(),
            processing_started_at: None,
            validated_commit: None,
            merged_commit: None,
            diagnostic_path: None,
            last_error: None,
        });
        state.entries.push(QueueEntry {
            id: "mq-2".to_owned(),
            target_ref: "b".to_owned(),
            target_commit: "b".to_owned(),
            base_ref: "main".to_owned(),
            priority: 10,
            note: None,
            status: STATUS_QUEUED.to_owned(),
            attempts: 0,
            queued_at: "2".to_owned(),
            updated_at: "2".to_owned(),
            processing_started_at: None,
            validated_commit: None,
            merged_commit: None,
            diagnostic_path: None,
            last_error: None,
        });

        assert_eq!(select_next_entry(&state), Some(1));
    }

    #[test]
    fn process_next_lands_fast_forward_candidate_with_clean_report() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def baseVal : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        let base_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        fs::write(repo.path().join("B.lean"), "def candidateVal : Nat := 2\n")
            .expect("write candidate");
        commit_all(repo.path(), "candidate");
        let target_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        git(
            repo.path(),
            &["checkout", "--detach", target_commit.as_str()],
        );
        git(
            repo.path(),
            &[
                "update-ref",
                "refs/heads/main",
                base_commit.as_str(),
                target_commit.as_str(),
            ],
        );
        let queue_path = repo.path().join("merge_queue.json");

        queue_push(QueuePushArgs {
            target: target_commit.clone(),
            base: "main".to_owned(),
            priority: 100,
            note: Some("test landing".to_owned()),
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
        })
        .expect("push queue entry");
        queue_process_next(QueueProcessNextArgs {
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
            profile: "test".to_owned(),
            verify_cmd: Some("test -f B.lean".to_owned()),
            math_projects: Vec::new(),
            json: true,
        })
        .expect("process queue entry");

        assert_eq!(
            git_output(repo.path(), &["rev-parse", "main"]),
            target_commit
        );
        assert_ne!(base_commit, target_commit);
        let state = read_state(&queue_path).expect("queue state");
        assert_eq!(state.entries.len(), 1);
        assert_eq!(state.entries[0].status, STATUS_MERGED);
        assert_eq!(
            state.entries[0].merged_commit.as_deref(),
            Some(target_commit.as_str())
        );
        let diagnostic_path = state.entries[0]
            .diagnostic_path
            .as_ref()
            .expect("diagnostic path");
        assert!(Path::new(diagnostic_path).is_file());
    }

    #[test]
    fn process_next_ignores_dirty_active_checkout_math_project_absent_from_candidate() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def baseVal : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        let base_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        fs::write(repo.path().join("B.lean"), "def candidateVal : Nat := 2\n")
            .expect("write candidate");
        commit_all(repo.path(), "candidate");
        let target_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        git(
            repo.path(),
            &["checkout", "--detach", target_commit.as_str()],
        );
        git(
            repo.path(),
            &[
                "update-ref",
                "refs/heads/main",
                base_commit.as_str(),
                target_commit.as_str(),
            ],
        );
        write_blocking_math_project(repo.path(), "Math/project.json");
        let queue_path = repo.path().join("merge_queue.json");

        queue_push(QueuePushArgs {
            target: target_commit.clone(),
            base: "main".to_owned(),
            priority: 100,
            note: Some("test active dirty ignored".to_owned()),
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
        })
        .expect("push queue entry");
        queue_process_next(QueueProcessNextArgs {
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
            profile: "test".to_owned(),
            verify_cmd: None,
            math_projects: Vec::new(),
            json: true,
        })
        .expect("process queue entry");

        assert_eq!(
            git_output(repo.path(), &["rev-parse", "main"]),
            target_commit
        );
        let state = read_state(&queue_path).expect("queue state");
        assert_eq!(state.entries.len(), 1);
        assert_eq!(state.entries[0].status, STATUS_MERGED);
    }

    #[test]
    fn process_next_writes_diagnostic_for_referenced_math_hygiene_rejection() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def baseVal : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        let base_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        fs::write(repo.path().join("B.lean"), "def candidateVal : Nat := 2\n")
            .expect("write candidate");
        write_blocking_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "candidate");
        let target_commit = git_output(repo.path(), &["rev-parse", "HEAD"]);
        git(
            repo.path(),
            &["checkout", "--detach", target_commit.as_str()],
        );
        git(
            repo.path(),
            &[
                "update-ref",
                "refs/heads/main",
                base_commit.as_str(),
                target_commit.as_str(),
            ],
        );
        let queue_path = repo.path().join("merge_queue.json");

        queue_push(QueuePushArgs {
            target: target_commit.clone(),
            base: "main".to_owned(),
            priority: 100,
            note: Some("test rejection".to_owned()),
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
        })
        .expect("push queue entry");
        let error = queue_process_next(QueueProcessNextArgs {
            queue: queue_path.clone(),
            repo_root: repo.path().to_owned(),
            profile: "test".to_owned(),
            verify_cmd: None,
            math_projects: Vec::new(),
            json: true,
        })
        .expect_err("math hygiene should reject queue entry");

        assert!(error.to_string().contains("merge check rejected candidate"));
        let state = read_state(&queue_path).expect("queue state");
        assert_eq!(state.entries.len(), 1);
        assert_eq!(state.entries[0].status, STATUS_FAILED);
        let diagnostic_path = state.entries[0]
            .diagnostic_path
            .as_ref()
            .expect("diagnostic path");
        let diagnostic = fs::read_to_string(diagnostic_path).expect("read diagnostic");
        assert!(diagnostic.contains("\"math_hygiene\""));
        assert!(diagnostic.contains("synthetic sorry is allowed"));
    }
}
