// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Durable project-local proof task lifecycle state.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    display_project_relative, issue_plan_report, load_json, obligation_fingerprint,
    IssuePlanFilingMetadata, IssuePlanRankingSignals, MathObligation, MathProjectError,
    MathProjectManifest,
};

pub const TASK_STORE_SCHEMA_VERSION: &str = "clean-math-task-store-v1";
pub const TASK_LIST_REPORT_SCHEMA_VERSION: &str = "clean-math-task-list-v1";
pub const TASK_STATUS_REPORT_SCHEMA_VERSION: &str = "clean-math-task-status-v1";
pub const TASK_UPDATE_REPORT_SCHEMA_VERSION: &str = "clean-math-task-update-v1";
pub const DEFAULT_TASK_STORE_PATH: &str = ".clean/math-tasks.json";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MathTaskStore {
    pub schema_version: String,
    pub project: String,
    pub project_root: String,
    pub tasks: Vec<MathTask>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MathTask {
    pub id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub obligation_fingerprint: Option<String>,
    pub title: String,
    pub status: TaskStatus,
    #[serde(default)]
    pub notes: Vec<String>,
    #[serde(default)]
    pub blockers: Vec<String>,
    pub issue: TaskIssueProjection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TaskStatus {
    Open,
    InProgress,
    Blocked,
    Done,
}

impl TaskStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::InProgress => "in-progress",
            Self::Blocked => "blocked",
            Self::Done => "done",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TaskIssueProjection {
    pub filing_key: String,
    pub dedupe_key: String,
    #[serde(default)]
    pub ranking: IssuePlanRankingSignals,
    pub phase: String,
    pub phase_title: String,
    pub workstream: String,
    pub priority: String,
    pub scope: String,
    pub files: Vec<String>,
    pub labels: Vec<String>,
    pub owners: Vec<String>,
    pub blocking_categories: Vec<String>,
    #[serde(default)]
    pub filing_metadata: IssuePlanFilingMetadata,
    pub dependencies: Vec<String>,
    pub acceptance: Vec<String>,
    pub verification_command: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathTaskListReport {
    pub schema_version: &'static str,
    pub project: String,
    pub task_file: String,
    pub total: usize,
    pub by_status: BTreeMap<String, usize>,
    pub tasks: Vec<MathTask>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathTaskStatusReport {
    pub schema_version: &'static str,
    pub project: String,
    pub task_file: String,
    pub task: MathTask,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MathTaskUpdateReport {
    pub schema_version: &'static str,
    pub project: String,
    pub task_file: String,
    pub task: MathTask,
    pub wrote: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaskUpdate {
    pub status: Option<TaskStatus>,
    pub append_notes: Vec<String>,
    pub append_blockers: Vec<String>,
    pub clear_notes: bool,
    pub clear_blockers: bool,
}

pub fn task_store_path(project_path: &Path) -> PathBuf {
    project_root(project_path).join(DEFAULT_TASK_STORE_PATH)
}

pub fn list_tasks(
    project_path: &Path,
    manifest: &MathProjectManifest,
) -> Result<MathTaskListReport, MathProjectError> {
    let (store_path, store) = load_or_project_store(project_path, manifest)?;
    Ok(MathTaskListReport {
        schema_version: TASK_LIST_REPORT_SCHEMA_VERSION,
        project: manifest.project.clone(),
        task_file: store_path.display().to_string(),
        total: store.tasks.len(),
        by_status: count_by_status(&store.tasks),
        tasks: store.tasks,
    })
}

pub fn task_status(
    project_path: &Path,
    manifest: &MathProjectManifest,
    selector: &str,
) -> Result<MathTaskStatusReport, MathProjectError> {
    let (store_path, store) = load_or_project_store(project_path, manifest)?;
    let task = resolve_task(&store.tasks, selector, project_path)?.clone();
    Ok(MathTaskStatusReport {
        schema_version: TASK_STATUS_REPORT_SCHEMA_VERSION,
        project: manifest.project.clone(),
        task_file: store_path.display().to_string(),
        task,
    })
}

pub fn update_task(
    project_path: &Path,
    manifest: &MathProjectManifest,
    selector: &str,
    update: TaskUpdate,
) -> Result<MathTaskUpdateReport, MathProjectError> {
    let (store_path, mut store) = load_or_project_store(project_path, manifest)?;
    let index = resolve_task_index(&store.tasks, selector, project_path)?;
    if let Some(status) = update.status {
        store.tasks[index].status = status;
    }
    if update.clear_notes {
        store.tasks[index].notes.clear();
    }
    if update.clear_blockers {
        store.tasks[index].blockers.clear();
    }
    append_unique_trimmed(&mut store.tasks[index].notes, update.append_notes);
    append_unique_trimmed(&mut store.tasks[index].blockers, update.append_blockers);
    if !store.tasks[index].blockers.is_empty() && store.tasks[index].status != TaskStatus::Done {
        store.tasks[index].status = TaskStatus::Blocked;
    }
    let task = store.tasks[index].clone();
    write_task_store_atomic(&store_path, &store)?;
    Ok(MathTaskUpdateReport {
        schema_version: TASK_UPDATE_REPORT_SCHEMA_VERSION,
        project: manifest.project.clone(),
        task_file: store_path.display().to_string(),
        task,
        wrote: true,
    })
}

pub fn load_or_project_store(
    project_path: &Path,
    manifest: &MathProjectManifest,
) -> Result<(PathBuf, MathTaskStore), MathProjectError> {
    let root = project_root(project_path);
    let store_path = task_store_path(project_path);
    let previous = load_json::<MathTaskStore>(&store_path).ok();
    let mut store = projected_store(project_path, manifest, previous.as_ref());
    if previous.as_ref() != Some(&store) {
        write_task_store_atomic(&store_path, &store)?;
    }
    store.tasks.sort_by(|left, right| {
        left.status
            .cmp(&right.status)
            .then_with(|| left.issue.phase.cmp(&right.issue.phase))
            .then_with(|| left.issue.workstream.cmp(&right.issue.workstream))
            .then_with(|| left.id.cmp(&right.id))
    });
    store.project_root = root.display().to_string();
    Ok((store_path, store))
}

fn projected_store(
    project_path: &Path,
    manifest: &MathProjectManifest,
    previous: Option<&MathTaskStore>,
) -> MathTaskStore {
    let root = project_root(project_path);
    let mut previous_by_id = BTreeMap::new();
    if let Some(previous) = previous {
        for task in &previous.tasks {
            previous_by_id.insert(task.id.clone(), task);
        }
    }

    let mut tasks = issue_plan_report(project_path, manifest)
        .rows
        .into_iter()
        .map(|row| {
            let obligation_fingerprint =
                obligation_fingerprint_for_issue_files(&root, manifest, &row.files);
            let id = obligation_fingerprint
                .clone()
                .unwrap_or_else(|| format!("issue:{}", stable_hash(&row.dedupe_key)));
            let previous = previous_by_id.get(&id);
            MathTask {
                id,
                obligation_fingerprint,
                title: row.title,
                status: previous.map(|task| task.status).unwrap_or(TaskStatus::Open),
                notes: previous
                    .map(|task| task.notes.clone())
                    .unwrap_or_else(Vec::new),
                blockers: previous
                    .map(|task| task.blockers.clone())
                    .unwrap_or_else(Vec::new),
                issue: TaskIssueProjection {
                    filing_key: row.filing_key,
                    dedupe_key: row.dedupe_key,
                    ranking: row.ranking,
                    phase: row.phase.to_owned(),
                    phase_title: row.phase_title.to_owned(),
                    workstream: row.workstream,
                    priority: row.priority.to_owned(),
                    scope: row.scope,
                    files: row.files,
                    labels: row.labels,
                    owners: row.owners,
                    blocking_categories: row.blocking_categories,
                    filing_metadata: row.filing_metadata,
                    dependencies: row.dependencies,
                    acceptance: row.acceptance,
                    verification_command: row.verification_command,
                },
            }
        })
        .collect::<Vec<_>>();
    tasks.sort_by(|left, right| left.id.cmp(&right.id));
    tasks.dedup_by(|left, right| left.id == right.id);
    MathTaskStore {
        schema_version: TASK_STORE_SCHEMA_VERSION.to_owned(),
        project: manifest.project.clone(),
        project_root: root.display().to_string(),
        tasks,
    }
}

fn obligation_fingerprint_for_issue_files(
    root: &Path,
    manifest: &MathProjectManifest,
    files: &[String],
) -> Option<String> {
    let obligation_sources = manifest
        .obligation_sources
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    for file in files {
        if !obligation_sources.contains(file.as_str()) {
            continue;
        }
        let Ok(obligation) = load_json::<MathObligation>(&root.join(file)) else {
            continue;
        };
        return Some(obligation_fingerprint(&obligation));
    }
    None
}

fn resolve_task<'a>(
    tasks: &'a [MathTask],
    selector: &str,
    project_path: &Path,
) -> Result<&'a MathTask, MathProjectError> {
    let index = resolve_task_index(tasks, selector, project_path)?;
    Ok(&tasks[index])
}

fn resolve_task_index(
    tasks: &[MathTask],
    selector: &str,
    project_path: &Path,
) -> Result<usize, MathProjectError> {
    let normalized = resolve_selector(selector, project_path);
    let mut matches = tasks
        .iter()
        .enumerate()
        .filter(|(_, task)| task_matches(task, selector, &normalized))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    matches.sort_unstable();
    matches.dedup();
    match matches.as_slice() {
        [index] => Ok(*index),
        [] => Err(MathProjectError::Validation(format!(
            "no math task matches `{selector}`"
        ))),
        _ => Err(MathProjectError::Validation(format!(
            "math task selector `{selector}` is ambiguous"
        ))),
    }
}

fn resolve_selector(selector: &str, project_path: &Path) -> String {
    let path = Path::new(selector);
    if path.exists() {
        if let Ok(obligation) = load_json::<MathObligation>(path) {
            return obligation_fingerprint(&obligation);
        }
    }
    let root = project_root(project_path);
    let project_relative = root.join(selector);
    if project_relative.exists() {
        if let Ok(obligation) = load_json::<MathObligation>(&project_relative) {
            return obligation_fingerprint(&obligation);
        }
    }
    selector.to_owned()
}

fn task_matches(task: &MathTask, raw: &str, normalized: &str) -> bool {
    task.id == normalized
        || task.id == raw
        || task
            .obligation_fingerprint
            .as_deref()
            .is_some_and(|fingerprint| fingerprint == normalized || fingerprint.starts_with(raw))
        || task.issue.dedupe_key == raw
        || task.issue.filing_key == raw
}

fn count_by_status(tasks: &[MathTask]) -> BTreeMap<String, usize> {
    let mut counts = BTreeMap::new();
    for task in tasks {
        *counts.entry(task.status.as_str().to_owned()).or_insert(0) += 1;
    }
    counts
}

fn append_unique_trimmed(target: &mut Vec<String>, values: Vec<String>) {
    for value in values {
        let trimmed = value.trim();
        if !trimmed.is_empty() && !target.iter().any(|existing| existing == trimmed) {
            target.push(trimmed.to_owned());
        }
    }
}

fn write_task_store_atomic(path: &Path, store: &MathTaskStore) -> Result<(), MathProjectError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| MathProjectError::Io {
            path: parent.to_owned(),
            source,
        })?;
    }
    let contents =
        serde_json::to_string_pretty(store).map_err(|source| MathProjectError::Json {
            path: path.to_owned(),
            source,
        })?;
    let tmp_path = path.with_extension(format!("json.tmp.{}", std::process::id()));
    {
        let mut file = fs::File::create(&tmp_path).map_err(|source| MathProjectError::Io {
            path: tmp_path.clone(),
            source,
        })?;
        file.write_all(contents.as_bytes())
            .and_then(|_| file.write_all(b"\n"))
            .and_then(|_| file.sync_all())
            .map_err(|source| MathProjectError::Io {
                path: tmp_path.clone(),
                source,
            })?;
    }
    fs::rename(&tmp_path, path).map_err(|source| MathProjectError::Io {
        path: path.to_owned(),
        source,
    })
}

fn stable_hash(value: &str) -> String {
    let digest = Sha256::digest(value.as_bytes());
    digest
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()[..16]
        .to_owned()
}

fn project_root(project_path: &Path) -> PathBuf {
    project_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .to_owned()
}

fn _project_relative_task_file(project_path: &Path) -> String {
    let root = project_root(project_path);
    display_project_relative(&root, &task_store_path(project_path))
}
