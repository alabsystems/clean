// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Math-project hygiene for `clean factory merge-check`: which math projects a
//! candidate touches, and each project's hygiene verdict read from the
//! candidate checkout rather than the live tree.

use std::path::{Path, PathBuf};

use walkdir::{DirEntry, WalkDir};

use super::{
    path_to_report_string, MathHygieneSummary, MergeFinding, SEVERITY_ERROR, SEVERITY_WARNING,
    STATUS_REJECT,
};
use crate::math_project::{hygiene_report, load_project, resolve_project_path};

pub(super) fn check_math_projects(
    repo_root: &Path,
    candidate_root: &Path,
    math_projects: &[PathBuf],
    findings: &mut Vec<MergeFinding>,
) -> Vec<MathHygieneSummary> {
    math_projects
        .iter()
        .map(|requested| check_math_project(repo_root, candidate_root, requested, findings))
        .collect()
}

pub(super) fn math_project_paths(
    repo_root: &Path,
    candidate_root: &Path,
    configured: &[PathBuf],
    changed_files: &[PathBuf],
) -> Vec<PathBuf> {
    let mut paths = configured.to_vec();
    paths.extend(discover_math_project_manifests(
        repo_root,
        candidate_root,
        changed_files,
    ));
    paths.sort_by_key(|path| project_path_sort_key(repo_root, candidate_root, path));
    paths.dedup_by(|left, right| same_project_path(repo_root, candidate_root, left, right));
    paths
}

fn discover_math_project_manifests(
    repo_root: &Path,
    candidate_root: &Path,
    changed_files: &[PathBuf],
) -> Vec<PathBuf> {
    let mut manifests = Vec::new();
    for entry in WalkDir::new(candidate_root)
        .follow_links(false)
        .into_iter()
        .filter_entry(should_descend_for_manifest_discovery)
        .filter_map(Result::ok)
    {
        if !entry.file_type().is_file() || !is_manifest_candidate(&entry) {
            continue;
        }
        let path = entry.path();
        if !changed_files_touch_project(candidate_root, path, changed_files) {
            continue;
        }
        manifests.push(path_in_repo_namespace(repo_root, candidate_root, path));
    }
    manifests
}

fn changed_files_touch_project(
    candidate_root: &Path,
    project_path: &Path,
    changed_files: &[PathBuf],
) -> bool {
    let project_root = project_path.parent().unwrap_or(candidate_root);
    changed_files.iter().any(|changed| {
        let changed_path = path_in_candidate_namespace(candidate_root, changed);
        changed_path == project_path
    }) || changed_files_reference_manifest_paths(
        candidate_root,
        project_root,
        project_path,
        changed_files,
    )
}

fn changed_files_reference_manifest_paths(
    candidate_root: &Path,
    project_root: &Path,
    project_path: &Path,
    changed_files: &[PathBuf],
) -> bool {
    let Ok(manifest) = load_project(project_path) else {
        return false;
    };
    let mut referenced = Vec::new();
    referenced.extend(manifest.theorem_packs);
    referenced.extend(manifest.obligation_sources);
    referenced.extend(manifest.evidence);
    changed_files.iter().any(|changed| {
        let changed_path = path_in_candidate_namespace(candidate_root, changed);
        referenced
            .iter()
            .map(|path| project_root.join(path))
            .any(|referenced_path| changed_path == referenced_path)
    })
}

fn path_in_candidate_namespace(candidate_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_owned()
    } else {
        candidate_root.join(path)
    }
}

fn should_descend_for_manifest_discovery(entry: &DirEntry) -> bool {
    let name = entry.file_name().to_string_lossy();
    !matches!(
        name.as_ref(),
        ".git" | "target" | ".lake" | ".elan" | ".clean"
    )
}

fn is_manifest_candidate(entry: &DirEntry) -> bool {
    matches!(
        entry.file_name().to_str(),
        Some("math-project.json") | Some("project.json")
    )
}

fn path_in_repo_namespace(repo_root: &Path, candidate_root: &Path, path: &Path) -> PathBuf {
    path.strip_prefix(candidate_root)
        .map(|relative| repo_root.join(relative))
        .unwrap_or_else(|_| path.to_owned())
}

fn project_path_sort_key(repo_root: &Path, candidate_root: &Path, path: &Path) -> String {
    resolve_project_path_in_candidate(repo_root, candidate_root, path)
        .map(|path| path_to_report_string(&path))
        .unwrap_or_else(|_| path_to_report_string(path))
}

fn same_project_path(
    repo_root: &Path,
    candidate_root: &Path,
    left: &PathBuf,
    right: &PathBuf,
) -> bool {
    match (
        resolve_project_path_in_candidate(repo_root, candidate_root, left),
        resolve_project_path_in_candidate(repo_root, candidate_root, right),
    ) {
        (Ok(left), Ok(right)) => left == right,
        (Err(_), Err(_)) => left == right,
        _ => false,
    }
}

fn check_math_project(
    repo_root: &Path,
    candidate_root: &Path,
    requested: &Path,
    findings: &mut Vec<MergeFinding>,
) -> MathHygieneSummary {
    let requested_path = path_to_report_string(requested);
    let project_path = match resolve_project_path_in_candidate(repo_root, candidate_root, requested)
    {
        Ok(path) => path,
        Err(message) => {
            findings.push(MergeFinding {
                severity: SEVERITY_ERROR.to_owned(),
                kind: "math_project_hygiene".to_owned(),
                message,
                fingerprint: Some("math_project_path_scope".to_owned()),
                declarations: Vec::new(),
            });
            return MathHygieneSummary {
                requested_path: requested_path.clone(),
                project_path: requested_path,
                project: None,
                status: STATUS_REJECT.to_owned(),
                errors: 1,
                warnings: 0,
            };
        }
    };
    let project_path_string = path_to_report_string(&project_path);
    let manifest = match load_project(&project_path) {
        Ok(manifest) => manifest,
        Err(error) => {
            findings.push(MergeFinding {
                severity: SEVERITY_ERROR.to_owned(),
                kind: "math_project_hygiene".to_owned(),
                message: format!(
                    "math project `{}` could not be loaded in candidate worktree: {error}",
                    requested.display()
                ),
                fingerprint: None,
                declarations: Vec::new(),
            });
            return MathHygieneSummary {
                requested_path,
                project_path: project_path_string,
                project: None,
                status: STATUS_REJECT.to_owned(),
                errors: 1,
                warnings: 0,
            };
        }
    };

    let report = hygiene_report(&project_path, &manifest);
    let errors = report
        .violations
        .iter()
        .filter(|violation| violation.severity == SEVERITY_ERROR)
        .count()
        + usize::from(manifest.trust_policy.allow_synthetic_sorry);
    let warnings = report
        .violations
        .iter()
        .filter(|violation| violation.severity == SEVERITY_WARNING)
        .count()
        + usize::from(!manifest.trust_policy.require_artifact_replay);

    for violation in report
        .violations
        .iter()
        .filter(|violation| violation.severity == SEVERITY_ERROR)
    {
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "math_project_hygiene".to_owned(),
            message: format!(
                "math project `{}` hygiene blocker {} at {}: {}",
                manifest.project, violation.code, violation.path, violation.message
            ),
            fingerprint: Some(violation.code.to_owned()),
            declarations: Vec::new(),
        });
    }
    if manifest.trust_policy.allow_synthetic_sorry {
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "math_project_hygiene".to_owned(),
            message: format!(
                "math project `{}` hygiene blocker: synthetic sorry is allowed by trust policy",
                manifest.project
            ),
            fingerprint: Some("allow_synthetic_sorry".to_owned()),
            declarations: Vec::new(),
        });
    }

    MathHygieneSummary {
        requested_path,
        project_path: project_path_string,
        project: Some(manifest.project),
        status: report.status.to_owned(),
        errors,
        warnings,
    }
}

fn resolve_project_path_in_candidate(
    repo_root: &Path,
    candidate_root: &Path,
    requested: &Path,
) -> Result<PathBuf, String> {
    let candidate_path = if requested.is_absolute() {
        requested
            .strip_prefix(repo_root)
            .map(|relative| candidate_root.join(relative))
            .map_err(|_| {
                format!(
                    "math project `{}` is outside repo root `{}`; refusing to read live external files",
                    requested.display(),
                    repo_root.display()
                )
            })?
    } else {
        candidate_root.join(requested)
    };
    Ok(resolve_project_path(&candidate_path))
}
