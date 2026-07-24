// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transactional Lean-aware merge checks for Rust-owned factory queues.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Environment, TypeChecker};
use serde::{Deserialize, Serialize};
use walkdir::{DirEntry, WalkDir};

use crate::math_project::{hygiene_report, load_project, resolve_project_path};

use super::decl_index::{
    build_index, build_source_index, DeclarationIndex, DeclarationKind, DeclarationRecord,
};
use super::git;
use super::module_scope::{self, ScopeReport};
use super::{FactoryOpsError, MergeCheckArgs};

const MERGE_CHECK_SCHEMA_VERSION: &str = "clean-factory-merge-check-v1";
const STATUS_ACCEPT: &str = "accept";
const STATUS_REJECT: &str = "reject";
const SEVERITY_ERROR: &str = "error";
const SEVERITY_WARNING: &str = "warning";

/// A compact declaration reference embedded in merge findings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct DeclarationRef {
    pub(crate) name: String,
    pub(crate) kind: DeclarationKind,
    pub(crate) source_path: String,
    pub(crate) statement_fingerprint: String,
}

impl From<&DeclarationRecord> for DeclarationRef {
    fn from(record: &DeclarationRecord) -> Self {
        Self {
            name: record.name.clone(),
            kind: record.kind,
            source_path: record.source_path.clone(),
            statement_fingerprint: record.statement_fingerprint.clone(),
        }
    }
}

/// One policy finding produced by a merge check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MergeFinding {
    pub(crate) severity: String,
    pub(crate) kind: String,
    pub(crate) message: String,
    pub(crate) fingerprint: Option<String>,
    pub(crate) declarations: Vec<DeclarationRef>,
}

/// A declaration-level change summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ChangedDeclaration {
    pub(crate) name: String,
    pub(crate) kind: DeclarationKind,
    pub(crate) change: String,
    pub(crate) before_path: Option<String>,
    pub(crate) after_path: Option<String>,
    pub(crate) before_fingerprint: Option<String>,
    pub(crate) after_fingerprint: Option<String>,
}

/// Current checkout state recorded to prove whether dirty state was allowed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct SourceState {
    pub(crate) checked_current_worktree: bool,
    pub(crate) dirty: bool,
    pub(crate) dirty_entries: Vec<String>,
}

/// Compact math-project hygiene result recorded in merge diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MathHygieneSummary {
    pub(crate) requested_path: String,
    pub(crate) project_path: String,
    pub(crate) project: Option<String>,
    pub(crate) status: String,
    pub(crate) errors: usize,
    pub(crate) warnings: usize,
}

/// Summary status for a merge check.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MergeSummary {
    pub(crate) status: String,
    pub(crate) errors: usize,
    pub(crate) warnings: usize,
}

/// Full merge-check report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct MergeCheckReport {
    pub(crate) schema_version: String,
    pub(crate) profile: String,
    pub(crate) repo_root: String,
    pub(crate) base_ref: String,
    pub(crate) candidate_ref: String,
    pub(crate) base_commit: String,
    pub(crate) candidate_commit: String,
    pub(crate) changed_files: Vec<String>,
    pub(crate) changed_lean_files: Vec<String>,
    pub(crate) impacted_lean_files: Vec<String>,
    pub(crate) source_scope: ScopeReport,
    pub(crate) changed_declarations: Vec<ChangedDeclaration>,
    pub(crate) source_state: SourceState,
    pub(crate) math_hygiene: Vec<MathHygieneSummary>,
    pub(crate) findings: Vec<MergeFinding>,
    pub(crate) summary: MergeSummary,
}

impl MergeCheckReport {
    pub(crate) fn accepted(&self) -> bool {
        self.summary.status == STATUS_ACCEPT
    }

    fn reject_message(&self) -> String {
        let reasons = self
            .findings
            .iter()
            .filter(|finding| finding.severity == SEVERITY_ERROR)
            .take(4)
            .map(|finding| finding.message.as_str())
            .collect::<Vec<_>>();
        if reasons.is_empty() {
            "merge policy rejected candidate".to_owned()
        } else {
            reasons.join("; ")
        }
    }
}

pub(crate) fn run_merge_check(args: MergeCheckArgs) -> Result<(), FactoryOpsError> {
    let report = run_merge_check_to_report(
        &args.repo_root,
        &args.base,
        &args.candidate,
        &args.profile,
        true,
        &args.math_projects,
    )?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_human_report(&mut out, &report)?;
    }

    if !report.accepted() {
        return Err(FactoryOpsError::MergeRejected(report.reject_message()));
    }
    Ok(())
}

pub(crate) fn run_merge_check_to_report(
    repo_root: &Path,
    base_ref: &str,
    candidate_ref: &str,
    profile: &str,
    require_clean_current_worktree: bool,
    math_projects: &[PathBuf],
) -> Result<MergeCheckReport, FactoryOpsError> {
    let repo_root = normalize_root(repo_root);
    let source_state = source_state(&repo_root, require_clean_current_worktree)?;
    let base_commit = git::resolve_commit(&repo_root, base_ref)?;
    let candidate_commit = git::resolve_commit(&repo_root, candidate_ref)?;
    let changed_files = git::changed_files(&repo_root, &base_commit, &candidate_commit)?;
    let changed_lean_paths = changed_files
        .iter()
        .filter(|path| path.extension().is_some_and(|ext| ext == "lean"))
        .cloned()
        .collect::<Vec<_>>();
    let changed_lean_set = changed_lean_paths
        .iter()
        .map(|p| path_to_report_string(p))
        .collect::<BTreeSet<_>>();

    let base_worktree = git::WorktreeGuard::create(&repo_root, "base", &base_commit)?;
    let candidate_worktree =
        git::WorktreeGuard::create(&repo_root, "candidate", &candidate_commit)?;
    let source_scope = module_scope::scope_report(candidate_worktree.path(), &changed_lean_paths)?;
    let impacted_lean_paths = source_scope
        .impacted_lean_files
        .iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    let active_lean_paths = source_scope
        .active_lean_files
        .iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>();

    let base_changed_index =
        build_explicit_index(base_worktree.path(), profile, &changed_lean_paths)?;
    let candidate_changed_index =
        build_explicit_index(candidate_worktree.path(), profile, &changed_lean_paths)?;
    let base_impacted_index =
        build_explicit_index(base_worktree.path(), profile, &impacted_lean_paths)?;
    let candidate_impacted_index =
        build_explicit_index(candidate_worktree.path(), profile, &impacted_lean_paths)?;
    let candidate_semantic_index = if changed_lean_paths.is_empty() {
        DeclarationIndex::empty(candidate_worktree.path(), profile)
    } else {
        build_explicit_index(candidate_worktree.path(), profile, &active_lean_paths)?
    };
    let base_source_index = build_source_index(base_worktree.path(), profile)?;
    let candidate_source_index = build_source_index(candidate_worktree.path(), profile)?;

    let mut findings = Vec::new();
    if source_state.dirty {
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "dirty_local_state".to_owned(),
            message: format!(
                "current checkout has {} dirty entries; merge checks run from commits and reject dirty source state",
                source_state.dirty_entries.len()
            ),
            fingerprint: None,
            declarations: Vec::new(),
        });
    }

    push_index_diagnostics("base", &base_changed_index, &mut findings);
    push_index_diagnostics("candidate", &candidate_changed_index, &mut findings);
    push_index_diagnostics("base_impacted", &base_impacted_index, &mut findings);
    push_index_diagnostics(
        "candidate_impacted",
        &candidate_impacted_index,
        &mut findings,
    );
    push_index_diagnostics("base_source", &base_source_index, &mut findings);
    push_index_diagnostics("candidate_source", &candidate_source_index, &mut findings);
    detect_name_collisions(
        &candidate_changed_index,
        &candidate_source_index,
        &changed_lean_set,
        &mut findings,
    );
    detect_duplicate_theorem_statements(
        &candidate_changed_index,
        &candidate_source_index,
        &candidate_semantic_index,
        &changed_lean_set,
        &mut findings,
    );
    detect_new_trust_debt(
        &base_source_index,
        &candidate_source_index,
        &candidate_changed_index,
        &changed_lean_set,
        &mut findings,
    );
    let math_hygiene = check_math_projects(
        &repo_root,
        candidate_worktree.path(),
        &math_project_paths(
            &repo_root,
            candidate_worktree.path(),
            math_projects,
            &changed_files,
        ),
        &mut findings,
    );

    let changed_declarations = summarize_changed_declarations(
        &base_changed_index,
        &candidate_changed_index,
        &base_source_index,
        &candidate_source_index,
        &changed_lean_set,
    );
    let summary = summary_from_findings(&findings);

    Ok(MergeCheckReport {
        schema_version: MERGE_CHECK_SCHEMA_VERSION.to_owned(),
        profile: profile.to_owned(),
        repo_root: repo_root.to_string_lossy().into_owned(),
        base_ref: base_ref.to_owned(),
        candidate_ref: candidate_ref.to_owned(),
        base_commit,
        candidate_commit,
        changed_files: changed_files
            .iter()
            .map(|p| path_to_report_string(p))
            .collect(),
        changed_lean_files: changed_lean_paths
            .iter()
            .map(|p| path_to_report_string(p))
            .collect(),
        impacted_lean_files: impacted_lean_paths
            .iter()
            .map(|p| path_to_report_string(p))
            .collect(),
        source_scope,
        changed_declarations,
        source_state,
        math_hygiene,
        findings,
        summary,
    })
}

fn check_math_projects(
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

fn math_project_paths(
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

fn source_state(
    repo_root: &Path,
    require_clean_current_worktree: bool,
) -> Result<SourceState, FactoryOpsError> {
    if require_clean_current_worktree {
        let dirty_entries = git::status_porcelain(repo_root)?;
        Ok(SourceState {
            checked_current_worktree: true,
            dirty: !dirty_entries.is_empty(),
            dirty_entries,
        })
    } else {
        Ok(SourceState {
            checked_current_worktree: false,
            dirty: false,
            dirty_entries: Vec::new(),
        })
    }
}

fn build_explicit_index(
    root: &Path,
    profile: &str,
    paths: &[PathBuf],
) -> Result<DeclarationIndex, FactoryOpsError> {
    if paths.is_empty() {
        Ok(DeclarationIndex::empty(root, profile))
    } else {
        build_index(root, profile, paths)
    }
}

fn push_index_diagnostics(label: &str, index: &DeclarationIndex, findings: &mut Vec<MergeFinding>) {
    for diagnostic in &index.diagnostics {
        findings.push(MergeFinding {
            severity: diagnostic.severity.clone(),
            kind: "lean_analysis_failed".to_owned(),
            message: format!("{label} {}: {}", diagnostic.path, diagnostic.message),
            fingerprint: None,
            declarations: Vec::new(),
        });
    }
}

fn detect_name_collisions(
    candidate_changed_index: &DeclarationIndex,
    candidate_source_index: &DeclarationIndex,
    changed_lean_set: &BTreeSet<String>,
    findings: &mut Vec<MergeFinding>,
) {
    let changed_names = changed_records(
        candidate_changed_index,
        candidate_source_index,
        changed_lean_set,
    )
    .into_iter()
    .map(|record| record.name.clone())
    .collect::<BTreeSet<_>>();
    if changed_names.is_empty() {
        return;
    }

    for (name, records) in candidate_source_index.by_name() {
        if !changed_names.contains(&name) || records.len() < 2 {
            continue;
        }
        let theorem_collision = records.iter().any(|record| record.kind.is_theorem_like());
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: if theorem_collision {
                "theorem_name_collision".to_owned()
            } else {
                "declaration_name_collision".to_owned()
            },
            message: format!(
                "candidate declares `{name}` {} times after applying changed Lean files",
                records.len()
            ),
            fingerprint: None,
            declarations: records.into_iter().map(DeclarationRef::from).collect(),
        });
    }
}

fn detect_duplicate_theorem_statements(
    candidate_changed_index: &DeclarationIndex,
    candidate_source_index: &DeclarationIndex,
    candidate_semantic_index: &DeclarationIndex,
    changed_lean_set: &BTreeSet<String>,
    findings: &mut Vec<MergeFinding>,
) {
    let changed_names = changed_records(
        candidate_changed_index,
        candidate_source_index,
        changed_lean_set,
    )
    .into_iter()
    .filter(|record| record.kind.is_theorem_like())
    .map(|record| record.name.clone())
    .collect::<BTreeSet<_>>();
    if changed_names.is_empty() {
        return;
    }

    let mut reported_pairs = BTreeSet::new();
    let mut by_statement: BTreeMap<String, Vec<&DeclarationRecord>> = BTreeMap::new();
    for record in &candidate_source_index.records {
        if record.kind.is_theorem_like() {
            by_statement
                .entry(record.statement_fingerprint.clone())
                .or_default()
                .push(record);
        }
    }

    for (fingerprint, records) in by_statement {
        let distinct_names = records
            .iter()
            .map(|record| record.name.as_str())
            .collect::<BTreeSet<_>>();
        if distinct_names.len() < 2 {
            continue;
        }
        if !records
            .iter()
            .any(|record| changed_names.contains(&record.name))
        {
            continue;
        }
        for (left, right) in record_pairs(&records) {
            reported_pairs.insert(name_pair_key(&left.name, &right.name));
        }
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "duplicate_theorem_statement".to_owned(),
            message: format!(
                "candidate contains {} theorem-like declarations with the same normalized statement",
                records.len()
            ),
            fingerprint: Some(fingerprint),
            declarations: records.into_iter().map(DeclarationRef::from).collect(),
        });
    }

    detect_semantic_duplicate_theorem_statements(
        candidate_semantic_index,
        &changed_names,
        &mut reported_pairs,
        findings,
    );
}

fn detect_semantic_duplicate_theorem_statements(
    candidate_semantic_index: &DeclarationIndex,
    changed_names: &BTreeSet<String>,
    reported_pairs: &mut BTreeSet<(String, String)>,
    findings: &mut Vec<MergeFinding>,
) {
    let semantic_records = candidate_semantic_index
        .records
        .iter()
        .filter(|record| record.kind.is_theorem_like() && record.type_expr.is_some())
        .collect::<Vec<_>>();
    let changed_semantic_records = semantic_records
        .iter()
        .copied()
        .filter(|record| changed_names.contains(&record.name))
        .collect::<Vec<_>>();
    if changed_semantic_records.is_empty() {
        return;
    }

    let Some(env) = semantic_environment(candidate_semantic_index, findings) else {
        return;
    };
    let tc = TypeChecker::new(&env);

    for changed in changed_semantic_records {
        let mut duplicates = vec![changed];
        for &other in &semantic_records {
            if changed.name == other.name {
                continue;
            }
            let pair = name_pair_key(&changed.name, &other.name);
            if reported_pairs.contains(&pair) {
                continue;
            }
            if semantic_statements_match(&tc, changed, other) {
                reported_pairs.insert(pair);
                duplicates.push(other);
            }
        }
        if duplicates.len() < 2 {
            continue;
        }
        duplicates.sort_by(|left, right| left.name.cmp(&right.name));
        duplicates.dedup_by(|left, right| left.name == right.name);
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "duplicate_theorem_statement".to_owned(),
            message: format!(
                "candidate contains theorem-like declaration `{}` with a definitionally equal statement already present",
                changed.name
            ),
            fingerprint: Some(changed.type_fingerprint.clone()),
            declarations: duplicates.into_iter().map(DeclarationRef::from).collect(),
        });
    }
}

fn semantic_environment(
    index: &DeclarationIndex,
    findings: &mut Vec<MergeFinding>,
) -> Option<Environment> {
    let mut env = match Environment::try_with_prelude() {
        Ok(env) => env,
        Err(error) => {
            findings.push(MergeFinding {
                severity: SEVERITY_ERROR.to_owned(),
                kind: "lean_analysis_failed".to_owned(),
                message: format!("semantic duplicate theorem check initialization failed: {error}"),
                fingerprint: None,
                declarations: Vec::new(),
            });
            return None;
        }
    };
    if let Err(error) = env.init_pprod() {
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "lean_analysis_failed".to_owned(),
            message: format!("semantic duplicate theorem check initialization failed: {error}"),
            fingerprint: None,
            declarations: Vec::new(),
        });
        return None;
    }

    let mut seen = BTreeSet::new();
    let constants = index
        .records
        .iter()
        .filter_map(DeclarationRecord::to_constant_info)
        .filter(|info| {
            let name = info.name.clone();
            env.get_const(&name).is_none() && seen.insert(name)
        })
        .collect::<Vec<_>>();
    // SOUNDNESS: extend_constants_unchecked is acceptable here because `env` is
    // analysis-only scaffolding, NOT a trust-bearing store. It backs a single TypeChecker
    // used only for is_def_eq duplicate-theorem-statement detection (semantic_statements_match
    // below); it is local, never persisted to an .olean/.mathverse artifact, never
    // re-exported, never added to the kernel TCB, and is dropped when the caller returns.
    // A wrong/refused def-eq can at worst emit a spurious or missed duplicate finding — a
    // precision/recall defect in a heuristic merge gate, never an unsound proof. Residual
    // trust: types come from the candidate (untrusted, pre-merge) source with no structural
    // check, so a malformed term reaches is_def_eq unvalidated; on hostile input the worst
    // case is engine misbehavior (DoS of the gate), not kernel unsoundness. Cheap mitigation:
    // extend_constants_structural. Tracking: data/unchecked_decl_ratchet.json (extend_constants block, #4).
    env.extend_constants_unchecked(constants.into_iter());
    Some(env)
}

fn semantic_statements_match(
    tc: &TypeChecker<'_>,
    left: &DeclarationRecord,
    right: &DeclarationRecord,
) -> bool {
    if left.type_fingerprint == right.type_fingerprint {
        return true;
    }
    match (&left.type_expr, &right.type_expr) {
        (Some(left_type), Some(right_type)) => tc.is_def_eq(left_type, right_type),
        _ => false,
    }
}

fn record_pairs<'a>(
    records: &'a [&'a DeclarationRecord],
) -> Vec<(&'a DeclarationRecord, &'a DeclarationRecord)> {
    let mut pairs = Vec::new();
    for idx in 0..records.len() {
        for next in idx + 1..records.len() {
            pairs.push((records[idx], records[next]));
        }
    }
    pairs
}

fn name_pair_key(left: &str, right: &str) -> (String, String) {
    if left <= right {
        (left.to_owned(), right.to_owned())
    } else {
        (right.to_owned(), left.to_owned())
    }
}

fn detect_new_trust_debt(
    base_source_index: &DeclarationIndex,
    candidate_source_index: &DeclarationIndex,
    candidate_changed_index: &DeclarationIndex,
    changed_lean_set: &BTreeSet<String>,
    findings: &mut Vec<MergeFinding>,
) {
    let base_by_name = base_source_index.by_name();
    for record in changed_records(
        candidate_changed_index,
        candidate_source_index,
        changed_lean_set,
    ) {
        if !record.trust.has_debt() {
            continue;
        }

        let before = base_by_name.get(&record.name).and_then(|records| {
            records
                .iter()
                .copied()
                .find(|base| base.source_path == record.source_path)
                .or_else(|| records.first().copied())
        });
        let declaration_changed = before.is_none_or(|base| {
            base.statement_fingerprint != record.statement_fingerprint
                || base.source_path != record.source_path
        });
        let trust_worse =
            before.is_some_and(|base| record.trust.is_strictly_worse_than(&base.trust));

        if !declaration_changed && !trust_worse {
            continue;
        }

        let mut labels = record.trust.debt_labels();
        if labels.is_empty() {
            labels.push("trust_debt".to_owned());
        }
        findings.push(MergeFinding {
            severity: SEVERITY_ERROR.to_owned(),
            kind: "new_trust_debt".to_owned(),
            message: format!(
                "changed declaration `{}` carries rejected trust debt: {}",
                record.name,
                labels.join(", ")
            ),
            fingerprint: Some(record.statement_fingerprint.clone()),
            declarations: vec![DeclarationRef::from(record)],
        });
    }
}

fn summarize_changed_declarations(
    base_changed_index: &DeclarationIndex,
    candidate_changed_index: &DeclarationIndex,
    base_source_index: &DeclarationIndex,
    candidate_source_index: &DeclarationIndex,
    changed_lean_set: &BTreeSet<String>,
) -> Vec<ChangedDeclaration> {
    let base_by_name = base_source_index.by_name();
    let candidate_by_name = candidate_source_index.by_name();
    let mut changed = Vec::new();

    for record in changed_records(
        candidate_changed_index,
        candidate_source_index,
        changed_lean_set,
    ) {
        let before = base_by_name
            .get(&record.name)
            .and_then(|records| records.first().copied());
        let change = match before {
            None => "added",
            Some(before) if before.statement_fingerprint != record.statement_fingerprint => {
                "modified"
            }
            Some(before) if before.source_path != record.source_path => "moved",
            Some(_) => continue,
        };
        changed.push(ChangedDeclaration {
            name: record.name.clone(),
            kind: record.kind,
            change: change.to_owned(),
            before_path: before.map(|record| record.source_path.clone()),
            after_path: Some(record.source_path.clone()),
            before_fingerprint: before.map(|record| record.statement_fingerprint.clone()),
            after_fingerprint: Some(record.statement_fingerprint.clone()),
        });
    }

    let candidate_names = candidate_by_name.keys().cloned().collect::<BTreeSet<_>>();
    for record in changed_records(base_changed_index, base_source_index, changed_lean_set) {
        if candidate_names.contains(&record.name) {
            continue;
        }
        changed.push(ChangedDeclaration {
            name: record.name.clone(),
            kind: record.kind,
            change: "removed".to_owned(),
            before_path: Some(record.source_path.clone()),
            after_path: None,
            before_fingerprint: Some(record.statement_fingerprint.clone()),
            after_fingerprint: None,
        });
    }

    changed.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then(left.change.cmp(&right.change))
    });
    changed
}

fn changed_records<'a>(
    primary_changed_index: &'a DeclarationIndex,
    source_index: &'a DeclarationIndex,
    changed_lean_set: &BTreeSet<String>,
) -> Vec<&'a DeclarationRecord> {
    let primary = primary_changed_index
        .records
        .iter()
        .filter(|record| changed_lean_set.contains(&record.source_path))
        .collect::<Vec<_>>();
    if !primary.is_empty() {
        primary
    } else {
        source_index
            .records
            .iter()
            .filter(|record| changed_lean_set.contains(&record.source_path))
            .collect()
    }
}

fn summary_from_findings(findings: &[MergeFinding]) -> MergeSummary {
    let errors = findings
        .iter()
        .filter(|finding| finding.severity == SEVERITY_ERROR)
        .count();
    let warnings = findings
        .iter()
        .filter(|finding| finding.severity == SEVERITY_WARNING)
        .count();
    MergeSummary {
        status: if errors == 0 {
            STATUS_ACCEPT.to_owned()
        } else {
            STATUS_REJECT.to_owned()
        },
        errors,
        warnings,
    }
}

fn render_human_report(out: &mut impl Write, report: &MergeCheckReport) -> io::Result<()> {
    writeln!(out, "summary: {}", report.summary.status)?;
    writeln!(out, "base: {} ({})", report.base_ref, report.base_commit)?;
    writeln!(
        out,
        "candidate: {} ({})",
        report.candidate_ref, report.candidate_commit
    )?;
    writeln!(
        out,
        "changed_lean_files: {}",
        report.changed_lean_files.len()
    )?;
    writeln!(
        out,
        "changed_declarations: {}",
        report.changed_declarations.len()
    )?;
    if !report.math_hygiene.is_empty() {
        writeln!(out, "math_hygiene: {}", report.math_hygiene.len())?;
        for hygiene in &report.math_hygiene {
            writeln!(
                out,
                "  {} {} errors={} warnings={}",
                hygiene.status, hygiene.project_path, hygiene.errors, hygiene.warnings
            )?;
        }
    }
    if !report.findings.is_empty() {
        writeln!(out, "findings:")?;
        for finding in &report.findings {
            writeln!(
                out,
                "  {} {}: {}",
                finding.severity, finding.kind, finding.message
            )?;
        }
    }
    Ok(())
}

fn normalize_root(root: &Path) -> PathBuf {
    let path = if root.is_absolute() {
        root.to_owned()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(root)
    };
    std::fs::canonicalize(&path).unwrap_or(path)
}

fn path_to_report_string(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::super::decl_index::TrustRecord;
    use super::*;
    use clean_kernel::env::{ConstantKind, Reducibility};
    use clean_kernel::{Expr, Level, Name};
    use std::fs;
    use std::process::Command;

    fn git(repo: &Path, args: &[&str]) {
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
  "project": "factory-blocked",
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

    fn write_clean_math_project(repo: &Path, path: &str) {
        let project_path = repo.join(path);
        let project_root = project_path.parent().expect("project parent");
        fs::create_dir_all(project_root.join("theorem_packs")).expect("mkdir theorem packs");
        fs::create_dir_all(project_root.join("obligations")).expect("mkdir obligations");
        fs::write(
            project_root.join("theorem_packs/clean.lean"),
            "theorem factory_clean_true : True := True.intro\n",
        )
        .expect("write theorem pack");
        fs::write(
            project_root.join("obligations/clean.json"),
            r#"{
  "schema_version": "clean-obligation-v1",
  "project": "factory-clean",
  "domain_profile": "sat-pb",
  "producer": {
    "system": "factory-tests",
    "commit": "fixture-clean"
  },
  "goal": {
    "expr": "True",
    "pretty": "True"
  },
  "trust_policy": "test-policy"
}
"#,
        )
        .expect("write obligation");
        fs::write(
            project_path,
            r#"{
  "schema_version": "clean-math-project-v1",
  "project": "factory-clean",
  "domain_profile": "sat-pb",
  "owner": "factory-tests",
  "theorem_packs": ["theorem_packs/clean.lean"],
  "obligation_sources": ["obligations/clean.json"],
  "trust_policy": {
    "name": "test-policy",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": false,
    "forbidden_trust_markers": ["synthetic_sorry"]
  }
}
"#,
        )
        .expect("write math project");
    }

    fn record(name: &str, path: &str, fp: &str) -> DeclarationRecord {
        DeclarationRecord {
            name: name.to_owned(),
            kind: DeclarationKind::Theorem,
            source_path: path.to_owned(),
            span: None,
            source: super::super::decl_index::RecordSource::SourceScan,
            statement_fingerprint: fp.to_owned(),
            type_fingerprint: fp.to_owned(),
            value_fingerprint: None,
            conclusion_head: None,
            symbol_refs: Vec::new(),
            trust: TrustRecord::default(),
            type_expr: None,
            value_expr: None,
            level_params: Vec::new(),
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            constant_kind: ConstantKind::Theorem,
        }
    }

    fn record_with_type(name: &str, path: &str, fp: &str, type_expr: Expr) -> DeclarationRecord {
        let mut record = record(name, path, fp);
        record.type_expr = Some(type_expr);
        record
    }

    fn definition_record(
        name: &str,
        path: &str,
        type_expr: Expr,
        value_expr: Expr,
    ) -> DeclarationRecord {
        DeclarationRecord {
            name: name.to_owned(),
            kind: DeclarationKind::Definition,
            source_path: path.to_owned(),
            span: None,
            source: super::super::decl_index::RecordSource::Kernel,
            statement_fingerprint: format!("{name}:definition"),
            type_fingerprint: format!("{name}:type"),
            value_fingerprint: Some(format!("{name}:value")),
            conclusion_head: None,
            symbol_refs: Vec::new(),
            trust: TrustRecord::default(),
            type_expr: Some(type_expr),
            value_expr: Some(value_expr),
            level_params: Vec::new(),
            is_reducible: false,
            reducibility: Reducibility::Regular(1),
            constant_kind: ConstantKind::Definition,
        }
    }

    fn index(records: Vec<DeclarationRecord>) -> DeclarationIndex {
        DeclarationIndex {
            schema_version: "test".to_owned(),
            root: ".".to_owned(),
            profile: "test".to_owned(),
            files_scanned: 1,
            records,
            diagnostics: Vec::new(),
        }
    }

    #[test]
    fn duplicate_statement_finding_requires_changed_member() {
        let changed = index(vec![record("new", "A.lean", "same")]);
        let source = index(vec![
            record("old", "B.lean", "same"),
            record("new", "A.lean", "same"),
        ]);
        let changed_files = BTreeSet::from(["A.lean".to_owned()]);
        let mut findings = Vec::new();

        detect_duplicate_theorem_statements(
            &changed,
            &source,
            &DeclarationIndex::empty(Path::new("."), "test"),
            &changed_files,
            &mut findings,
        );

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].kind, "duplicate_theorem_statement");
    }

    #[test]
    fn duplicate_statement_finding_uses_semantic_type_equality() {
        let ty = Expr::sort(Level::zero());
        let changed = index(vec![record("new", "A.lean", "changed-source")]);
        let source = index(vec![
            record("old", "B.lean", "old-source"),
            record("new", "A.lean", "changed-source"),
        ]);
        let semantic = index(vec![
            record_with_type("old", "B.lean", "old-source", ty.clone()),
            record_with_type("new", "A.lean", "changed-source", ty),
        ]);
        let changed_files = BTreeSet::from(["A.lean".to_owned()]);
        let mut findings = Vec::new();

        detect_duplicate_theorem_statements(
            &changed,
            &source,
            &semantic,
            &changed_files,
            &mut findings,
        );

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].kind, "duplicate_theorem_statement");
        assert!(findings[0].message.contains("definitionally equal"));
    }

    #[test]
    fn duplicate_statement_finding_unfolds_semantic_definitions() {
        let alias = Name::from_string("Alias");
        let changed = index(vec![record("new", "A.lean", "changed-source")]);
        let source = index(vec![
            record("old", "B.lean", "old-source"),
            record("new", "A.lean", "changed-source"),
        ]);
        let semantic = index(vec![
            definition_record("Alias", "Defs.lean", Expr::type_(), Expr::prop()),
            record_with_type("old", "B.lean", "old-source", Expr::prop()),
            record_with_type(
                "new",
                "A.lean",
                "changed-source",
                Expr::const_(alias, vec![]),
            ),
        ]);
        let changed_files = BTreeSet::from(["A.lean".to_owned()]);
        let mut findings = Vec::new();

        detect_duplicate_theorem_statements(
            &changed,
            &source,
            &semantic,
            &changed_files,
            &mut findings,
        );

        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].kind, "duplicate_theorem_statement");
        assert!(findings[0].message.contains("definitionally equal"));
    }

    #[test]
    fn merge_check_rejects_dirty_current_worktree() {
        let repo = init_repo();
        fs::write(
            repo.path().join("A.lean"),
            "theorem CleanBase : True := True.intro\n",
        )
        .expect("write base");
        commit_all(repo.path(), "base");
        fs::write(
            repo.path().join("B.lean"),
            "theorem CleanCandidate : True := True.intro\n",
        )
        .expect("write candidate");
        commit_all(repo.path(), "candidate");
        fs::write(repo.path().join("dirty.txt"), "unrelated local state\n").expect("write dirty");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", true, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report.source_state.dirty);
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.kind == "dirty_local_state"));
    }

    #[test]
    fn merge_check_rejects_changed_theorem_name_collision() {
        let repo = init_repo();
        fs::write(
            repo.path().join("A.lean"),
            "theorem collide : True := True.intro\n",
        )
        .expect("write base");
        commit_all(repo.path(), "base");
        fs::write(
            repo.path().join("B.lean"),
            "theorem collide : True := True.intro\n",
        )
        .expect("write candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.kind == "theorem_name_collision"));
    }

    #[test]
    fn merge_check_rejects_changed_duplicate_theorem_statement() {
        let repo = init_repo();
        fs::write(
            repo.path().join("A.lean"),
            "theorem originalName : True := True.intro\n",
        )
        .expect("write base");
        commit_all(repo.path(), "base");
        fs::write(
            repo.path().join("B.lean"),
            "theorem duplicateStatement : True := True.intro\n",
        )
        .expect("write candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report
            .findings
            .iter()
            .any(|finding| finding.kind == "duplicate_theorem_statement"));
    }

    #[test]
    fn merge_check_rejects_new_axiom_trust_debt() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("B.lean"), "axiom riskyAxiom : False\n")
            .expect("write candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "new_trust_debt" && finding.message.contains("axiom")
        }));
    }

    #[test]
    fn merge_check_rejects_new_unsafe_trust_debt() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("B.lean"), "unsafe def danger : Nat := 1\n")
            .expect("write candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "new_trust_debt" && finding.message.contains("unsafe")
        }));
    }

    #[test]
    fn merge_check_rejects_new_sorry_trust_debt() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(
            repo.path().join("B.lean"),
            "theorem unfinished : True := by\n  sorry\n",
        )
        .expect("write candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "new_trust_debt" && finding.message.contains("sorry")
        }));
    }

    #[test]
    fn merge_check_reports_deleted_lean_declarations() {
        let repo = init_repo();
        fs::write(
            repo.path().join("A.lean"),
            "theorem removedDecl : True := True.intro\n",
        )
        .expect("write base");
        commit_all(repo.path(), "base");
        fs::remove_file(repo.path().join("A.lean")).expect("remove");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert_eq!(report.changed_lean_files, vec!["A.lean"]);
        assert!(report
            .changed_declarations
            .iter()
            .any(|decl| { decl.name == "removedDecl" && decl.change == "removed" }));
    }

    #[test]
    fn merge_check_uses_lake_import_dependent_scope() {
        let repo = init_repo();
        fs::write(
            repo.path().join("lakefile.lean"),
            "package test\nlean_lib Test\n",
        )
        .expect("write lakefile");
        fs::write(repo.path().join("A.lean"), "def a : Nat := 1\n").expect("write A");
        fs::write(repo.path().join("B.lean"), "import A\ndef b : Nat := 2\n").expect("write B");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("A.lean"), "def a : Nat := 2\n").expect("write A candidate");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert_eq!(report.source_scope.kind, "lake_workspace");
        assert!(report.impacted_lean_files.contains(&"A.lean".to_owned()));
        assert!(report.impacted_lean_files.contains(&"B.lean".to_owned()));
    }

    #[test]
    fn merge_check_does_not_scan_everything_for_non_lean_changes() {
        let repo = init_repo();
        fs::write(
            repo.path().join("A.lean"),
            "theorem existingOne : True := True.intro\n",
        )
        .expect("write A");
        fs::write(
            repo.path().join("B.lean"),
            "theorem existingTwo : True := True.intro\n",
        )
        .expect("write B");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "documentation only\n").expect("write docs");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert!(report.changed_lean_files.is_empty());
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.kind != "duplicate_theorem_statement"));
        assert!(report.math_hygiene.is_empty());
    }

    #[test]
    fn merge_check_ignores_unchanged_failing_math_project_for_unrelated_candidate() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        write_blocking_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "documentation only\n").expect("write docs");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert!(report.math_hygiene.is_empty());
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.kind != "math_project_hygiene"));
    }

    #[test]
    fn merge_check_does_not_auto_check_root_project_for_unrelated_file_change() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        write_blocking_math_project(repo.path(), "project.json");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "documentation only\n").expect("write docs");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert!(report.math_hygiene.is_empty());
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.kind != "math_project_hygiene"));
    }

    #[test]
    fn merge_check_auto_checks_changed_math_project_evidence_path() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        fs::create_dir_all(repo.path().join("evidence")).expect("mkdir evidence");
        fs::write(repo.path().join("evidence/status.json"), "{}\n").expect("write evidence");
        fs::write(
            repo.path().join("project.json"),
            r#"{
  "schema_version": "clean-math-project-v1",
  "project": "factory-blocked-evidence",
  "domain_profile": "sat-pb",
  "owner": "factory-tests",
  "evidence": ["evidence/status.json"],
  "trust_policy": {
    "name": "test-policy",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": true
  }
}
"#,
        )
        .expect("write math project");
        commit_all(repo.path(), "base");
        fs::write(
            repo.path().join("evidence/status.json"),
            "{\"changed\":true}\n",
        )
        .expect("write changed evidence");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(
            report.math_hygiene[0].project.as_deref(),
            Some("factory-blocked-evidence")
        );
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("synthetic sorry is allowed")
        }));
    }

    #[test]
    fn merge_check_rejects_auto_discovered_malformed_math_project_manifest() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::create_dir_all(repo.path().join("Math")).expect("mkdir math");
        fs::write(repo.path().join("Math/project.json"), "{ not json\n")
            .expect("write malformed manifest");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(report.math_hygiene[0].project, None);
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("could not be loaded")
        }));
    }

    #[test]
    fn merge_check_rejects_auto_discovered_wrong_schema_math_project_manifest() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::create_dir_all(repo.path().join("Math")).expect("mkdir math");
        fs::write(
            repo.path().join("Math/project.json"),
            r#"{
  "schema_version": "wrong-schema",
  "project": "factory-wrong-schema",
  "domain_profile": "sat-pb",
  "owner": "factory-tests",
  "trust_policy": {
    "name": "test-policy",
    "require_artifact_replay": true,
    "allow_synthetic_sorry": false,
    "forbidden_trust_markers": ["synthetic_sorry"]
  }
}
"#,
        )
        .expect("write wrong schema manifest");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(
            report.math_hygiene[0].project.as_deref(),
            Some("factory-wrong-schema")
        );
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("MP001")
                && finding.message.contains("schema_version")
        }));
    }

    #[test]
    fn merge_check_rejects_explicit_absolute_math_project_outside_repo_root() {
        let repo = init_repo();
        let external = tempfile::tempdir().expect("external tempdir");
        write_clean_math_project(external.path(), "project.json");
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "documentation only\n").expect("write docs");
        commit_all(repo.path(), "candidate");

        let external_project = external.path().join("project.json");
        let report = run_merge_check_to_report(
            repo.path(),
            "HEAD~1",
            "HEAD",
            "test",
            false,
            &[external_project],
        )
        .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(report.math_hygiene[0].project, None);
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding
                    .message
                    .contains("refusing to read live external files")
        }));
    }

    #[test]
    fn merge_check_rejects_explicit_math_project_hygiene_blocker() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "math project change\n").expect("write docs");
        write_blocking_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(
            repo.path(),
            "HEAD~1",
            "HEAD",
            "test",
            false,
            &[PathBuf::from("Math/project.json")],
        )
        .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(
            report.math_hygiene[0].project.as_deref(),
            Some("factory-blocked")
        );
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("synthetic sorry is allowed")
        }));
    }

    #[test]
    fn merge_check_rejects_explicit_unchanged_math_project_hygiene_blocker() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        write_blocking_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "documentation only\n").expect("write docs");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(
            repo.path(),
            "HEAD~1",
            "HEAD",
            "test",
            false,
            &[PathBuf::from("Math/project.json")],
        )
        .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("synthetic sorry is allowed")
        }));
    }

    #[test]
    fn merge_check_rejects_referenced_math_project_hygiene_blocker() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "math project change\n").expect("write docs");
        write_blocking_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(!report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(
            report.math_hygiene[0].project.as_deref(),
            Some("factory-blocked")
        );
        assert!(report.findings.iter().any(|finding| {
            finding.kind == "math_project_hygiene"
                && finding.message.contains("synthetic sorry is allowed")
        }));
    }

    #[test]
    fn merge_check_accepts_referenced_clean_math_project_hygiene() {
        let repo = init_repo();
        fs::write(repo.path().join("A.lean"), "def base : Nat := 1\n").expect("write base");
        commit_all(repo.path(), "base");
        fs::write(repo.path().join("README.md"), "math project change\n").expect("write docs");
        write_clean_math_project(repo.path(), "Math/project.json");
        commit_all(repo.path(), "candidate");

        let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
            .expect("report");

        assert!(report.accepted());
        assert_eq!(report.math_hygiene.len(), 1);
        assert_eq!(
            report.math_hygiene[0].project.as_deref(),
            Some("factory-clean")
        );
        assert_eq!(report.math_hygiene[0].status, "pass");
        assert!(report
            .findings
            .iter()
            .all(|finding| finding.kind != "math_project_hygiene"));
    }
}
