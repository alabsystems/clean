// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transactional Lean-aware merge checks for Rust-owned factory queues.

mod math_projects;

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{Environment, TypeChecker};
use serde::{Deserialize, Serialize};

use super::decl_index::{
    build_index, build_source_index, DeclarationIndex, DeclarationKind, DeclarationRecord,
};
use super::git;
use super::module_scope::{self, ScopeReport};
use super::{FactoryOpsError, MergeCheckArgs};
use math_projects::{check_math_projects, math_project_paths};

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
#[path = "merge_check_tests.rs"]
mod tests;
