// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `factory::merge_check`, split out of `merge_check.rs` to keep
//! that file under the 1000-line paragon bound.

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
        identity: Some(
            clean_parser::parse_name(name)
                .expect("fixture source name")
                .into_name(),
        ),
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
        identity: Some(
            clean_parser::parse_name(name)
                .expect("fixture source name")
                .into_name(),
        ),
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
    fs::write(repo.path().join("B.lean"), "axiom riskyAxiom : False\n").expect("write candidate");
    commit_all(repo.path(), "candidate");

    let report = run_merge_check_to_report(repo.path(), "HEAD~1", "HEAD", "test", false, &[])
        .expect("report");

    assert!(!report.accepted());
    assert!(report
        .findings
        .iter()
        .any(|finding| { finding.kind == "new_trust_debt" && finding.message.contains("axiom") }));
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
    assert!(report
        .findings
        .iter()
        .any(|finding| { finding.kind == "new_trust_debt" && finding.message.contains("unsafe") }));
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
    assert!(report
        .findings
        .iter()
        .any(|finding| { finding.kind == "new_trust_debt" && finding.message.contains("sorry") }));
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
        finding.kind == "math_project_hygiene" && finding.message.contains("could not be loaded")
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
