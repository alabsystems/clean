// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 4) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use crate::cmd_replacement::*;

#[test]
fn replacement_status_tracks_rust_first_python_migration_inventory() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let tooling = &report.rust_first_tooling;
    let command_ids: Vec<&str> = tooling.commands.iter().map(|row| row.id).collect();

    assert_eq!(tooling.issue.number, 3706);
    assert_eq!(tooling.owner_slot, "Slot 6");
    assert!(tooling.launch_ready);
    assert_eq!(tooling.overall_status, ToolMigrationStatus::RustOwned);
    assert_eq!(
        tooling
            .counts
            .get(&ToolMigrationStatus::Transitional)
            .copied(),
        None
    );
    assert_eq!(
        tooling.counts.get(&ToolMigrationStatus::Demoted).copied(),
        Some(3)
    );
    assert_eq!(
        tooling.counts.get(&ToolMigrationStatus::RustOwned).copied(),
        Some(4)
    );
    assert_eq!(
        command_ids,
        vec![
            "docs-metrics-sync",
            "system-health-release-json",
            "trust-boundary-audit-report",
            "benchmark-publication-check",
            "benchmark-publication-launch",
            "release-issue-hygiene",
            "mathverse-download-pytest",
        ]
    );
    assert!(tooling.commands.iter().all(|row| row.owner_slot == "Slot 6"
        && row.issue.number == 3706
        && !row.removal_condition.is_empty()));
    assert!(tooling
        .commands
        .iter()
        .filter(|row| row.status != ToolMigrationStatus::Demoted)
        .all(|row| row.replacement_critical));
    let docs_metrics_row = tooling
        .commands
        .iter()
        .find(|row| row.id == "docs-metrics-sync")
        .expect("docs metrics migration row");
    assert_eq!(docs_metrics_row.status, ToolMigrationStatus::Demoted);
    assert!(!docs_metrics_row.replacement_critical);
    assert_eq!(docs_metrics_row.source_artifact, "docs/SOURCE_INVENTORY.md");
    assert!(docs_metrics_row
        .planned_rust_surface
        .contains("non-launch diagnostic"));
    assert!(docs_metrics_row
        .removal_condition
        .contains("Demoted out of replacement launch evidence"));
    assert!(docs_metrics_row.blocker.contains("non-launch diagnostic"));
    assert!(docs_metrics_row
        .blocker
        .contains("cannot satisfy or block Lean4 replacement readiness"));
    let system_health_row = tooling
        .commands
        .iter()
        .find(|row| row.id == "system-health-release-json")
        .expect("system-health migration row");
    assert_eq!(system_health_row.status, ToolMigrationStatus::RustOwned);
    assert!(system_health_row
        .removal_condition
        .contains("tracked Cargo.lock presence"));
    assert!(system_health_row
        .removal_condition
        .contains("local Rust toolchain availability"));
    assert!(system_health_row
        .removal_condition
        .contains("committed AY Git-graph validation"));
    assert!(system_health_row
        .removal_condition
        .contains("remote-main freshness"));
    assert!(system_health_row
        .blocker
        .contains("no longer launch evidence"));
    assert!(system_health_row.blocker.contains("legacy diagnostic"));
    assert!(!system_health_row.blocker.contains("lockfile"));
    assert!(!system_health_row.blocker.contains("ay reachability checks"));
    assert!(tooling
        .commands
        .iter()
        .any(|row| row.command == "python3 scripts/sync_readme_metrics.py --check"));
    let trust_boundary_row = tooling
        .commands
        .iter()
        .find(|row| row.id == "trust-boundary-audit-report")
        .expect("trust-boundary audit migration row");
    assert_eq!(trust_boundary_row.status, ToolMigrationStatus::RustOwned);
    assert!(trust_boundary_row
        .planned_rust_surface
        .starts_with("clean replacement trust-boundary-audit"));
    assert!(trust_boundary_row
        .removal_condition
        .contains("groups hits deterministically"));
    assert!(trust_boundary_row
        .blocker
        .contains("No Python wrapper is required"));
    let benchmark_launch_row = tooling
        .commands
        .iter()
        .find(|row| row.id == "benchmark-publication-launch")
        .expect("benchmark publication launch migration row");
    assert_eq!(
        benchmark_launch_row.command,
        "python3 scripts/check_benchmark_publication.py --check --launch"
    );
    assert_eq!(benchmark_launch_row.status, ToolMigrationStatus::Demoted);
    assert!(!benchmark_launch_row.replacement_critical);
    assert_ne!(
            benchmark_launch_row.status,
            ToolMigrationStatus::RustOwned,
            "benchmark publication launch must not become RustOwned merely because the Rust launch skeleton exists"
        );
    assert!(benchmark_launch_row
        .source_artifact
        .contains("reports/benchmarks/publication/current.json"));
    assert_eq!(
            benchmark_launch_row.planned_rust_surface,
            "clean bench publication-check --launch --json (accepted benchmark lane; non-launch diagnostic for Lean4 replacement readiness)"
        );
    assert!(benchmark_launch_row
        .removal_condition
        .contains("benchmark publication evidence is accepted"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("not a Lean4 replacement launch blocker"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("Rust clean bench publication-check --launch --json surface"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("published-status"));
    assert!(benchmark_launch_row.removal_condition.contains("freshness"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("reachable commits"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("dirty-evidence rejection"));
    assert!(benchmark_launch_row
        .removal_condition
        .contains("publication_commit artifact hash rejection"));
    assert!(benchmark_launch_row
        .blocker
        .contains("Accepted benchmark lane"));
    assert!(benchmark_launch_row
        .blocker
        .contains("non-launch diagnostic audit checks"));
    assert!(benchmark_launch_row
        .blocker
        .contains("cannot satisfy or block Lean4 replacement readiness"));
    assert!(benchmark_launch_row.blocker.contains("publication parity"));
    let issue_hygiene_row = tooling
        .commands
        .iter()
        .find(|row| row.id == "release-issue-hygiene")
        .expect("release issue hygiene migration row");
    assert_eq!(
        issue_hygiene_row.command,
        "python3 scripts/release_issue_hygiene.py --fetch"
    );
    assert_eq!(issue_hygiene_row.status, ToolMigrationStatus::RustOwned);
    assert!(issue_hygiene_row.replacement_critical);
    assert!(issue_hygiene_row
        .planned_rust_surface
        .contains("read-only live gh issue list fetch"));
    assert!(issue_hygiene_row
        .planned_rust_surface
        .contains("offline snapshot parser"));
    assert!(issue_hygiene_row
        .planned_rust_surface
        .contains("replacement status JSON alone is not sufficient"));
    assert!(issue_hygiene_row
        .removal_condition
        .contains("Rust-owned launch gate"));
    assert!(issue_hygiene_row
        .removal_condition
        .contains("--input validates offline snapshots"));
    assert!(issue_hygiene_row
        .removal_condition
        .contains("non_ready_issues missing_fields"));
    assert!(issue_hygiene_row
        .blocker
        .contains("No Python wrapper is required for release issue hygiene launch evidence"));
    assert!(issue_hygiene_row
        .blocker
        .contains("fail-closed on gh failures"));
}

#[test]
fn release_issue_hygiene_fetch_limit_zero_fails_closed_before_gh() {
    let report = ReleaseIssueHygieneReport::from_args(&ReleaseIssueHygieneArgs {
        json: true,
        fetch: true,
        input: None,
        limit: 0,
    });
    let json = serde_json::to_string(&report).expect("serialize issue hygiene report");

    assert_eq!(report.schema_version, RELEASE_ISSUE_HYGIENE_SCHEMA_VERSION);
    assert!(!report.ready);
    assert_eq!(report.status, "not_ready");
    assert_eq!(report.input_source.mode, "live_fetch");
    assert!(report.input_source.fetch_requested);
    assert_eq!(report.input_source.limit, 0);
    assert!(report.non_ready_issues.is_empty());
    for required in RELEASE_ISSUE_REQUIRED_FIELDS {
        assert!(report.required_issue_fields.contains(required));
    }
    for watched in RELEASE_ISSUE_WATCHED_LABELS {
        assert!(report.watched_labels.contains(watched));
    }
    for required_json_field in [
        "non_ready_issues",
        "missing_fields",
        "suggested_actions",
        "Release decision:",
        "limit",
        "positive --limit",
    ] {
        assert!(
            json.contains(required_json_field),
            "issue hygiene JSON must name {required_json_field}"
        );
    }
    assert!(report
        .parity_blocker
        .contains("--limit must be greater than zero"));
}

#[test]
fn release_issue_hygiene_offline_snapshot_filters_and_reports_gaps() {
    let dir = tempfile::tempdir().expect("tempdir");
    let snapshot = dir.path().join("issues.json");
    fs::write(
        &snapshot,
        r#"
[
  {
    "number": 101,
    "title": "watched gap",
    "url": "https://example.test/101",
    "labels": [{"name": "P1"}],
    "assignees": [],
    "body": "",
    "comments": []
  },
  {
    "number": 102,
    "title": "unwatched gap",
    "url": "https://example.test/102",
    "labels": [{"name": "P2"}],
    "assignees": [],
    "body": "",
    "comments": []
  },
  {
    "number": 103,
    "title": "owner label and comment decision",
    "url": "https://example.test/103",
    "labels": [{"name": "urgent"}, {"name": "W7"}],
    "assignees": [],
    "body": "",
    "comments": [{"body": "Release decision: defer until the next train."}]
  },
  {
    "number": 104,
    "title": "assignee and body decision",
    "url": "https://example.test/104",
    "labels": [{"name": "blocked"}],
    "assignees": [{"login": "ayates"}],
    "body": "Release decision: ship with notes.",
    "comments": []
  }
]
"#,
    )
    .expect("write snapshot");

    let report = ReleaseIssueHygieneReport::from_args(&ReleaseIssueHygieneArgs {
        json: true,
        fetch: false,
        input: Some(snapshot),
        limit: 500,
    });

    assert!(!report.ready);
    assert_eq!(report.status, "not_ready");
    assert_eq!(report.input_source.mode, "offline_snapshot");
    assert_eq!(report.summary.scanned, 4);
    assert_eq!(report.summary.release_impacting, 3);
    assert_eq!(report.summary.non_ready, 1);
    assert_eq!(report.summary.counts.get("P1"), Some(&1));
    assert_eq!(report.summary.counts.get("urgent"), Some(&1));
    assert_eq!(report.summary.counts.get("blocked"), Some(&1));
    assert!(report.missing_fields.is_empty());
    assert_eq!(report.non_ready_issues.len(), 1);
    let issue = &report.non_ready_issues[0];
    assert_eq!(issue.number, 101);
    assert_eq!(
        issue.missing_fields,
        vec!["owner".to_string(), "release_decision".to_string()]
    );
    assert!(issue
        .suggested_actions
        .contains(&RELEASE_ISSUE_OWNER_ACTION.to_string()));
    assert!(issue
        .suggested_actions
        .contains(&RELEASE_DECISION_ACTION.to_string()));
}

#[test]
fn release_issue_hygiene_offline_snapshot_accepts_python_input_shapes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let snapshot = dir.path().join("issues.json");
    fs::write(
        &snapshot,
        r#"
{
  "items": [
    {
      "number": "401",
      "title": "comment-only release decision",
      "url": "https://example.test/401",
      "labels": {"nodes": [{"name": "urgent"}]},
      "assignees": {"nodes": []},
      "body": "",
      "comments": {"nodes": [{"body": "**Release decision:** ship after owner pickup."}]}
    },
    {
      "number": 402,
      "title": "owner evidence but missing decision",
      "url": "https://example.test/402",
      "labels": {"nodes": [{"name": "blocked"}, {"name": "M2"}]},
      "assignees": {"nodes": [{"login": "release-captain"}]},
      "body": "",
      "comments": {"nodes": []}
    },
    {
      "number": 403,
      "title": "unwatched missing everything",
      "url": "https://example.test/403",
      "labels": {"nodes": [{"name": "P3"}]},
      "assignees": {"nodes": []},
      "body": "",
      "comments": {"nodes": []}
    }
  ]
}
"#,
    )
    .expect("write snapshot");

    let report = ReleaseIssueHygieneReport::from_args(&ReleaseIssueHygieneArgs {
        json: true,
        fetch: false,
        input: Some(snapshot),
        limit: 500,
    });

    assert!(!report.ready);
    assert_eq!(report.status, "not_ready");
    assert_eq!(report.summary.scanned, 3);
    assert_eq!(report.summary.release_impacting, 2);
    assert_eq!(report.summary.non_ready, 2);
    assert_eq!(report.summary.counts.get("urgent"), Some(&1));
    assert_eq!(report.summary.counts.get("blocked"), Some(&1));
    assert!(report.missing_fields.is_empty());
    assert_eq!(report.non_ready_issues.len(), 2);

    let comment_decision = &report.non_ready_issues[0];
    assert_eq!(comment_decision.number, 401);
    assert_eq!(comment_decision.missing_fields, vec!["owner".to_string()]);
    assert_eq!(
        comment_decision.release_decision_evidence,
        vec!["comment:1".to_string()]
    );

    let owner_only = &report.non_ready_issues[1];
    assert_eq!(owner_only.number, 402);
    assert_eq!(
        owner_only.missing_fields,
        vec!["release_decision".to_string()]
    );
    assert_eq!(
        owner_only.owner_evidence,
        vec![
            "assignee:release-captain".to_string(),
            "label:M2".to_string()
        ]
    );
}
