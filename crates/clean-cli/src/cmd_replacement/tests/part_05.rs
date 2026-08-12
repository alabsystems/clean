// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 5) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use crate::cmd_replacement::*;

#[test]
fn release_issue_hygiene_offline_snapshot_can_be_ready() {
    let dir = tempfile::tempdir().expect("tempdir");
    let snapshot = dir.path().join("issues.json");
    fs::write(
        &snapshot,
        r#"
{
  "issues": [
    {
      "number": 201,
      "title": "ready issue",
      "url": "https://example.test/201",
      "labels": {"nodes": [{"name": "local-maximum"}, {"name": "prov3"}]},
      "assignees": {"nodes": []},
      "body": "",
      "comments": {"nodes": [{"body": "Release decision `_: ship with workaround."}]}
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

    assert!(report.ready);
    assert_eq!(report.status, "ready");
    assert_eq!(report.summary.scanned, 1);
    assert_eq!(report.summary.release_impacting, 1);
    assert!(report.non_ready_issues.is_empty());
    assert!(report.missing_fields.is_empty());
    assert!(report
        .parity_blocker
        .contains("offline --input snapshot passed in Rust"));
}

#[test]
fn release_issue_hygiene_offline_snapshot_fails_closed_on_missing_required_fields() {
    let dir = tempfile::tempdir().expect("tempdir");
    let snapshot = dir.path().join("issues.json");
    fs::write(
        &snapshot,
        r#"
[
  {
    "number": 301,
    "title": "missing comments field",
    "url": "https://example.test/301",
    "labels": [{"name": "P1"}],
    "assignees": [{"login": "owner"}],
    "body": "Release decision: ship."
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
    assert_eq!(report.summary.scanned, 1);
    assert!(report.non_ready_issues.is_empty());
    assert!(report
        .missing_fields
        .contains(&"#301.comments: missing required field".to_string()));
    assert!(report
        .suggested_actions
        .iter()
        .any(|action| action.contains("number,title,url,labels,assignees,body,comments")));
}
