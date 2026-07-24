// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Release issue hygiene report and snapshot parsing.

use super::*;

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReleaseIssueHygieneReport {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) ready: bool,
    pub(crate) status: &'static str,
    pub(crate) input_source: ReleaseIssueHygieneInputSource,
    pub(crate) required_issue_fields: Vec<&'static str>,
    pub(crate) watched_labels: Vec<&'static str>,
    pub(crate) owner_evidence_rules: Vec<&'static str>,
    pub(crate) release_decision_evidence: &'static str,
    pub(crate) summary: ReleaseIssueHygieneSummary,
    pub(crate) non_ready_issues: Vec<ReleaseIssueHygieneIssue>,
    pub(crate) missing_fields: Vec<String>,
    pub(crate) suggested_actions: Vec<String>,
    pub(crate) parity_blocker: String,
}

impl ReleaseIssueHygieneReport {
    pub(crate) fn from_args(args: &ReleaseIssueHygieneArgs) -> Self {
        let mut report = Self::empty(args);
        if args.limit == 0 {
            report.missing_fields.push("limit".to_string());
            report
                .suggested_actions
                .push("Pass a positive --limit value for live issue fetches.".to_string());
            report.parity_blocker = "--limit must be greater than zero.".to_string();
            return report;
        }

        if args.fetch {
            report.evaluate_live_fetch(args.limit);
            return report;
        }

        let Some(input) = args.input.as_deref() else {
            report.missing_fields.push("input snapshot".to_string());
            report.suggested_actions.push(
                "Pass `--input <snapshot>` with local gh issue JSON including number,title,url,labels,assignees,body,comments.".to_string(),
            );
            report.suggested_actions.push(
                "Use `--fetch` for a read-only live `gh issue list` check, or pass `--input <snapshot>` for reproducible offline review.".to_string(),
            );
            report.parity_blocker =
                "no offline snapshot was provided and --fetch was not requested.".to_string();
            return report;
        };

        report.evaluate_offline_snapshot(input);
        report
    }

    pub(crate) fn evaluate_live_fetch(&mut self, limit: usize) {
        match fetch_release_issue_snapshot(limit) {
            Ok(snapshot) => {
                self.apply_snapshot(snapshot);
                self.parity_blocker = if self.ready {
                    "live read-only `gh issue list` fetch passed in Rust.".to_string()
                } else {
                    "live read-only `gh issue list` fetch is not ready; fix watched issue hygiene gaps.".to_string()
                };
            }
            Err(message) => {
                self.missing_fields
                    .push(format!("live gh issue list fetch: {message}"));
                self.suggested_actions.push(
                    "Install/authenticate GitHub CLI `gh`, run from the target repository, and retry `clean replacement release-issue-hygiene --fetch`.".to_string(),
                );
                self.suggested_actions.push(
                    format!("For offline review, capture `gh issue list --state open --limit {limit} --json {RELEASE_ISSUE_GH_JSON_FIELDS}` and pass `--input <snapshot>`."),
                );
                self.parity_blocker =
                    "live read-only `gh issue list` fetch failed closed before hygiene evaluation."
                        .to_string();
            }
        }
    }

    pub(crate) fn empty(args: &ReleaseIssueHygieneArgs) -> Self {
        Self {
            schema_version: RELEASE_ISSUE_HYGIENE_SCHEMA_VERSION,
            generated_by: "clean replacement release-issue-hygiene",
            ready: false,
            status: "not_ready",
            input_source: ReleaseIssueHygieneInputSource::from_args(args),
            required_issue_fields: RELEASE_ISSUE_REQUIRED_FIELDS.to_vec(),
            watched_labels: RELEASE_ISSUE_WATCHED_LABELS.to_vec(),
            owner_evidence_rules: vec![
                "assignees",
                "Wn labels",
                "Rn labels",
                "Mn labels",
                "provN labels",
            ],
            release_decision_evidence: "body or comment containing `Release decision:`",
            summary: ReleaseIssueHygieneSummary::default(),
            non_ready_issues: Vec::new(),
            missing_fields: Vec::new(),
            suggested_actions: Vec::new(),
            parity_blocker: "offline snapshot evaluation has not run".to_string(),
        }
    }

    pub(crate) fn evaluate_offline_snapshot(&mut self, path: &Path) {
        match load_release_issue_snapshot(path) {
            Ok(snapshot) => {
                self.apply_snapshot(snapshot);
                self.parity_blocker = if self.ready {
                    "offline --input snapshot passed in Rust.".to_string()
                } else {
                    "offline --input snapshot is not ready; fix malformed snapshot fields or watched issue hygiene gaps.".to_string()
                };
            }
            Err(message) => {
                self.missing_fields.push(message);
                self.suggested_actions.push(
                    "Regenerate the snapshot with `gh issue list --state open --limit 500 --json number,title,url,labels,assignees,body,comments`.".to_string(),
                );
                self.suggested_actions.push(
                    "Keep `comments` in the snapshot so comment-only `Release decision:` notes are visible.".to_string(),
                );
                self.parity_blocker =
                    "offline --input snapshot could not be parsed and is not release evidence."
                        .to_string();
            }
        }
    }

    pub(crate) fn apply_snapshot(&mut self, snapshot: ReleaseIssueSnapshot) {
        self.summary = snapshot.summary;
        self.non_ready_issues = snapshot.non_ready_issues;
        self.missing_fields = snapshot.missing_fields;
        self.suggested_actions = snapshot.suggested_actions;
        self.ready = self.missing_fields.is_empty() && self.non_ready_issues.is_empty();
        self.status = if self.ready { "ready" } else { "not_ready" };
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReleaseIssueHygieneInputSource {
    pub(crate) mode: &'static str,
    pub(crate) fetch_requested: bool,
    pub(crate) limit: usize,
    pub(crate) snapshot_path: Option<String>,
}

impl ReleaseIssueHygieneInputSource {
    pub(crate) fn from_args(args: &ReleaseIssueHygieneArgs) -> Self {
        let snapshot_path = args
            .input
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned());
        let mode = if args.fetch {
            "live_fetch"
        } else if snapshot_path.is_some() {
            "offline_snapshot"
        } else {
            "unspecified"
        };

        Self {
            mode,
            fetch_requested: args.fetch,
            limit: args.limit,
            snapshot_path,
        }
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub(crate) struct ReleaseIssueHygieneSummary {
    pub(crate) scanned: usize,
    pub(crate) release_impacting: usize,
    pub(crate) non_ready: usize,
    pub(crate) counts: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReleaseIssueHygieneIssue {
    pub(crate) number: u64,
    pub(crate) title: String,
    pub(crate) url: String,
    pub(crate) labels: Vec<String>,
    pub(crate) has_owner: bool,
    pub(crate) has_release_decision: bool,
    pub(crate) missing_fields: Vec<String>,
    pub(crate) suggested_actions: Vec<String>,
    pub(crate) owner_evidence: Vec<String>,
    pub(crate) release_decision_evidence: Vec<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ReleaseIssueSnapshot {
    pub(crate) summary: ReleaseIssueHygieneSummary,
    pub(crate) non_ready_issues: Vec<ReleaseIssueHygieneIssue>,
    pub(crate) missing_fields: Vec<String>,
    pub(crate) suggested_actions: Vec<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct ReleaseIssueSnapshotEntry {
    pub(crate) number: Option<u64>,
    pub(crate) title: String,
    pub(crate) url: String,
    pub(crate) labels: Vec<String>,
    pub(crate) assignees: Vec<String>,
    pub(crate) body: String,
    pub(crate) comments: Vec<String>,
}

pub(crate) fn load_release_issue_snapshot(path: &Path) -> Result<ReleaseIssueSnapshot, String> {
    let source = fs::read_to_string(path)
        .map_err(|err| format!("input: failed to read {}: {err}", path.display()))?;
    let payload = serde_json::from_str::<serde_json::Value>(&source)
        .map_err(|err| format!("input: failed to parse JSON: {err}"))?;
    parse_release_issue_snapshot(&payload)
}

pub(crate) fn fetch_release_issue_snapshot(limit: usize) -> Result<ReleaseIssueSnapshot, String> {
    let limit_string = limit.to_string();
    let output = Command::new("gh")
        .args([
            "issue",
            "list",
            "--state",
            "open",
            "--limit",
            &limit_string,
            "--json",
            RELEASE_ISSUE_GH_JSON_FIELDS,
        ])
        .output()
        .map_err(|err| format!("failed to execute `gh issue list`: {err}"))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
        let detail = if !stderr.is_empty() {
            stderr
        } else if !stdout.is_empty() {
            stdout
        } else {
            "`gh issue list` exited nonzero".to_string()
        };
        return Err(detail);
    }

    let payload = serde_json::from_slice::<serde_json::Value>(&output.stdout)
        .map_err(|err| format!("failed to parse `gh issue list` JSON: {err}"))?;
    parse_release_issue_snapshot(&payload)
}

pub(crate) fn parse_release_issue_snapshot(
    payload: &serde_json::Value,
) -> Result<ReleaseIssueSnapshot, String> {
    let items = extract_release_issue_items(payload)?;
    let mut missing_fields = Vec::new();
    let mut issues = Vec::new();

    for (index, item) in items.iter().enumerate() {
        let Some(issue) = item.as_object() else {
            missing_fields.push(format!(
                "issues[{index}]: JSON issue entry must be an object"
            ));
            continue;
        };
        issues.push(parse_release_issue_entry(index, issue, &mut missing_fields));
    }

    Ok(evaluate_release_issue_entries(issues, missing_fields))
}

pub(crate) fn extract_release_issue_items(
    payload: &serde_json::Value,
) -> Result<&[serde_json::Value], String> {
    if let Some(items) = payload.as_array() {
        return Ok(items.as_slice());
    }

    let Some(object) = payload.as_object() else {
        return Err(
            "input: JSON input must be a list or object with issues/items/nodes".to_string(),
        );
    };

    for key in ["issues", "items", "nodes"] {
        if let Some(value) = object.get(key) {
            return value
                .as_array()
                .map(Vec::as_slice)
                .ok_or_else(|| format!("input.{key}: expected an array of issue objects"));
        }
    }

    Err("input: JSON input object must contain issues, items, or nodes".to_string())
}

pub(crate) fn parse_release_issue_entry(
    index: usize,
    issue: &serde_json::Map<String, serde_json::Value>,
    missing_fields: &mut Vec<String>,
) -> ReleaseIssueSnapshotEntry {
    let issue_ref = release_issue_error_ref(index, issue);
    for field in RELEASE_ISSUE_REQUIRED_FIELDS {
        if !issue.contains_key(*field) {
            missing_fields.push(format!("{issue_ref}.{field}: missing required field"));
        }
    }

    ReleaseIssueSnapshotEntry {
        number: parse_issue_number(issue.get("number"), &issue_ref, missing_fields),
        title: parse_required_string(issue.get("title"), &issue_ref, "title", missing_fields),
        url: parse_required_string(issue.get("url"), &issue_ref, "url", missing_fields),
        labels: parse_label_names(issue.get("labels"), &issue_ref, missing_fields),
        assignees: parse_assignee_names(issue.get("assignees"), &issue_ref, missing_fields),
        body: parse_required_string(issue.get("body"), &issue_ref, "body", missing_fields),
        comments: parse_comment_bodies(issue.get("comments"), &issue_ref, missing_fields),
    }
}

pub(crate) fn release_issue_error_ref(
    index: usize,
    issue: &serde_json::Map<String, serde_json::Value>,
) -> String {
    match issue.get("number") {
        Some(value) if value.is_u64() => format!("#{}", value.as_u64().unwrap_or_default()),
        Some(value) if value.is_i64() => format!("#{}", value.as_i64().unwrap_or_default()),
        Some(value) if value.is_string() => {
            let number = value.as_str().unwrap_or_default().trim();
            if number.is_empty() {
                format!("issues[{index}]")
            } else {
                format!("#{number}")
            }
        }
        _ => format!("issues[{index}]"),
    }
}

pub(crate) fn parse_issue_number(
    value: Option<&serde_json::Value>,
    issue_ref: &str,
    missing_fields: &mut Vec<String>,
) -> Option<u64> {
    match value {
        Some(value) if value.is_u64() => value.as_u64(),
        Some(value) if value.is_string() => {
            let raw = value.as_str().unwrap_or_default().trim();
            raw.parse::<u64>().map(Some).unwrap_or_else(|_| {
                missing_fields.push(format!("{issue_ref}.number: expected a positive integer"));
                None
            })
        }
        Some(_) => {
            missing_fields.push(format!("{issue_ref}.number: expected a positive integer"));
            None
        }
        None => None,
    }
}

pub(crate) fn parse_required_string(
    value: Option<&serde_json::Value>,
    issue_ref: &str,
    field: &str,
    missing_fields: &mut Vec<String>,
) -> String {
    match value {
        Some(value) if value.is_string() => value.as_str().unwrap_or_default().trim().to_string(),
        Some(_) => {
            missing_fields.push(format!("{issue_ref}.{field}: expected a string"));
            String::new()
        }
        None => String::new(),
    }
}

pub(crate) fn parse_label_names(
    value: Option<&serde_json::Value>,
    issue_ref: &str,
    missing_fields: &mut Vec<String>,
) -> Vec<String> {
    let Some(items) = release_issue_nodes(value, issue_ref, "labels", missing_fields) else {
        return Vec::new();
    };

    let mut labels = Vec::new();
    for (index, label) in items.iter().enumerate() {
        if let Some(name) = label.as_str() {
            push_trimmed(&mut labels, name);
        } else if let Some(object) = label.as_object() {
            match object.get("name").and_then(serde_json::Value::as_str) {
                Some(name) => push_trimmed(&mut labels, name),
                None => missing_fields.push(format!(
                    "{issue_ref}.labels[{index}].name: expected a string"
                )),
            }
        } else {
            missing_fields.push(format!(
                "{issue_ref}.labels[{index}]: expected a string or object with name"
            ));
        }
    }
    labels
}

pub(crate) fn parse_assignee_names(
    value: Option<&serde_json::Value>,
    issue_ref: &str,
    missing_fields: &mut Vec<String>,
) -> Vec<String> {
    let Some(items) = release_issue_nodes(value, issue_ref, "assignees", missing_fields) else {
        return Vec::new();
    };

    let mut names = Vec::new();
    for (index, assignee) in items.iter().enumerate() {
        if let Some(name) = assignee.as_str() {
            push_trimmed(&mut names, name);
        } else if let Some(object) = assignee.as_object() {
            let name = object
                .get("login")
                .and_then(serde_json::Value::as_str)
                .or_else(|| object.get("name").and_then(serde_json::Value::as_str));
            match name {
                Some(name) => push_trimmed(&mut names, name),
                None => missing_fields.push(format!(
                    "{issue_ref}.assignees[{index}].login: expected login or name string"
                )),
            }
        } else {
            missing_fields.push(format!(
                "{issue_ref}.assignees[{index}]: expected a string or assignee object"
            ));
        }
    }
    names
}

pub(crate) fn parse_comment_bodies(
    value: Option<&serde_json::Value>,
    issue_ref: &str,
    missing_fields: &mut Vec<String>,
) -> Vec<String> {
    let Some(items) = release_issue_nodes(value, issue_ref, "comments", missing_fields) else {
        return Vec::new();
    };

    let mut bodies = Vec::new();
    for (index, comment) in items.iter().enumerate() {
        let Some(object) = comment.as_object() else {
            missing_fields.push(format!(
                "{issue_ref}.comments[{index}]: expected a comment object with body"
            ));
            continue;
        };
        match object.get("body").and_then(serde_json::Value::as_str) {
            Some(body) => bodies.push(body.to_string()),
            None => missing_fields.push(format!(
                "{issue_ref}.comments[{index}].body: expected a string"
            )),
        }
    }
    bodies
}
