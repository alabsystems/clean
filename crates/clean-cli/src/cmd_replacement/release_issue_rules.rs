// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Release issue hygiene evaluation rules.

use super::*;

pub(crate) fn release_issue_nodes<'a>(
    value: Option<&'a serde_json::Value>,
    issue_ref: &str,
    field: &str,
    missing_fields: &mut Vec<String>,
) -> Option<&'a [serde_json::Value]> {
    match value {
        Some(value) if value.is_array() => value.as_array().map(Vec::as_slice),
        Some(value) if value.is_object() => match value.get("nodes") {
            Some(nodes) => nodes.as_array().map(Vec::as_slice).or_else(|| {
                missing_fields.push(format!("{issue_ref}.{field}.nodes: expected an array"));
                None
            }),
            None => {
                missing_fields.push(format!("{issue_ref}.{field}.nodes: missing required field"));
                None
            }
        },
        Some(_) => {
            missing_fields.push(format!(
                "{issue_ref}.{field}: expected an array or nodes object"
            ));
            None
        }
        None => None,
    }
}

pub(crate) fn push_trimmed(values: &mut Vec<String>, value: &str) {
    let trimmed = value.trim();
    if !trimmed.is_empty() {
        values.push(trimmed.to_string());
    }
}

pub(crate) fn evaluate_release_issue_entries(
    issues: Vec<ReleaseIssueSnapshotEntry>,
    missing_fields: Vec<String>,
) -> ReleaseIssueSnapshot {
    let mut counts = BTreeMap::new();
    for label in RELEASE_ISSUE_WATCHED_LABELS {
        counts.insert((*label).to_string(), 0);
    }

    let mut release_impacting = 0;
    let mut non_ready_issues = Vec::new();
    let mut suggested_actions = Vec::new();

    for issue in issues.iter().filter(|issue| issue.number.is_some()) {
        let watched_labels = watched_labels_for(issue);
        for label in &watched_labels {
            *counts.entry(label.clone()).or_insert(0) += 1;
        }
        if watched_labels.is_empty() {
            continue;
        }

        release_impacting += 1;
        let owner_evidence = owner_evidence_for(issue);
        let release_decision_evidence = release_decision_evidence_for(issue);
        let mut issue_missing_fields = Vec::new();
        let mut issue_suggested_actions = Vec::new();

        if owner_evidence.is_empty() {
            issue_missing_fields.push("owner".to_string());
            issue_suggested_actions.push(RELEASE_ISSUE_OWNER_ACTION.to_string());
        }
        if release_decision_evidence.is_empty() {
            issue_missing_fields.push("release_decision".to_string());
            issue_suggested_actions.push(RELEASE_DECISION_ACTION.to_string());
        }

        if !issue_missing_fields.is_empty() {
            let number = issue.number.unwrap_or_default();
            for action in &issue_suggested_actions {
                push_unique(&mut suggested_actions, format!("#{number}: {action}"));
            }
            non_ready_issues.push(ReleaseIssueHygieneIssue {
                number,
                title: issue.title.clone(),
                url: issue.url.clone(),
                labels: issue.labels.clone(),
                has_owner: !owner_evidence.is_empty(),
                has_release_decision: !release_decision_evidence.is_empty(),
                missing_fields: issue_missing_fields,
                suggested_actions: issue_suggested_actions,
                owner_evidence,
                release_decision_evidence,
            });
        }
    }

    if !missing_fields.is_empty() {
        push_unique(
            &mut suggested_actions,
            "Regenerate the snapshot with `gh issue list --state open --limit 500 --json number,title,url,labels,assignees,body,comments`.".to_string(),
        );
        push_unique(
            &mut suggested_actions,
            "Keep `comments` in the snapshot so comment-only `Release decision:` notes are visible.".to_string(),
        );
    }

    ReleaseIssueSnapshot {
        summary: ReleaseIssueHygieneSummary {
            scanned: issues.len(),
            release_impacting,
            non_ready: non_ready_issues.len(),
            counts,
        },
        non_ready_issues,
        missing_fields,
        suggested_actions,
    }
}

pub(crate) fn watched_labels_for(issue: &ReleaseIssueSnapshotEntry) -> Vec<String> {
    RELEASE_ISSUE_WATCHED_LABELS
        .iter()
        .filter(|watched| issue.labels.iter().any(|label| label == **watched))
        .map(|label| (*label).to_string())
        .collect()
}

pub(crate) fn owner_evidence_for(issue: &ReleaseIssueSnapshotEntry) -> Vec<String> {
    let mut evidence: Vec<String> = issue
        .assignees
        .iter()
        .map(|assignee| format!("assignee:{assignee}"))
        .collect();
    evidence.extend(
        issue
            .labels
            .iter()
            .filter(|label| is_ownership_label(label))
            .map(|label| format!("label:{label}")),
    );
    evidence
}

pub(crate) fn release_decision_evidence_for(issue: &ReleaseIssueSnapshotEntry) -> Vec<String> {
    let mut evidence = Vec::new();
    if contains_release_decision(&issue.body) {
        evidence.push("body".to_string());
    }
    for (index, comment) in issue.comments.iter().enumerate() {
        if contains_release_decision(comment) {
            evidence.push(format!("comment:{}", index + 1));
        }
    }
    evidence
}

pub(crate) fn is_ownership_label(label: &str) -> bool {
    let lower = label.to_ascii_lowercase();
    if let Some(rest) = lower.strip_prefix("prov") {
        return !rest.is_empty() && rest.chars().all(|ch| ch.is_ascii_digit());
    }

    let mut chars = lower.chars();
    let Some(prefix) = chars.next() else {
        return false;
    };
    let rest = chars.as_str();
    matches!(prefix, 'w' | 'r' | 'm')
        && !rest.is_empty()
        && rest.chars().all(|ch| ch.is_ascii_digit())
}

pub(crate) fn contains_release_decision(text: &str) -> bool {
    let lower = text.to_ascii_lowercase();
    let needle = "release decision";
    let mut search_start = 0;

    while let Some(relative) = lower[search_start..].find(needle) {
        let start = search_start + relative;
        let end = start + needle.len();
        let before_ok = lower[..start]
            .chars()
            .next_back()
            .is_none_or(|ch| !is_word_char(ch));
        let after_ok = lower[end..]
            .chars()
            .next()
            .is_none_or(|ch| !is_word_char(ch));
        if before_ok && after_ok {
            let tail = &lower[end..];
            let tail = tail.trim_start_matches(|ch: char| {
                ch.is_whitespace() || ch == '*' || ch == '_' || ch == '`'
            });
            if tail.starts_with(':') {
                return true;
            }
        }
        search_start = end;
    }

    false
}

pub(crate) fn is_word_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

pub(crate) fn push_unique(values: &mut Vec<String>, value: String) {
    if !values.contains(&value) {
        values.push(value);
    }
}
