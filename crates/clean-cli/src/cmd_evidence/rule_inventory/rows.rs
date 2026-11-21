// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rule-row status shape and exact working-tree ratchet comparison.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::super::k3_inputs::find_regular_file;
use super::super::lean_families::{Ratchet, Status, RULE_RATCHET};
use super::super::read_json;
use super::super::rule_families::RULE_INVENTORY;
use crate::EvidenceCheckError;

#[derive(Deserialize)]
struct Inventory {
    rows: Vec<Row>,
}

#[derive(Deserialize)]
struct Row {
    id: String,
    kind: Option<String>,
    status: Option<String>,
    cic_l: Option<Vec<Value>>,
    missing: Option<String>,
    extension: Option<Value>,
}

#[derive(Default, Serialize)]
pub(super) struct Report {
    pub(super) families: usize,
    pub(super) specified: usize,
    pub(super) partial: usize,
    pub(super) unspecified: usize,
    pub(super) not_specified: BTreeMap<String, Status>,
    pub(super) findings: Vec<String>,
    pub(super) unreadable: Vec<String>,
}

pub(super) fn check(root: &Path, bytes: &[u8]) -> Result<Report, EvidenceCheckError> {
    let inventory: Inventory = serde_json::from_slice(bytes)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{RULE_INVENTORY}: {error}")))?;
    let mut report = Report::default();
    for row in &inventory.rows {
        if row.kind.as_deref() == Some("rule") {
            check_shape(row, &mut report);
        }
    }
    report.families = report.specified + report.partial + report.unspecified;

    match read_ratchet(root) {
        Ok(ratchet) => {
            let ids: BTreeSet<_> = inventory.rows.iter().map(|row| row.id.as_str()).collect();
            compare_ratchet(&ratchet.not_specified, &ids, &mut report);
        }
        Err(EvidenceCheckError::Unavailable(reason)) => report.unreadable.push(reason),
        Err(error) => report.findings.push(format!("(c) RATCHET: {error}")),
    }
    Ok(report)
}

fn read_ratchet(root: &Path) -> Result<Ratchet, EvidenceCheckError> {
    if find_regular_file(root, RULE_RATCHET)?.is_none() {
        return Err(EvidenceCheckError::Unavailable(format!(
            "{RULE_RATCHET} is not an available regular file"
        )));
    }
    read_json(root, RULE_RATCHET)
}

fn check_shape(row: &Row, report: &mut Report) {
    let id = &row.id;
    let incomplete = match row.status.as_deref() {
        Some("specified") => {
            report.specified += 1;
            None
        }
        Some("partial") => {
            report.partial += 1;
            Some(Status::Partial)
        }
        Some("unspecified") => {
            report.unspecified += 1;
            Some(Status::Unspecified)
        }
        invalid => {
            let repr = invalid.map_or_else(|| "None".to_owned(), |status| format!("'{status}'"));
            report.findings.push(format!(
                "SHAPE: {id} status={repr} is not one of ('specified', 'partial', 'unspecified')"
            ));
            return;
        }
    };
    if let Some(status) = incomplete {
        report.not_specified.insert(id.clone(), status);
    }
    let status = incomplete.map_or("specified", status_name);
    let has_items = row.cic_l.as_ref().is_some_and(|items| !items.is_empty());
    if incomplete == Some(Status::Unspecified) && has_items {
        report.findings.push(format!(
            "SHAPE: {id} is unspecified and names CIC_L items -- it is partial, or the items are `groundwork`"
        ));
    }
    if incomplete != Some(Status::Unspecified) && !has_items {
        report
            .findings
            .push(format!("SHAPE: {id} is {status} and names no CIC_L item"));
    }
    // Include the control separators recognized by Python's str.strip().
    let has_missing = row.missing.as_ref().is_some_and(|text| {
        text.chars()
            .any(|ch| !ch.is_whitespace() && !matches!(ch, '\u{1c}'..='\u{1f}'))
    });
    if (incomplete == Some(Status::Partial)) != has_missing {
        report.findings.push(format!(
            "SHAPE: {id} is {status}: `missing` names the unspecified part of a partial row and of no other"
        ));
    }
    if row.extension.as_ref().is_some_and(|extension| {
        !extension
            .get("plan_requires_derived_rule")
            .is_some_and(Value::is_boolean)
    }) {
        report.findings.push(format!(
            "SHAPE: {id} is a kernel extension and does not say whether the plan requires it as a derived rule"
        ));
    }
}

fn compare_ratchet(recorded: &BTreeMap<String, Status>, ids: &BTreeSet<&str>, report: &mut Report) {
    for (id, status) in recorded {
        if !report.not_specified.contains_key(id) {
            let detail = if ids.contains(id.as_str()) {
                "the inventory now calls it specified -- remove it from the ratchet in the same change (--update)"
            } else {
                "the inventory has no such rule family"
            };
            report.findings.push(format!(
                "(c) RATCHET: {id} is in {RULE_RATCHET} as {} and {detail}",
                status_name(*status)
            ));
        }
    }
    for (id, status) in &report.not_specified {
        if !recorded.contains_key(id) {
            report.findings.push(format!(
                "(c) RATCHET: {id} is {} and is not in {RULE_RATCHET} -- the ratchet only shrinks; a family that stopped being specified, or a new one, is added by hand with its reason",
                status_name(*status)
            ));
        }
    }
    for (id, status) in &report.not_specified {
        if let Some(pinned) = recorded.get(id).filter(|pinned| *pinned != status) {
            report.findings.push(format!(
                "(c) RATCHET: {id} is {} and {RULE_RATCHET} records {}",
                status_name(*status),
                status_name(*pinned)
            ));
        }
    }
}

fn status_name(status: Status) -> &'static str {
    match status {
        Status::Partial => "partial",
        Status::Unspecified => "unspecified",
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use serde_json::json;

    use super::{check, status_name, BTreeMap, Path, Report, Status, Value, RULE_RATCHET};

    fn report(root: &Path, rows: Vec<Value>) -> Report {
        let bytes = serde_json::to_vec(&json!({"rows": rows})).unwrap();
        check(root, &bytes).unwrap()
    }

    fn write_ratchet(root: &Path, bytes: &[u8]) {
        let path = root.join(RULE_RATCHET);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }

    #[test]
    fn accepts_exact_empty_and_seven_family_ratchets() {
        let root = tempfile::tempdir().unwrap();
        for statuses in [
            &[][..],
            &[
                Status::Partial,
                Status::Partial,
                Status::Partial,
                Status::Unspecified,
                Status::Unspecified,
                Status::Unspecified,
                Status::Unspecified,
            ][..],
        ] {
            let mut rows = vec![json!({
                "id": "specified", "kind": "rule", "status": "specified",
                "cic_l": [{}], "missing": null, "extension": null
            })];
            let mut pinned = BTreeMap::new();
            for (index, status) in statuses.iter().copied().enumerate() {
                let id = format!("family-{index}");
                let (items, missing) = match status {
                    Status::Partial => (json!([{}]), Some("remaining proof")),
                    Status::Unspecified => (json!([]), None),
                };
                rows.push(json!({
                    "id": id, "kind": "rule", "status": status_name(status),
                    "cic_l": items, "missing": missing,
                    "extension": {"plan_requires_derived_rule": index % 2 == 0}
                }));
                pinned.insert(id, status);
            }
            let ratchet = serde_json::to_vec(&json!({"not_specified": pinned})).unwrap();
            write_ratchet(root.path(), &ratchet);
            let report = report(root.path(), rows);
            assert_eq!(report.families, statuses.len() + 1);
            assert_eq!(report.not_specified, pinned);
            assert_eq!(report.specified, 1);
            assert!(report.findings.is_empty() && report.unreadable.is_empty());
        }
    }

    #[test]
    fn preserves_ratchet_categories_and_stops_shape_checks_at_invalid_status() {
        let root = tempfile::tempdir().unwrap();
        write_ratchet(
            root.path(),
            br#"{"not_specified":{"specified":"partial","gone":"unspecified","changed":"unspecified"}}"#,
        );
        let report = report(
            root.path(),
            vec![
                json!({"id": "invalid", "kind": "rule", "status": "unknown", "extension": {}}),
                json!({"id": "specified", "kind": "rule", "status": "specified", "cic_l": [{}]}),
                json!({
                    "id": "changed", "kind": "rule", "status": "partial", "cic_l": [{}],
                    "missing": "remaining proof"
                }),
                json!({"id": "unpinned", "kind": "rule", "status": "unspecified"}),
            ],
        );
        assert_eq!(report.families, 3);
        assert_eq!(report.findings, [
            "SHAPE: invalid status='unknown' is not one of ('specified', 'partial', 'unspecified')",
            "(c) RATCHET: gone is in data/cic_l_rule_ratchet.json as unspecified and the inventory has no such rule family",
            "(c) RATCHET: specified is in data/cic_l_rule_ratchet.json as partial and the inventory now calls it specified -- remove it from the ratchet in the same change (--update)",
            "(c) RATCHET: unpinned is unspecified and is not in data/cic_l_rule_ratchet.json -- the ratchet only shrinks; a family that stopped being specified, or a new one, is added by hand with its reason",
            "(c) RATCHET: changed is partial and data/cic_l_rule_ratchet.json records unspecified",
        ]);
    }

    #[test]
    fn retains_known_shape_problems_with_unavailable_or_invalid_ratchets() {
        let root = tempfile::tempdir().unwrap();
        let rows = vec![json!({
            "id": "partial", "kind": "rule", "status": "partial", "cic_l": [{}],
            "missing": "\t\u{1c}", "extension": {"plan_requires_derived_rule": 0}
        })];
        let missing = report(root.path(), rows.clone());
        assert_eq!(missing.unreadable.len(), 1);
        assert_eq!(missing.findings.len(), 2);

        write_ratchet(
            root.path(),
            br#"{"not_specified":{"partial":"partial","partial":"unspecified"}}"#,
        );
        let corrupt = report(root.path(), rows);
        assert!(corrupt.unreadable.is_empty());
        assert_eq!(corrupt.findings.len(), 3);
        assert_eq!(corrupt.findings[..2], missing.findings);
        assert!(corrupt.findings[2].contains("duplicate rule family"));
    }
}
