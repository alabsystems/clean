// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Board row 9: `model.lean.families`, the specified column.
//!
//! Reads the rule inventory and its falling ratchet
//! (`data/cic_l_rule_ratchet.json`). The ratchet must name exactly the rule
//! families the inventory does not mark `specified`, status for status, and
//! against the baseline committed at HEAD it may only shrink: a family may
//! leave it or move from `unspecified` to `partial`, never join it or regress.
//! The modelled, checked, compiled and aligned columns are absent until EV5
//! mints them.

use super::git_record::committed_bytes;
use super::historical::rule_family_ids;
use super::read_json;
use super::reading::{FreshnessReading, Outcome, Reading, NO_INPUT_DIGEST};
use super::rule_families::RULE_INVENTORY;
use crate::EvidenceCheckError;
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::json;
use std::collections::BTreeMap;
use std::path::Path;

pub(super) const RULE_RATCHET: &str = "data/cic_l_rule_ratchet.json";
pub(super) const LEAN_FAMILIES_FIGURE: &str = "model.lean.families";

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "snake_case")]
pub(super) enum Status {
    Partial,
    Unspecified,
}

#[derive(Deserialize)]
struct Inventory {
    rows: Vec<InventoryRow>,
}

#[derive(Deserialize)]
struct InventoryRow {
    id: String,
    kind: String,
    status: Option<String>,
}

#[derive(Deserialize)]
pub(super) struct Ratchet {
    #[serde(deserialize_with = "read_statuses")]
    pub(super) not_specified: BTreeMap<String, Status>,
}

fn read_statuses<'de, D: Deserializer<'de>>(
    input: D,
) -> Result<BTreeMap<String, Status>, D::Error> {
    super::read_unique_map(input, "rule family")
}

/// The inventory's rule families that are not specified, with their status.
fn not_specified(inventory: &Inventory) -> Result<BTreeMap<String, Status>, EvidenceCheckError> {
    let mut families = BTreeMap::new();
    for row in inventory.rows.iter().filter(|row| row.kind == "rule") {
        let status = match row.status.as_deref() {
            Some("specified") => continue,
            Some("partial") => Status::Partial,
            Some("unspecified") => Status::Unspecified,
            other => {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{RULE_INVENTORY} rule {:?} has status {other:?}",
                    row.id
                )))
            }
        };
        families.insert(row.id.clone(), status);
    }
    Ok(families)
}

/// Refuse a ratchet that grew or regressed against its committed baseline.
fn check_direction(
    current: &BTreeMap<String, Status>,
    baseline: &BTreeMap<String, Status>,
) -> Result<(), EvidenceCheckError> {
    let grown: Vec<String> = current
        .iter()
        .filter_map(|(family, status)| match baseline.get(family) {
            None => Some(format!("{family} joined as {status:?}")),
            Some(before) if status > before => {
                Some(format!("{family} regressed from {before:?} to {status:?}"))
            }
            Some(_) => None,
        })
        .collect();
    if grown.is_empty() {
        Ok(())
    } else {
        Err(EvidenceCheckError::Invalid(format!(
            "{RULE_RATCHET} may only fall against its committed baseline: {}",
            grown.join("; ")
        )))
    }
}

pub(super) fn read(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let inventory: Inventory = read_json(root, RULE_INVENTORY)?;
    let derived = not_specified(&inventory)?;
    let ratchet: Ratchet = read_json(root, RULE_RATCHET)?;
    if ratchet.not_specified != derived {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RULE_RATCHET} not_specified differs from {RULE_INVENTORY}\nrecorded {:?}\nderived  {derived:?}",
            ratchet.not_specified
        )));
    }
    let direction = match committed_bytes(root, RULE_RATCHET) {
        Some(bytes) => {
            let baseline: Ratchet = serde_json::from_slice(&bytes).map_err(|error| {
                EvidenceCheckError::Invalid(format!("HEAD:{RULE_RATCHET}: {error}"))
            })?;
            check_direction(&ratchet.not_specified, &baseline.not_specified)?;
            "the ratchet did not grow against HEAD"
        }
        None => "no committed baseline here; the direction was not compared",
    };
    let denominator = rule_family_ids(root)?;
    let not_specified_count = derived.len() as u64;
    let specified = denominator
        .count
        .checked_sub(not_specified_count)
        .ok_or_else(|| {
            EvidenceCheckError::Invalid(format!(
                "{RULE_INVENTORY} has more unspecified families than families"
            ))
        })?;
    let mut reading = Reading::new(
        json!({
            "specified": specified,
            "modelled": null,
            "checked": null,
            "compiled": null,
            "aligned": null,
            "not_specified": derived,
        }),
        format!(
            "{specified} of {} rule families specified; modelled, checked, compiled and aligned absent",
            denominator.count
        ),
        FreshnessReading::unknown(NO_INPUT_DIGEST),
    );
    reading.denominator = Some(denominator);
    reading.labels = vec![
        "specified: statuses as written in the inventory".to_owned(),
        direction.to_owned(),
    ];
    reading.non_claims = vec![
        "modelled, checked, compiled and aligned columns are absent until EV5 mints them"
            .to_owned(),
        "the statuses are not re-derived from Lean or C++ source by this reader".to_owned(),
    ];
    Ok(Outcome::Measured(Box::new(reading)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn map(entries: &[(&str, Status)]) -> BTreeMap<String, Status> {
        entries
            .iter()
            .map(|(family, status)| ((*family).to_owned(), *status))
            .collect()
    }

    #[test]
    fn test_lean_families_direction_shrinking_is_accepted() {
        let baseline = map(&[("a", Status::Unspecified), ("b", Status::Partial)]);
        let current = map(&[("a", Status::Partial)]);
        check_direction(&current, &baseline).unwrap();
    }

    #[test]
    fn test_lean_families_direction_growth_or_regression_is_refused() {
        let baseline = map(&[("a", Status::Partial)]);
        for current in [
            map(&[("a", Status::Unspecified)]),
            map(&[("a", Status::Partial), ("b", Status::Partial)]),
        ] {
            let error = check_direction(&current, &baseline).unwrap_err();
            assert!(error.to_string().contains("may only fall"));
        }
    }

    #[test]
    fn test_lean_families_ratchet_must_match_inventory() {
        let root = tempfile::tempdir().unwrap();
        let write = |path: &str, value: serde_json::Value| {
            let path = root.path().join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, serde_json::to_vec(&value).unwrap()).unwrap();
        };
        write(
            RULE_INVENTORY,
            json!({"rows": [
                {"id": "a", "kind": "rule", "status": "specified"},
                {"id": "b", "kind": "rule", "status": "partial"},
                {"id": "s", "kind": "strategy"}
            ]}),
        );
        write(RULE_RATCHET, json!({"not_specified": {"b": "partial"}}));
        let Outcome::Measured(reading) = read(root.path()).unwrap() else {
            panic!("expected a reading");
        };
        assert_eq!(reading.value["specified"], 1);
        assert_eq!(reading.denominator.as_ref().unwrap().count, 2);
        write(RULE_RATCHET, json!({"not_specified": {"b": "unspecified"}}));
        let error = read(root.path()).err().unwrap();
        assert!(error.to_string().contains("not_specified differs"));
    }
}
