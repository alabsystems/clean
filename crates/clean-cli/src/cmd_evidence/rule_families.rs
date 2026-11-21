// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Offline projection of the recorded S7 rule-family statuses into W0.

use super::{read_json, Measurement, ReportProvenance, RouteScoreboard, SCOREBOARD};
use crate::EvidenceCheckError;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fmt;
use std::path::Path;

pub(super) const RULE_INVENTORY: &str = "data/cic_l_rule_inventory.json";
pub(super) const RULE_FAMILIES_FIGURE: &str = "selfproof.lean_kernel_rule_families";

#[derive(Deserialize)]
struct RuleInventory {
    rows: Vec<InventoryRow>,
}

#[derive(Deserialize)]
struct InventoryRow {
    id: String,
    kind: RowKind,
    status: Option<RuleStatus>,
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum RowKind {
    Rule,
    Strategy,
    Infrastructure,
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum RuleStatus {
    Specified,
    Partial,
    Unspecified,
}

#[derive(Deserialize)]
struct RuleRoute {
    lean_kernel_rule_families: RuleFamilyFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct RuleFamilyFigure {
    pub(super) families: usize,
    pub(super) specified: usize,
    pub(super) partial: usize,
    pub(super) unspecified: usize,
    source: String,
}

impl fmt::Display for RuleFamilyFigure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} recorded rule families ({} specified, {} partial, {} unspecified)",
            self.families, self.specified, self.partial, self.unspecified
        )
    }
}

fn project(inventory: &RuleInventory) -> Result<RuleFamilyFigure, EvidenceCheckError> {
    let mut identities = HashSet::new();
    let (mut specified, mut partial, mut unspecified) = (0, 0, 0);
    for row in &inventory.rows {
        if row.id.trim().is_empty() || !identities.insert(&row.id) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{RULE_INVENTORY} has a blank or duplicate row ID {:?}",
                row.id
            )));
        }
        match (&row.kind, &row.status) {
            (RowKind::Rule, Some(RuleStatus::Specified)) => specified += 1,
            (RowKind::Rule, Some(RuleStatus::Partial)) => partial += 1,
            (RowKind::Rule, Some(RuleStatus::Unspecified)) => unspecified += 1,
            (RowKind::Rule, None) => {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{RULE_INVENTORY} rule {:?} requires a status",
                    row.id
                )));
            }
            (_, Some(_)) => {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{RULE_INVENTORY} non-rule row {:?} carries a rule status",
                    row.id
                )));
            }
            (_, None) => {}
        }
    }
    Ok(RuleFamilyFigure {
        families: specified + partial + unspecified,
        specified,
        partial,
        unspecified,
        source: RULE_INVENTORY.to_owned(),
    })
}

pub(super) fn derive(root: &Path) -> Result<RuleFamilyFigure, EvidenceCheckError> {
    project(&read_json(root, RULE_INVENTORY)?)
}

pub(super) fn measure(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let derived = derive(root)?;
    let scoreboard: RouteScoreboard<RuleRoute> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.route.lean_kernel_rule_families;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} route.lean_kernel_rule_families differs from {RULE_INVENTORY}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::RuleFamilies(derived))
}

#[derive(Deserialize)]
struct InventoryProvenance {
    #[serde(default)]
    upstream: UpstreamRecording,
    #[serde(default)]
    spec: SpecificationRecording,
}

#[derive(Default, Deserialize)]
struct UpstreamRecording {
    repository: Option<String>,
    tag: Option<String>,
    commit: Option<String>,
    root: Option<String>,
}

#[derive(Default, Deserialize)]
struct SpecificationRecording {
    root: Option<String>,
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let report: InventoryProvenance = read_json(root, RULE_INVENTORY)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Upstream repository", report.upstream.repository),
            ("Recorded Lean tag", report.upstream.tag),
            ("Recorded Lean commit", report.upstream.commit),
            ("Pinned source root", report.upstream.root),
            ("Specification root", report.spec.root),
            (
                "Inventory validator",
                Some("scripts/check_cic_l_rule_inventory.py".to_owned()),
            ),
        ],
        legs: None,
    })
}
