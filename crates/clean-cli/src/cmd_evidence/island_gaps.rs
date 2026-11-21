// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Offline projection of the dated W2 island gap inventory into W0.

use super::{read_json, Measurement, ReportProvenance, RouteScoreboard, SCOREBOARD};
use crate::EvidenceCheckError;
use serde::{Deserialize, Serialize};
use std::path::Path;

pub(super) const ISLAND_GAPS: &str = "data/kcheck_island_gaps.json";
pub(super) const ISLAND_GAPS_FIGURE: &str = "selfproof.island_gaps";

#[derive(Deserialize)]
enum GapSchema {
    #[serde(rename = "clean.kcheck_island_gaps.v1")]
    V1,
}

#[derive(Deserialize)]
struct GapInventory {
    #[serde(rename = "schema")]
    _schema: GapSchema,
    gaps: Vec<GapRow>,
}

#[derive(Deserialize)]
struct GapRow {
    status: GapStatus,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum GapStatus {
    Open,
    Closed,
    Pinned,
}

#[derive(Deserialize)]
struct IslandRoute {
    island_gaps: GapFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct GapFigure {
    pub(super) rows: usize,
    pub(super) open: usize,
    source: String,
}

pub(super) fn derive(root: &Path) -> Result<GapFigure, EvidenceCheckError> {
    let inventory: GapInventory = read_json(root, ISLAND_GAPS)?;
    Ok(GapFigure {
        rows: inventory.gaps.len(),
        open: inventory
            .gaps
            .iter()
            .filter(|gap| matches!(gap.status, GapStatus::Open))
            .count(),
        source: ISLAND_GAPS.to_owned(),
    })
}

pub(super) fn measure(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let derived = derive(root)?;
    let scoreboard: RouteScoreboard<IslandRoute> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.route.island_gaps;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} route.island_gaps differs from {ISLAND_GAPS}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::IslandGaps {
        rows: derived.rows,
        open: derived.open,
        source: derived.source,
    })
}

#[derive(Deserialize)]
struct GapProvenance {
    #[serde(rename = "schema")]
    _schema: GapSchema,
    measured_at: Option<String>,
    measured_with: Option<String>,
    subject: Option<String>,
    record: Option<String>,
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let report: GapProvenance = read_json(root, ISLAND_GAPS)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Measured at", report.measured_at),
            ("Measured with", report.measured_with),
            ("Subject", report.subject),
            ("Probe record", report.record),
        ],
        legs: None,
    })
}
