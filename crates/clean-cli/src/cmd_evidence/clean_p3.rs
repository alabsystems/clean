// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reader for the historical Clean P3 mutant report.

use super::provenance::{RecordedLeg, ReportProvenance};
use super::{read_json, Measurement, MeasurementProvenance, Scoreboard, CLEAN_PINS, SCOREBOARD};
use crate::EvidenceCheckError;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::path::Path;

#[derive(Deserialize)]
enum CleanPinsSchema {
    #[serde(rename = "clean.patched_kernel_control.v1")]
    V1,
}

#[derive(Deserialize)]
enum CleanMutationId {
    #[serde(rename = "check-type-nat-zero-false")]
    CheckTypeNatZeroFalse,
}

#[derive(Deserialize)]
struct CleanMutation {
    #[serde(rename = "id")]
    _id: CleanMutationId,
}

#[derive(Deserialize)]
struct CleanPins {
    #[serde(rename = "schema")]
    _schema: CleanPinsSchema,
    #[serde(rename = "mutation")]
    _mutation: CleanMutation,
    measured_commit: String,
    sites: Vec<CleanSite>,
    summary: CleanSummary,
}

#[derive(Deserialize)]
struct CleanProvenance {
    #[serde(rename = "schema")]
    _schema: CleanPinsSchema,
    #[serde(rename = "mutation")]
    _mutation: CleanMutation,
    measured_commit: String,
    generated_at: Option<String>,
    minted_by: Option<String>,
    toolchain: Option<String>,
    lean_toolchain: Option<String>,
    #[serde(default)]
    legs: Vec<RecordedLeg>,
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let report: CleanProvenance = read_json(root, CLEAN_PINS)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Report generated", report.generated_at),
            ("Measured Clean commit", Some(report.measured_commit)),
            ("Recorded producer command", report.minted_by),
            ("Recorded Rust toolchain", report.toolchain),
            ("Recorded Lean toolchain", report.lean_toolchain),
        ],
        legs: Some(report.legs),
    })
}

#[derive(Deserialize)]
struct CleanSite {
    package: String,
    site: String,
    mutant: CleanOutcome,
}

#[derive(Deserialize)]
struct CleanOutcome {
    verdict: CleanVerdict,
}

#[derive(Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum CleanVerdict {
    Minted,
    Refused,
}

#[derive(Deserialize)]
struct CleanSummary {
    sites: usize,
    minted_under_mutant: usize,
}

#[derive(Deserialize)]
struct CleanHeadline {
    planted_false_mints_clean: CleanFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct CleanFigure {
    pub(super) sites: usize,
    pub(super) minted_under_mutant: usize,
    measured_commit: String,
    source: String,
}

fn clean_figure(report: &CleanPins) -> Result<CleanFigure, EvidenceCheckError> {
    if report.measured_commit.trim().is_empty() || report.sites.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{CLEAN_PINS} requires a measured commit and at least one site"
        )));
    }
    let mut sites = HashSet::new();
    let mut minted_under_mutant = 0;
    for row in &report.sites {
        let identity = (row.package.as_str(), row.site.as_str());
        if row.package.trim().is_empty() || row.site.trim().is_empty() || !sites.insert(identity) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{CLEAN_PINS} has a blank or duplicate package and site {identity:?}"
            )));
        }
        if row.mutant.verdict == CleanVerdict::Minted {
            minted_under_mutant += 1;
        }
    }
    if report.summary.sites != sites.len()
        || report.summary.minted_under_mutant != minted_under_mutant
    {
        return Err(EvidenceCheckError::Invalid(format!(
            "{CLEAN_PINS} summary records {} of {} sites but the rows yield {minted_under_mutant} of {}",
            report.summary.minted_under_mutant,
            report.summary.sites,
            sites.len()
        )));
    }
    Ok(CleanFigure {
        sites: sites.len(),
        minted_under_mutant,
        measured_commit: report.measured_commit.clone(),
        source: CLEAN_PINS.to_owned(),
    })
}

pub(super) fn derive(root: &Path) -> Result<CleanFigure, EvidenceCheckError> {
    clean_figure(&read_json(root, CLEAN_PINS)?)
}

pub(super) fn measure(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let derived = derive(root)?;
    let scoreboard: Scoreboard<CleanHeadline> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.headline.planted_false_mints_clean;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} headline.planted_false_mints_clean differs from {CLEAN_PINS}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::PlantedFalse {
        sites: derived.sites,
        minted_under_mutant: derived.minted_under_mutant,
        source: derived.source,
        provenance: MeasurementProvenance::Clean {
            measured_commit: derived.measured_commit,
        },
    })
}
