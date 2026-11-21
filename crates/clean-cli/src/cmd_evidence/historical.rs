// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Readings of the six historical W0 figures.
//!
//! Each reading first runs the figure's existing recount and W0 comparison
//! (`measure`), so a reading exists only for a consistent record. It then
//! reads the members that define the denominator from the same record and
//! the measurement metadata the record names.

use super::reading::{owned, DenominatorReading, FreshnessReading, Outcome, Reading};
use super::{
    checker_source, clean_p3, elaboration, island_gaps, read_json, rule_families, CLEAN_PINS,
    TRUST_PINS,
};
use super::{
    elaboration::ELABORATION_BASELINE, island_gaps::ISLAND_GAPS, measure_trust,
    reading::NO_INPUT_DIGEST, rule_families::RULE_INVENTORY,
};
use super::{Measurement, MeasurementProvenance};
use crate::EvidenceCheckError;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::Path;

pub(super) fn reading(
    measurement: &Measurement,
    denominator: Option<DenominatorReading>,
    labels: &[&str],
    non_claims: &[&str],
) -> Result<Reading, EvidenceCheckError> {
    let value = serde_json::to_value(measurement)
        .map_err(|error| EvidenceCheckError::Invalid(format!("cannot render value: {error}")))?;
    let mut reading = Reading::new(
        value,
        measurement.to_string(),
        FreshnessReading::unknown(NO_INPUT_DIGEST),
    );
    reading.denominator = denominator;
    reading.labels = owned(labels);
    reading.non_claims = owned(non_claims);
    if let Measurement::PlantedFalse { provenance, .. } = measurement {
        match provenance {
            MeasurementProvenance::Clean { measured_commit } => {
                reading.commit = Some(measured_commit.clone());
            }
            MeasurementProvenance::Trust {
                measured_at,
                trust_commit,
                clean_pin_in_trust,
            } => {
                reading.recorded_at = Some(measured_at.clone());
                reading.labels.push(format!(
                    "Trust {trust_commit}, Clean pin in Trust {clean_pin_in_trust}"
                ));
            }
        }
    }
    Ok(reading)
}

const PLANTED_NON_CLAIMS: &[&str] = &[
    "a historical mutant experiment, not a re-run",
    "the inside-fragment split of these sites is absent",
];

#[derive(Deserialize)]
struct CleanSites {
    generated_at: Option<String>,
    sites: Vec<CleanSiteId>,
}

#[derive(Deserialize)]
struct CleanSiteId {
    package: String,
    site: String,
}

pub(super) fn planted_false_clean(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = clean_p3::measure(root)?;
    let record: CleanSites = read_json(root, CLEAN_PINS)?;
    let denominator = DenominatorReading::counting(
        "Clean planted-False sites (package/site)",
        record
            .sites
            .iter()
            .map(|site| format!("{}/{}", site.package, site.site)),
    )?;
    let mut reading = reading(
        &measurement,
        Some(denominator),
        &["mutation check-type-nat-zero-false in clean-kernel"],
        PLANTED_NON_CLAIMS,
    )?;
    reading.recorded_at = record.generated_at;
    Ok(Outcome::Measured(Box::new(reading)))
}

#[derive(Deserialize)]
struct TrustSites {
    pins: BTreeMap<String, Vec<TrustSiteId>>,
}

#[derive(Deserialize)]
struct TrustSiteId {
    site: String,
}

pub(super) fn planted_false_trust(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = measure_trust(root)?;
    let record: TrustSites = read_json(root, TRUST_PINS)?;
    let denominator = DenominatorReading::counting(
        "Trust planted-False sites",
        record.pins.values().flatten().map(|pin| pin.site.clone()),
    )?;
    let reading = reading(
        &measurement,
        Some(denominator),
        &["measured in Trust at the recorded commit"],
        PLANTED_NON_CLAIMS,
    )?;
    Ok(Outcome::Measured(Box::new(reading)))
}

#[derive(Deserialize)]
struct GapIds {
    measured_at: Option<String>,
    gaps: Vec<GapId>,
}

#[derive(Deserialize)]
struct GapId {
    id: String,
}

pub(super) fn island_gaps(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = island_gaps::measure(root)?;
    let record: GapIds = read_json(root, ISLAND_GAPS)?;
    let denominator = DenominatorReading::counting(
        "recorded island gaps",
        record.gaps.into_iter().map(|gap| gap.id),
    )?;
    let mut reading = reading(
        &measurement,
        Some(denominator),
        &["gaps of the kcheck island build, as recorded"],
        &["the inventory is hand-maintained; no producer re-measures it"],
    )?;
    reading.recorded_at = record.measured_at;
    Ok(Outcome::Measured(Box::new(reading)))
}

#[derive(Deserialize)]
struct ElaborationRoster {
    commit: String,
    expected_modules: Vec<(String, String)>,
}

pub(super) fn theories_elaborated(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = elaboration::measure(root)?;
    let record: ElaborationRoster = read_json(root, ELABORATION_BASELINE)?;
    let denominator = DenominatorReading::counting(
        "theory modules of the recorded package roster (package/module)",
        record
            .expected_modules
            .iter()
            .map(|(package, module)| format!("{package}/{module}")),
    )?;
    let mut reading = reading(
        &measurement,
        Some(denominator),
        &["Clean's elaborator on the five self-proof packages"],
        &["the roster predates mounted packages; the current denominator is larger"],
    )?;
    reading.commit = Some(record.commit);
    Ok(Outcome::Measured(Box::new(reading)))
}

#[derive(Deserialize)]
struct RuleIds {
    rows: Vec<RuleId>,
}

#[derive(Deserialize)]
struct RuleId {
    id: String,
    kind: String,
}

pub(super) fn rule_family_ids(root: &Path) -> Result<DenominatorReading, EvidenceCheckError> {
    let record: RuleIds = read_json(root, RULE_INVENTORY)?;
    DenominatorReading::counting(
        "Lean kernel rule families of the inventory",
        record
            .rows
            .into_iter()
            .filter(|row| row.kind == "rule")
            .map(|row| row.id),
    )
}

pub(super) fn lean_kernel_rule_families(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = rule_families::measure(root)?;
    let reading = reading(
        &measurement,
        Some(rule_family_ids(root)?),
        &["statuses as written in the inventory"],
        &["the inventory's statuses are not re-derived from Lean source here"],
    )?;
    Ok(Outcome::Measured(Box::new(reading)))
}

pub(super) fn checker_soundness(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let measurement = checker_source::measure(root)?;
    let reading = reading(
        &measurement,
        None,
        &["theorem statements lexed from the current Lean source"],
        &["a statement in source is not a re-checked proof; quorum re-checking is separate"],
    )?;
    Ok(Outcome::Measured(Box::new(reading)))
}
