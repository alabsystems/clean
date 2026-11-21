// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Offline projection of the historical E4 elaboration baseline into W0.

use super::{read_json, Measurement, ReportProvenance, RouteScoreboard, SCOREBOARD};
use crate::EvidenceCheckError;
use serde::{Deserialize, Deserializer, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::path::Path;

pub(super) const ELABORATION_BASELINE: &str = "reports/self-proof-elab/baseline.json";
pub(super) const ELABORATION_FIGURE: &str = "selfproof.theories_elaborated";

#[derive(Deserialize)]
enum ElaborationSchema {
    #[serde(rename = "self-proof-elab-v2")]
    V2,
}

#[derive(Deserialize)]
struct ElaborationBaseline {
    #[serde(rename = "schema")]
    _schema: ElaborationSchema,
    commit: String,
    complete: bool,
    expected_modules: Vec<(String, String)>,
    modules: Vec<ModuleResult>,
}

#[derive(Deserialize)]
struct ModuleResult {
    package: String,
    module: String,
    status: ModuleStatus,
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum ModuleStatus {
    Elaborated,
    Refused,
    TimedOut,
}

#[derive(Debug, Default, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct PackageCounts {
    modules: usize,
    elaborated: usize,
}

#[derive(Deserialize)]
struct ElaborationRoute {
    clean_elaborates_theories: ElaborationFigure,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct ElaborationFigure {
    pub(super) modules: usize,
    pub(super) elaborated: usize,
    #[serde(deserialize_with = "read_package_counts")]
    by_package: BTreeMap<String, PackageCounts>,
    producer_commit: String,
    source: String,
}

fn read_package_counts<'de, D: Deserializer<'de>>(
    input: D,
) -> Result<BTreeMap<String, PackageCounts>, D::Error> {
    super::read_unique_map(input, "package count")
}

impl fmt::Display for ElaborationFigure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} of {} historical modules elaborated (producer commit {:?})",
            self.elaborated, self.modules, self.producer_commit
        )
    }
}

fn project(report: ElaborationBaseline) -> Result<ElaborationFigure, EvidenceCheckError> {
    if !report.complete || report.commit.trim().is_empty() || report.modules.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ELABORATION_BASELINE} requires a complete run, a producer commit and a nonempty module roster"
        )));
    }
    let actual = report.modules.iter().map(|row| (&row.package, &row.module));
    let expected = report
        .expected_modules
        .iter()
        .map(|(package, module)| (package, module));
    if !actual.eq(expected) {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ELABORATION_BASELINE} module rows differ from its declared roster"
        )));
    }
    let mut by_package = BTreeMap::<String, PackageCounts>::new();
    let mut identities = HashSet::new();
    let mut elaborated = 0;
    for row in &report.modules {
        if row.package.trim().is_empty()
            || row.module.trim().is_empty()
            || !identities.insert((&row.package, &row.module))
        {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ELABORATION_BASELINE} has a blank or duplicate package and module ({:?}, {:?})",
                row.package, row.module
            )));
        }
        let counts = by_package.entry(row.package.clone()).or_default();
        counts.modules += 1;
        if matches!(row.status, ModuleStatus::Elaborated) {
            counts.elaborated += 1;
            elaborated += 1;
        }
    }
    Ok(ElaborationFigure {
        modules: report.modules.len(),
        elaborated,
        by_package,
        producer_commit: report.commit,
        source: ELABORATION_BASELINE.to_owned(),
    })
}

pub(super) fn derive(root: &Path) -> Result<ElaborationFigure, EvidenceCheckError> {
    project(read_json(root, ELABORATION_BASELINE)?)
}

pub(super) fn measure(root: &Path) -> Result<Measurement, EvidenceCheckError> {
    let derived = derive(root)?;
    let scoreboard: RouteScoreboard<ElaborationRoute> = read_json(root, SCOREBOARD)?;
    let recorded = scoreboard.route.clean_elaborates_theories;
    if derived != recorded {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SCOREBOARD} route.clean_elaborates_theories differs from {ELABORATION_BASELINE}\nrecorded {recorded:?}\nderived  {derived:?}"
        )));
    }
    Ok(Measurement::TheoriesElaborated(derived))
}

#[derive(Deserialize)]
struct ElaborationProvenance {
    #[serde(rename = "schema")]
    _schema: ElaborationSchema,
    commit: Option<String>,
    source_snapshot_commit: Option<String>,
    measured_at_utc: Option<String>,
    version: Option<String>,
    build_profile: Option<String>,
    lean_version: Option<String>,
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let report: ElaborationProvenance = read_json(root, ELABORATION_BASELINE)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Measured at", report.measured_at_utc),
            ("Producer commit", report.commit),
            ("Source snapshot commit", report.source_snapshot_commit),
            ("Recorded binary version", report.version),
            ("Recorded build profile", report.build_profile),
            ("Recorded Lean version", report.lean_version),
        ],
        legs: None,
    })
}

#[cfg(test)]
mod tests {
    use super::ElaborationFigure;

    #[test]
    fn refuses_duplicate_package_counts_after_json_unescaping() {
        let row = r#"{
            "modules": 2, "elaborated": 1,
            "by_package": {
                "alpha": {"modules": 9, "elaborated": 9},
                "\u0061lpha": {"modules": 2, "elaborated": 1}
            },
            "producer_commit": "historical-binary", "source": "reports/self-proof-elab/baseline.json"
        }"#;
        let error = serde_json::from_str::<ElaborationFigure>(row).unwrap_err();
        assert!(error
            .to_string()
            .contains("duplicate package count \"alpha\""));
    }
}
