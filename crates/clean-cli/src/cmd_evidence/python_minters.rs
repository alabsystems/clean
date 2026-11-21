// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Present the canonical Python tooling observation on board row 16.

use super::{
    reading::{FreshnessReading, Outcome, Reading},
    ReportProvenance,
};
use crate::EvidenceCheckError;
use clean_evidence::envelope::python_minters::{self, InventoryError};
use std::path::Path;

impl From<InventoryError> for EvidenceCheckError {
    fn from(error: InventoryError) -> Self {
        match error {
            InventoryError::Invalid(reason) => Self::Invalid(reason),
            InventoryError::Unavailable(reason) => Self::Unavailable(reason),
        }
    }
}

pub(super) fn read(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let record = python_minters::read_record(root)?;
    let counts = record.counts;
    let envelope = record.envelope;
    let mut reading = Reading::new(
        envelope.value,
        format!(
            "{} tracked Python paths, {} registry path entries and {} implemented_by entries across {} rows",
            counts.tracked_scripts, counts.registry_path, counts.registry_implemented_by, counts.registry_rows
        ),
        freshness(record.fresh),
    );
    reading.labels = envelope.labels;
    reading.non_claims = envelope.non_claims;
    reading.commit = Some(envelope.provenance.clean_commit);
    reading.recorded_at = Some(envelope.provenance.finished_at);
    Ok(Outcome::Measured(Box::new(reading)))
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let record = python_minters::read_record(root)?;
    let freshness = freshness(record.fresh);
    let provenance = record.envelope.provenance;
    let inputs = &provenance.inputs;
    Ok(ReportProvenance {
        fields: vec![
            ("Recorded commit", Some(provenance.clean_commit)),
            ("Recorded at", Some(provenance.finished_at)),
            (
                "Recorded tree state",
                Some(format!("{:?}", provenance.tree_state)),
            ),
            (
                "Recorded producer argv",
                Some(
                    serde_json::to_string(&provenance.producer.argv)
                        .map_err(|error| EvidenceCheckError::Invalid(error.to_string()))?,
                ),
            ),
            (
                "Producer source digest",
                Some(provenance.producer.module_digest),
            ),
            ("Input digest", Some(inputs.digest.clone())),
            (
                python_minters::TRACKED_INPUT,
                inputs.files.get(python_minters::TRACKED_INPUT).cloned(),
            ),
            (
                python_minters::REGISTRY,
                inputs.files.get(python_minters::REGISTRY).cloned(),
            ),
            ("Publication gate", Some(record.envelope.gate_command)),
            (
                "Freshness",
                Some(format!("{} ({})", freshness.label(), freshness.reason)),
            ),
        ],
        legs: None,
    })
}

fn freshness(fresh: bool) -> FreshnessReading {
    if fresh {
        FreshnessReading::fresh("live Git index, registry bytes and all four counts match")
    } else {
        FreshnessReading::stale("tracked Python paths or gate registry bytes changed".to_owned())
    }
}
