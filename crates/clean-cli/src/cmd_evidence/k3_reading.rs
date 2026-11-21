// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Board readings of the two K3 coverage rows.
//!
//! Both rows come from one verification of the K3 coverage receipt against its
//! export, packet and pinned sources (`k3_scoreboard::Snapshot`). A receipt
//! that verifies is fresh by that comparison. A stale or absent receipt makes
//! the W0 row record its absence, and the board shows the figure as absent
//! with that reason.

use super::historical::reading;
use super::k3_scoreboard::{Row, Snapshot};
use super::k3_sources::RECORD;
use super::reading::{DenominatorReading, FreshnessReading, Outcome};
use super::w0_scoreboard::RowValue;
use super::{read_json, Measurement};
use crate::EvidenceCheckError;
use serde::Deserialize;
use std::path::Path;

#[derive(Deserialize)]
struct CoverageExport {
    export: ExportIdentity,
}

#[derive(Deserialize)]
struct ExportIdentity {
    path: String,
    sha256_decompressed: String,
}

const K3_NON_CLAIMS: &[&str] = &[
    "an accepted declaration is not a proved one, and no site consults this run",
    "the run was compiled by upstream Lean, not by Clean or Trust",
];

fn read_row(root: &Path, row: Row, labels: &[&str]) -> Result<Outcome, EvidenceCheckError> {
    let snapshot = Snapshot::read(root)?;
    let measurement = snapshot.measure(row)?;
    let absent = match &measurement {
        Measurement::K3Decided(RowValue::Absent(absent))
        | Measurement::K3Accepted(RowValue::Absent(absent)) => Some(absent.absent.clone()),
        _ => None,
    };
    if let Some(reason) = absent {
        return Ok(Outcome::Absent { reason });
    }
    let Measurement::K3Accepted(RowValue::Present(accepted)) = snapshot.measure(Row::Accepted)?
    else {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD}: the accepted row is absent while the decided row is present"
        )));
    };
    let export: CoverageExport = read_json(root, RECORD)?;
    let denominator = DenominatorReading::of_members(
        &format!("ordinary declarations of {}", export.export.path),
        accepted.ordinary_declarations as u64,
        [format!("sha256:{}", export.export.sha256_decompressed)],
    )?;
    let mut reading = reading(&measurement, Some(denominator), labels, K3_NON_CLAIMS)?;
    reading.freshness = FreshnessReading::fresh(
        "the coverage receipt re-verifies against its export, packet and pinned sources",
    );
    Ok(Outcome::Measured(Box::new(reading)))
}

pub(super) fn decided(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    read_row(
        root,
        Row::Decided,
        &["decided means a site consulted a compiled kcheck verdict"],
    )
}

pub(super) fn accepted(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    read_row(
        root,
        Row::Accepted,
        &["checker kcheck_labelled, run by the recorded interim executable"],
    )
}
