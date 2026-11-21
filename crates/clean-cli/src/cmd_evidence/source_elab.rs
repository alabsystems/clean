// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The five-file Mathlib source-elaboration ratchet,
//! `data/source_elab_ratchet.json` (schema `Clean-srcelab-ratchet-v1`).
//!
//! The reader re-derives the totals from the per-file rows and refuses a row
//! whose success count exceeds its declarations. Binding the baseline to its
//! dated report stays with `scripts/source_elab_gate.sh --check-artifact`.

use super::read_json;
use super::reading::{DenominatorReading, FreshnessReading, Outcome, Reading};
use crate::EvidenceCheckError;
use serde::{Deserialize, Deserializer};
use serde_json::json;
use std::collections::BTreeMap;
use std::path::Path;

pub(super) const SOURCE_ELAB_RATCHET: &str = "data/source_elab_ratchet.json";
pub(super) const SOURCE_ELAB_FIGURE: &str = "frontend.source_elab";

#[derive(Deserialize)]
enum RatchetSchema {
    #[serde(rename = "Clean-srcelab-ratchet-v1")]
    V1,
}

#[derive(Deserialize)]
struct SourceElabRatchet {
    #[serde(rename = "schema_version")]
    _schema: RatchetSchema,
    last_updated: String,
    armed: bool,
    counting_basis: String,
    armed_commit: Option<String>,
    corpus: Corpus,
    #[serde(deserialize_with = "read_files")]
    files: BTreeMap<String, FileBaseline>,
}

fn read_files<'de, D: Deserializer<'de>>(
    input: D,
) -> Result<BTreeMap<String, FileBaseline>, D::Error> {
    super::read_unique_map(input, "corpus file")
}

#[derive(Deserialize)]
struct Corpus {
    rev: String,
    toolchain: String,
}

#[derive(Deserialize)]
struct FileBaseline {
    success_baseline: u64,
    decl_count: u64,
    sorry_axioms: u64,
}

pub(super) fn read(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let ratchet: SourceElabRatchet = read_json(root, SOURCE_ELAB_RATCHET)?;
    if ratchet.files.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SOURCE_ELAB_RATCHET} names no files"
        )));
    }
    let (mut success, mut declarations, mut sorry_axioms) = (0u64, 0u64, 0u64);
    for (file, row) in &ratchet.files {
        if row.decl_count == 0 || row.success_baseline > row.decl_count {
            return Err(EvidenceCheckError::Invalid(format!(
                "{SOURCE_ELAB_RATCHET} {file}: {} successes of {} declarations",
                row.success_baseline, row.decl_count
            )));
        }
        success += row.success_baseline;
        declarations += row.decl_count;
        sorry_axioms += row.sorry_axioms;
    }
    let summary = format!(
        "{success} of {declarations} declarations elaborate across {} Mathlib files{}",
        ratchet.files.len(),
        if ratchet.armed {
            ""
        } else {
            " (ratchet disarmed)"
        }
    );
    let mut reading = Reading::new(
        json!({
            "success": success,
            "files": ratchet.files.len(),
            "sorry_axioms": sorry_axioms,
            "armed": ratchet.armed,
        }),
        summary,
        FreshnessReading::unknown(
            "the measured corpus lies outside this checkout; only a source-elab gate run decides",
        ),
    );
    reading.denominator = Some(DenominatorReading::of_members(
        "declarations of the pinned five-file Mathlib slice",
        declarations,
        ratchet
            .files
            .iter()
            .map(|(file, row)| format!("{file} {}", row.decl_count)),
    )?);
    reading.labels = vec![
        format!("counting basis {}", ratchet.counting_basis),
        format!(
            "Mathlib {} under {}",
            ratchet.corpus.rev, ratchet.corpus.toolchain
        ),
    ];
    reading.non_claims = vec![
        "a five-file proxy and per-declaration regression guard, not a headline metric".to_owned(),
        "the dated-report binding is checked by scripts/source_elab_gate.sh --check-artifact"
            .to_owned(),
    ];
    reading.commit = ratchet.armed_commit;
    reading.recorded_at = Some(ratchet.last_updated);
    Ok(Outcome::Measured(Box::new(reading)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read_value(value: &serde_json::Value) -> Result<Outcome, EvidenceCheckError> {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join(SOURCE_ELAB_RATCHET);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, serde_json::to_vec(value).unwrap()).unwrap();
        read(root.path())
    }

    fn example() -> serde_json::Value {
        json!({
            "schema_version": "Clean-srcelab-ratchet-v1",
            "last_updated": "2026-10-17", "armed": true,
            "counting_basis": "allow_sorry_success", "armed_commit": "abc",
            "corpus": {"rev": "43ad", "toolchain": "v4.30.0-rc2"},
            "files": {
                "A.lean": {"success_baseline": 2, "decl_count": 3, "sorry_axioms": 0},
                "B.lean": {"success_baseline": 1, "decl_count": 1, "sorry_axioms": 0}
            }
        })
    }

    #[test]
    fn test_source_elab_totals_are_rederived_from_rows() {
        let Outcome::Measured(reading) = read_value(&example()).unwrap() else {
            panic!("expected a reading");
        };
        assert_eq!(reading.value["success"], 3);
        assert_eq!(reading.denominator.as_ref().unwrap().count, 4);
        assert_eq!(reading.freshness.label(), "unknown");
    }

    #[test]
    fn test_source_elab_success_above_declarations_is_invalid() {
        let mut ratchet = example();
        ratchet["files"]["B.lean"]["success_baseline"] = json!(2);
        let error = read_value(&ratchet).err().unwrap();
        assert!(error.to_string().contains("2 successes of 1 declarations"));
    }

    #[test]
    fn test_source_elab_unknown_schema_is_invalid() {
        let mut ratchet = example();
        ratchet["schema_version"] = json!("Clean-srcelab-ratchet-v2");
        let error = read_value(&ratchet).err().unwrap();
        assert!(matches!(error, EvidenceCheckError::Invalid(_)));
    }
}
