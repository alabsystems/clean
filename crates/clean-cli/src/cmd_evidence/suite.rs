// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The persistent suite runner's projected records, `data/suite_state/*.json`
//! (schema `clean.suite_state/v1`).
//!
//! The reader checks that each record's status agrees with its own exit code,
//! failure count and timeout, and that its file name spells its target. A
//! GREEN record that ran zero tests counts as unknown, as `docs/SUITE_STATE.md`
//! defines. The input digest of a record is a path-dependency closure that
//! only `scripts/verify_runner.sh status` recomputes, so freshness is unknown
//! here and a recorded GREEN is not a current GREEN.

use super::reading::{DenominatorReading, FreshnessReading, Outcome, Reading};
use crate::EvidenceCheckError;
use serde::Deserialize;
use serde_json::json;
use std::fs;
use std::path::Path;

pub(super) const SUITE_STATE: &str = "data/suite_state";
pub(super) const SUITE_FIGURE: &str = "suite.recorded_targets";

#[derive(Deserialize)]
enum SuiteSchema {
    #[serde(rename = "clean.suite_state/v1")]
    V1,
}

#[derive(Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "UPPERCASE")]
enum RecordedStatus {
    Green,
    Red,
    Error,
    Skipped,
    Superseded,
}

#[derive(Deserialize)]
struct SuiteRecord {
    #[serde(rename = "schema")]
    _schema: SuiteSchema,
    target: String,
    status: RecordedStatus,
    exit_code: Option<i64>,
    counts: Option<Counts>,
    timed_out: Option<bool>,
    finished_at: Option<String>,
}

#[derive(Deserialize)]
struct Counts {
    passed: u64,
    failed: u64,
}

#[derive(Default)]
struct Tally {
    green: u64,
    red: u64,
    unknown: u64,
}

/// Classify one record, refusing a status its own fields contradict.
fn classify(record: &SuiteRecord, tally: &mut Tally) -> Result<(), String> {
    let failed = record.counts.as_ref().map_or(0, |counts| counts.failed);
    let passed = record.counts.as_ref().map_or(0, |counts| counts.passed);
    let timed_out = record.timed_out.unwrap_or(false);
    match record.status {
        RecordedStatus::Green => {
            if record.exit_code != Some(0) || failed != 0 || timed_out {
                return Err("GREEN with a nonzero exit, a failure or a timeout".to_owned());
            }
            if passed == 0 {
                tally.unknown += 1;
            } else {
                tally.green += 1;
            }
        }
        RecordedStatus::Red => {
            if record.exit_code == Some(0) && failed == 0 && !timed_out {
                return Err("RED with exit 0, no failure and no timeout".to_owned());
            }
            tally.red += 1;
        }
        RecordedStatus::Error | RecordedStatus::Skipped | RecordedStatus::Superseded => {
            tally.unknown += 1;
        }
    }
    Ok(())
}

pub(super) fn read(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let directory = root.join(SUITE_STATE);
    let entries = fs::read_dir(&directory).map_err(|error| {
        EvidenceCheckError::Unavailable(format!("{}: {error}", directory.display()))
    })?;
    let mut names = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|error| {
            EvidenceCheckError::Unavailable(format!("{}: {error}", directory.display()))
        })?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.ends_with(".json") && entry.path().is_file() {
            names.push(name);
        }
    }
    names.sort_unstable();
    if names.is_empty() {
        return Err(EvidenceCheckError::Unavailable(format!(
            "{SUITE_STATE} holds no records"
        )));
    }
    let mut tally = Tally::default();
    let mut targets = Vec::with_capacity(names.len());
    let mut latest: Option<String> = None;
    for name in &names {
        let path = format!("{SUITE_STATE}/{name}");
        let record: SuiteRecord = super::read_json(root, &path)?;
        if format!("{}.json", record.target.replace("::", "__")) != *name {
            return Err(EvidenceCheckError::Invalid(format!(
                "{path} records target {:?}",
                record.target
            )));
        }
        classify(&record, &mut tally)
            .map_err(|reason| EvidenceCheckError::Invalid(format!("{path}: {reason}")))?;
        if let Some(finished) = &record.finished_at {
            if latest.as_ref().is_none_or(|known| finished > known) {
                latest = Some(finished.clone());
            }
        }
        targets.push(record.target);
    }
    let mut reading = Reading::new(
        json!({"green": tally.green, "red": tally.red, "unknown": tally.unknown}),
        format!(
            "{} recorded GREEN, {} RED and {} unknown of {} suite targets",
            tally.green,
            tally.red,
            tally.unknown,
            targets.len()
        ),
        FreshnessReading::unknown(
            "each record holds only while its input digest matches; \
             scripts/verify_runner.sh status recomputes it, this reader does not",
        ),
    );
    reading.denominator = Some(DenominatorReading::counting(
        "suite runner targets with a projected record",
        targets,
    )?);
    reading.labels = vec!["each record's own commit and argv, as projected".to_owned()];
    reading.non_claims = vec![
        "a recorded GREEN is not a current GREEN".to_owned(),
        "unknown counts zero-test, ERROR, SKIPPED and SUPERSEDED records".to_owned(),
    ];
    reading.recorded_at = latest;
    Ok(Outcome::Measured(Box::new(reading)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(root: &Path, name: &str, value: &serde_json::Value) {
        let path = root.join(SUITE_STATE).join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, serde_json::to_vec(value).unwrap()).unwrap();
    }

    fn record(
        target: &str,
        status: &str,
        exit: i64,
        passed: u64,
        failed: u64,
    ) -> serde_json::Value {
        json!({
            "schema": "clean.suite_state/v1", "target": target, "status": status,
            "exit_code": exit, "counts": {"passed": passed, "failed": failed},
            "timed_out": false, "finished_at": "2026-11-14T03:49:09Z"
        })
    }

    #[test]
    fn test_suite_tally_counts_zero_test_green_as_unknown() {
        let root = tempfile::tempdir().unwrap();
        write(
            root.path(),
            "a__lib.json",
            &record("a::lib", "GREEN", 0, 3, 0),
        );
        write(
            root.path(),
            "a__test__t.json",
            &record("a::test::t", "GREEN", 0, 0, 0),
        );
        write(
            root.path(),
            "b__lib.json",
            &record("b::lib", "RED", 101, 2, 1),
        );
        let Outcome::Measured(reading) = read(root.path()).unwrap() else {
            panic!("expected a reading");
        };
        assert_eq!(reading.value, json!({"green": 1, "red": 1, "unknown": 1}));
        assert_eq!(reading.denominator.as_ref().unwrap().count, 3);
        assert_eq!(reading.freshness.label(), "unknown");
    }

    #[test]
    fn test_suite_contradictory_status_is_invalid() {
        for (status, exit, failed) in [("GREEN", 101, 0), ("GREEN", 0, 1), ("RED", 0, 0)] {
            let root = tempfile::tempdir().unwrap();
            write(
                root.path(),
                "a__lib.json",
                &record("a::lib", status, exit, 1, failed),
            );
            let error = read(root.path()).err().unwrap();
            assert!(matches!(error, EvidenceCheckError::Invalid(_)), "{status}");
        }
    }

    #[test]
    fn test_suite_file_name_must_spell_target() {
        let root = tempfile::tempdir().unwrap();
        write(
            root.path(),
            "a__lib.json",
            &record("b::lib", "GREEN", 0, 1, 0),
        );
        let error = read(root.path()).err().unwrap();
        assert!(error.to_string().contains("records target"));
    }

    #[test]
    fn test_suite_missing_directory_is_unavailable() {
        let root = tempfile::tempdir().unwrap();
        let error = read(root.path()).err().unwrap();
        assert!(matches!(error, EvidenceCheckError::Unavailable(_)));
    }
}
