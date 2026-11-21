// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shadow the two K3 rows of the Python scoreboard from a verified receipt.

use super::k3_export::EXPORT;
use super::k3_receipt::{self, CoverageError, Labels, VerifiedCoverage, DECIDED_REASON, LABELS};
use super::k3_sources::{read_object, RECORD};
use super::w0_scoreboard::{Absent, RowValue};
use super::{Measurement, ReportProvenance, RouteScoreboard, Scoreboard, SCOREBOARD};
use crate::EvidenceCheckError;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::path::Path;

pub(super) const DECIDED_FIGURE: &str = "selfproof.decided_by_compiled_kcheck";
pub(super) const ACCEPTED_FIGURE: &str = "selfproof.accepted_by_kcheck_no_site";
pub(super) const INPUTS: &[&str] = &[
    RECORD,
    EXPORT,
    super::k3_packet::ADVICE,
    super::k3_packet::TRANSCRIPT,
    "theories/",
    SCOREBOARD,
];

#[derive(Clone, Copy)]
pub(super) enum Row {
    Decided,
    Accepted,
}

pub(super) enum Coverage {
    Verified(VerifiedCoverage),
    Absent(String),
}

pub(super) struct Snapshot {
    coverage: Coverage,
    scoreboard: Vec<u8>,
}

impl Snapshot {
    pub(super) fn read(root: &Path) -> Result<Self, EvidenceCheckError> {
        let coverage = Coverage::read(root)?;
        let path = root.join(SCOREBOARD);
        let scoreboard = fs::read(&path).map_err(|error| {
            EvidenceCheckError::Unavailable(format!("{}: {error}", path.display()))
        })?;
        Ok(Self {
            coverage,
            scoreboard,
        })
    }

    fn read_row<T: DeserializeOwned>(&self) -> Result<T, EvidenceCheckError> {
        let Object(value) = serde_json::from_slice(&self.scoreboard)
            .map_err(|error| EvidenceCheckError::Invalid(format!("{SCOREBOARD}: {error}")))?;
        Ok(value)
    }

    pub(super) fn measure(&self, row: Row) -> Result<Measurement, EvidenceCheckError> {
        match row {
            Row::Decided => {
                let derived = self.coverage.decided();
                let recorded: Scoreboard<Object<K3Headline>> = self.read_row()?;
                Ok(Measurement::K3Decided(compare(
                    "headline.decided_by_compiled_kcheck",
                    recorded.headline.0.decided_by_compiled_kcheck.0,
                    derived,
                )?))
            }
            Row::Accepted => {
                let derived = self.coverage.accepted();
                let recorded: RouteScoreboard<Object<K3Route>> = self.read_row()?;
                Ok(Measurement::K3Accepted(compare(
                    "route.accepted_by_kcheck_no_site",
                    recorded.route.0.accepted_by_kcheck_no_site.0,
                    derived,
                )?))
            }
        }
    }
}

impl Coverage {
    pub(super) fn read(root: &Path) -> Result<Self, EvidenceCheckError> {
        match k3_receipt::verify(root) {
            Ok(verified) => Ok(Self::Verified(verified)),
            Err(CoverageError::Absent(absence)) => Ok(Self::Absent(format!(
                "stale or absent: {}",
                absence.reason()
            ))),
            Err(error) => Err(error.into()),
        }
    }

    pub(super) fn decided(&self) -> RowValue<Decided> {
        self.row(|_| Decided {
            real_declarations_decided: 0,
            reason: DECIDED_REASON.into(),
            source: RECORD.into(),
        })
    }

    pub(super) fn accepted(&self) -> RowValue<Accepted> {
        self.row(|figures| Accepted {
            accepted: figures.accepted,
            export: EXPORT.into(),
            inside_fragment: figures.inside_fragment,
            labels: LABELS,
            ordinary_declarations: figures.ordinary_declarations,
            source: RECORD.into(),
        })
    }

    fn row<T>(&self, present: impl FnOnce(&VerifiedCoverage) -> T) -> RowValue<T> {
        match self {
            Self::Verified(verified) => RowValue::Present(present(verified)),
            Self::Absent(reason) => RowValue::Absent(Absent {
                absent: reason.clone(),
            }),
        }
    }
}

#[derive(Deserialize)]
#[serde(transparent, bound(deserialize = "T: Deserialize<'de>"))]
struct Object<T>(#[serde(deserialize_with = "read_object")] T);

#[derive(Deserialize)]
struct K3Headline {
    decided_by_compiled_kcheck: Object<RowValue<Decided>>,
}

#[derive(Deserialize)]
struct K3Route {
    accepted_by_kcheck_no_site: Object<RowValue<Accepted>>,
}

// Sorted field order matches the corresponding Python row after serialization.
#[derive(Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct Decided {
    pub(super) real_declarations_decided: usize,
    reason: String,
    source: String,
}

#[derive(Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct Accepted {
    pub(super) accepted: usize,
    export: String,
    pub(super) inside_fragment: usize,
    #[serde(deserialize_with = "read_object")]
    labels: Labels<'static>,
    pub(super) ordinary_declarations: usize,
    source: String,
}

fn compare<T: PartialEq>(
    field: &str,
    recorded: RowValue<T>,
    derived: RowValue<T>,
) -> Result<RowValue<T>, EvidenceCheckError> {
    if recorded == derived {
        return Ok(derived);
    }
    Err(EvidenceCheckError::Invalid(format!(
        "{SCOREBOARD} {field} differs from the K3 coverage derivation over {RECORD}"
    )))
}

impl fmt::Display for Decided {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} declarations decided at a site. {}",
            self.real_declarations_decided, self.reason
        )
    }
}

impl fmt::Display for Accepted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} of {} inside-fragment declarations accepted in the recorded interim run, {} ordinary declarations. No site consults this run",
            self.accepted, self.inside_fragment, self.ordinary_declarations
        )
    }
}

pub(super) fn read_provenance(root: &Path) -> Result<ReportProvenance, EvidenceCheckError> {
    let run = k3_receipt::recorded_run(root)?;
    Ok(ReportProvenance {
        fields: vec![
            ("Recorded producer command", Some(run.command)),
            ("Recorded Lean toolchain", Some(run.lean_toolchain)),
            ("Recorded Lean version", Some(run.lean_version)),
            ("Recorded executable SHA-256", Some(run.executable_sha256)),
        ],
        legs: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    const DECIDED: &str = "decided_by_compiled_kcheck";
    const ACCEPTED: &str = "accepted_by_kcheck_no_site";

    fn fixture() -> (Snapshot, Value) {
        let decided =
            json!({"real_declarations_decided": 0, "reason": DECIDED_REASON, "source": RECORD});
        let accepted = json!({
            "accepted": 9,
            "export": EXPORT,
            "inside_fragment": 22,
            "labels": LABELS,
            "ordinary_declarations": 256,
            "source": RECORD,
        });
        let scoreboard = json!({
            "schema": "clean.self_proof_scoreboard.v1",
            "headline": { (DECIDED): decided },
            "route": { (ACCEPTED): accepted },
        });
        let snapshot = Snapshot {
            coverage: Coverage::Verified(VerifiedCoverage {
                accepted: 9,
                inside_fragment: 22,
                ordinary_declarations: 256,
                sources: 42,
            }),
            scoreboard: serde_json::to_vec(&scoreboard).unwrap(),
        };
        (snapshot, scoreboard)
    }

    #[test]
    fn verifies_each_recorded_row_against_the_same_independent_receipt() {
        let (mut snapshot, mut scoreboard) = fixture();
        assert_eq!(
            serde_json::to_value(snapshot.measure(Row::Decided).unwrap()).unwrap(),
            scoreboard["headline"][DECIDED]
        );
        assert_eq!(
            serde_json::to_value(snapshot.measure(Row::Accepted).unwrap()).unwrap(),
            scoreboard["route"][ACCEPTED]
        );

        scoreboard["headline"][DECIDED]["real_declarations_decided"] = json!(1);
        snapshot.scoreboard = serde_json::to_vec(&scoreboard).unwrap();
        assert!(matches!(
            snapshot.measure(Row::Decided),
            Err(EvidenceCheckError::Invalid(message)) if message.contains("differs")
        ));
        assert!(snapshot.measure(Row::Accepted).is_ok());

        scoreboard["route"][ACCEPTED]["labels"]["site"] = json!("an invented site");
        snapshot.scoreboard = serde_json::to_vec(&scoreboard).unwrap();
        assert!(matches!(
            snapshot.measure(Row::Accepted),
            Err(EvidenceCheckError::Invalid(message)) if message.contains("differs")
        ));
    }

    #[test]
    fn refuses_alternative_row_shapes_and_duplicate_counts() {
        let (mut snapshot, scoreboard) = fixture();
        let canonical = serde_json::to_string(&scoreboard).unwrap();
        for before in ["\"real_declarations_decided\":0", "\"accepted\":9"] {
            let corrupt = canonical.replacen(before, &format!("{before},{before}"), 1);
            assert_ne!(corrupt, canonical);
            snapshot.scoreboard = corrupt.into_bytes();
            let row = if before.contains("decided") {
                Row::Decided
            } else {
                Row::Accepted
            };
            assert!(matches!(
                snapshot.measure(row),
                Err(EvidenceCheckError::Invalid(_))
            ));
        }
        let mut positional = scoreboard.clone();
        positional["headline"][DECIDED] = json!([0, DECIDED_REASON, RECORD]);
        snapshot.scoreboard = serde_json::to_vec(&positional).unwrap();
        assert!(matches!(
            snapshot.measure(Row::Decided),
            Err(EvidenceCheckError::Invalid(_))
        ));
        assert!(snapshot.measure(Row::Accepted).is_ok());
    }

    #[test]
    fn missing_receipt_only_matches_an_explicit_stable_absence() {
        let root = tempfile::tempdir().unwrap();
        let absent = json!({"absent": format!("stale or absent: {RECORD} does not exist")});
        let coverage = Coverage::read(root.path()).unwrap();
        assert_eq!(serde_json::to_value(coverage.decided()).unwrap(), absent);
        assert_eq!(serde_json::to_value(coverage.accepted()).unwrap(), absent);

        let path = root.path().join(SCOREBOARD);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        let (_, mut scoreboard) = fixture();
        scoreboard["headline"][DECIDED] = absent.clone();
        fs::write(&path, serde_json::to_vec(&scoreboard).unwrap()).unwrap();

        let snapshot = Snapshot::read(root.path()).unwrap();
        assert_eq!(
            serde_json::to_value(snapshot.measure(Row::Decided).unwrap()).unwrap(),
            absent
        );
        assert!(matches!(
            snapshot.measure(Row::Accepted),
            Err(EvidenceCheckError::Invalid(message)) if message.contains("differs")
        ));

        scoreboard["route"][ACCEPTED] = absent.clone();
        fs::write(path, serde_json::to_vec(&scoreboard).unwrap()).unwrap();
        assert!(snapshot.measure(Row::Accepted).is_err());
        let snapshot = Snapshot::read(root.path()).unwrap();
        assert_eq!(
            serde_json::to_value(snapshot.measure(Row::Accepted).unwrap()).unwrap(),
            absent
        );
    }
}
