// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Board row 15 (`seams`, design unit D4) and the route-of-record lane table
//! (`tooling.route_lanes`, design unit EV6).
//!
//! `read_seams` validates `data/seams.toml` (`SM1..SM7` in exact canonical
//! order, non-empty metadata, and an existing `evidence_artifact` file for
//! every `closed` or `refuted` seam and any `open` seam that cites one).
//!
//! `read_route_lanes` validates `data/route_lanes.toml` against Plan §0, the
//! registered `FIGURES` catalog, and `theories/cic_l/README.md` (§5.6 item 2).

use super::catalog::FIGURES;
use super::reading::{DenominatorReading, FreshnessReading, Outcome, Reading};
use crate::EvidenceCheckError;
use clean_evidence::digest::sha256_file;
use serde::Deserialize;
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

pub(super) const SEAMS_FIGURE: &str = "seams";
pub(super) const SEAMS_TOML: &str = "data/seams.toml";

pub(super) const ROUTE_LANES_FIGURE: &str = "tooling.route_lanes";
pub(super) const ROUTE_LANES_TOML: &str = "data/route_lanes.toml";
pub(super) const CIC_L_README: &str = "theories/cic_l/README.md";
pub(super) const ROUTE_LANES_INPUTS: &[&str] = &[ROUTE_LANES_TOML, CIC_L_README];

const REQUIRED_SEAM_IDS: &[&str] = &["SM1", "SM2", "SM3", "SM4", "SM5", "SM6", "SM7"];

const MANDATORY_PAUSED_UNTIL_W5: &[&str] = &[
    "S1", "S2", "S3", "S4", "S5", "S6", "M5", "M6", "C6", "C7", "C8", "Q5", "Q6", "P4", "P5", "P7",
    "E5",
];

const ALLOWED_PROBE_CAPPED_UNITS: &[&str] = &[
    "G.1",
    "G.2",
    "S+",
    "clean-specr",
    "diff.kernel",
    "semr-schema",
];

const STALE_CIC_L_BULLET: &str =
    "- **Literals, projections and free variables have no typing rule.**";

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
enum SeamStatus {
    Open,
    Closed,
    Refuted,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SeamRow {
    id: String,
    title: String,
    probe_unit: String,
    refutation_criterion: String,
    status: SeamStatus,
    #[serde(default)]
    evidence_artifact: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SeamsTable {
    schema: String,
    #[serde(rename = "seam", default)]
    seams: Vec<SeamRow>,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
enum LaneClass {
    #[serde(rename = "continue")]
    Continue,
    #[serde(rename = "pause")]
    Pause,
    #[serde(rename = "probe-capped")]
    ProbeCapped,
    #[serde(rename = "stop")]
    Stop,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteLaneUnit {
    id: String,
    lane: LaneClass,
    group: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteLanesTable {
    schema: String,
    probe_capped_max_in_flight: usize,
    #[serde(default)]
    probe_capped_in_flight: Vec<String>,
    #[serde(default)]
    w5_held_artifact: String,
    #[serde(rename = "unit", default)]
    units: Vec<RouteLaneUnit>,
}

fn read_toml_with_digest<T: serde::de::DeserializeOwned>(
    root: &Path,
    rel: &str,
) -> Result<(T, String), EvidenceCheckError> {
    let path = root.join(rel);
    let raw = fs::read_to_string(&path)
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())))?;
    let digest = sha256_file(&path)
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())))?;
    let parsed = toml::from_str(&raw)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{rel}: {error}")))?;
    Ok((parsed, digest))
}

pub(super) fn read_seams(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let (parsed, toml_sha256): (SeamsTable, String) = read_toml_with_digest(root, SEAMS_TOML)?;
    if parsed.schema != "clean.seams/v1" {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SEAMS_TOML}: expected schema `clean.seams/v1`, got {:?}",
            parsed.schema
        )));
    }
    let got_ids: Vec<&str> = parsed.seams.iter().map(|s| s.id.as_str()).collect();
    if got_ids.as_slice() != REQUIRED_SEAM_IDS {
        return Err(EvidenceCheckError::Invalid(format!(
            "{SEAMS_TOML}: expected canonical seam sequence {REQUIRED_SEAM_IDS:?}, got {got_ids:?}"
        )));
    }

    let (mut closed, mut open, mut refuted) = (0u64, 0u64, 0u64);
    for seam in &parsed.seams {
        if seam.title.trim().is_empty()
            || seam.probe_unit.trim().is_empty()
            || seam.refutation_criterion.trim().is_empty()
        {
            return Err(EvidenceCheckError::Invalid(format!(
                "{SEAMS_TOML}: seam {:?} has an empty title, probe_unit, or refutation_criterion",
                seam.id
            )));
        }
        let rel = seam.evidence_artifact.trim();
        match seam.status {
            SeamStatus::Open => {
                if !rel.is_empty() && !root.join(rel).is_file() {
                    return Err(EvidenceCheckError::Invalid(format!(
                        "{SEAMS_TOML}: open seam {:?} cites missing evidence_artifact {rel:?}",
                        seam.id
                    )));
                }
                open += 1;
            }
            SeamStatus::Closed | SeamStatus::Refuted => {
                if rel.is_empty() {
                    return Err(EvidenceCheckError::Invalid(format!(
                        "{SEAMS_TOML}: seam {:?} has status {:?} without an evidence_artifact path",
                        seam.id, seam.status
                    )));
                }
                if !root.join(rel).is_file() {
                    return Err(EvidenceCheckError::Invalid(format!(
                        "{SEAMS_TOML}: seam {:?} cites missing evidence_artifact {rel:?}",
                        seam.id
                    )));
                }
                if seam.status == SeamStatus::Closed {
                    closed += 1;
                } else {
                    refuted += 1;
                }
            }
        }
    }

    let total = parsed.seams.len() as u64;
    let mut reading = Reading::new(
        json!({
            "closed": closed,
            "open": open,
            "refuted": refuted,
            "total": total,
        }),
        format!(
            "{closed} closed, {open} open and {refuted} refuted of {total} architectural seams"
        ),
        FreshnessReading::fresh(
            "re-derived in this run from live data/seams.toml and cited evidence artifacts",
        ),
    );
    reading.denominator = Some(DenominatorReading::counting(
        "architectural seams SM1..SM7 in data/seams.toml",
        parsed.seams.iter().map(|seam| seam.id.as_str()),
    )?);
    reading.labels = vec![
        format!("{SEAMS_TOML} sha256:{toml_sha256}"),
        "by design until closed by committed artifact".to_owned(),
    ];
    reading.non_claims = vec![
        "seam registration is a risk and probe ledger, not a proof or closure claim".to_owned(),
        "closed or refuted seams require an existing committed evidence_artifact".to_owned(),
    ];
    Ok(Outcome::Measured(Box::new(reading)))
}

pub(super) fn read_route_lanes(root: &Path) -> Result<Outcome, EvidenceCheckError> {
    let (parsed, toml_sha256): (RouteLanesTable, String) =
        read_toml_with_digest(root, ROUTE_LANES_TOML)?;
    if parsed.schema != "clean.route-lanes/v1" {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ROUTE_LANES_TOML}: expected schema `clean.route-lanes/v1`, got {:?}",
            parsed.schema
        )));
    }
    if parsed.probe_capped_max_in_flight > 1 {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ROUTE_LANES_TOML}: probe_capped_max_in_flight is {}, but Plan §0 allows at most 1",
            parsed.probe_capped_max_in_flight
        )));
    }
    if parsed.probe_capped_in_flight.len() > parsed.probe_capped_max_in_flight {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ROUTE_LANES_TOML}: probe_capped_in_flight has {} entries (max {})",
            parsed.probe_capped_in_flight.len(),
            parsed.probe_capped_max_in_flight
        )));
    }

    let mut by_id: BTreeMap<&str, &RouteLaneUnit> = BTreeMap::new();
    let (mut continue_units, mut paused_units, mut probe_capped_units, mut stopped_units) =
        (0u64, 0u64, 0u64, 0u64);

    for unit in &parsed.units {
        if unit.id.trim().is_empty() || unit.group.trim().is_empty() {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: unit entry has an empty id or group"
            )));
        }
        if by_id.insert(unit.id.as_str(), unit).is_some() {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: duplicate unit id {:?}",
                unit.id
            )));
        }
        match unit.lane {
            LaneClass::Continue => continue_units += 1,
            LaneClass::Pause => paused_units += 1,
            LaneClass::ProbeCapped => {
                if !ALLOWED_PROBE_CAPPED_UNITS.contains(&unit.id.as_str()) {
                    return Err(EvidenceCheckError::Invalid(format!(
                        "{ROUTE_LANES_TOML}: unit {:?} is marked probe-capped outside allowed set {ALLOWED_PROBE_CAPPED_UNITS:?}",
                        unit.id
                    )));
                }
                probe_capped_units += 1;
            }
            LaneClass::Stop => stopped_units += 1,
        }
    }

    let w5_rel = parsed.w5_held_artifact.trim();
    let w5_holds = !w5_rel.is_empty() && root.join(w5_rel).is_file();
    if !w5_rel.is_empty() && !w5_holds {
        return Err(EvidenceCheckError::Invalid(format!(
            "{ROUTE_LANES_TOML}: w5_held_artifact {w5_rel:?} does not exist on disk"
        )));
    }
    if !w5_holds {
        for req in MANDATORY_PAUSED_UNTIL_W5 {
            let Some(unit) = by_id.get(req) else {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{ROUTE_LANES_TOML}: mandatory Plan §0 paused unit {req:?} is missing"
                )));
            };
            if unit.lane != LaneClass::Pause {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{ROUTE_LANES_TOML}: unit {req:?} must stay `pause` until W5 holds (found {:?})",
                    unit.lane
                )));
            }
        }
    }

    let mut seen_in_flight = BTreeSet::new();
    for flight_id in &parsed.probe_capped_in_flight {
        if !seen_in_flight.insert(flight_id.as_str()) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: duplicate {flight_id:?} in probe_capped_in_flight"
            )));
        }
        let Some(unit) = by_id.get(flight_id.as_str()) else {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: unknown unit {flight_id:?} in probe_capped_in_flight"
            )));
        };
        if unit.lane != LaneClass::ProbeCapped {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: unit {flight_id:?} in probe_capped_in_flight has lane {:?} (expected probe-capped)",
                unit.lane
            )));
        }
    }

    for figure in FIGURES {
        let Some(unit) = by_id.get(figure.plan_unit) else {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: figure {:?} cites plan_unit {:?} missing from route_lanes.toml",
                figure.id, figure.plan_unit
            )));
        };
        if figure.absent_reason().is_none()
            && matches!(unit.lane, LaneClass::Pause | LaneClass::Stop)
        {
            return Err(EvidenceCheckError::Invalid(format!(
                "{ROUTE_LANES_TOML}: active figure {:?} claims paused/stopped unit {:?}",
                figure.id, figure.plan_unit
            )));
        }
    }

    let readme_path = root.join(CIC_L_README);
    if readme_path.is_file() {
        let readme = fs::read_to_string(&readme_path).map_err(|error| {
            EvidenceCheckError::Unavailable(format!("{}: {error}", readme_path.display()))
        })?;
        if readme.contains(STALE_CIC_L_BULLET) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{CIC_L_README} still carries stale unqualified bullet {STALE_CIC_L_BULLET:?} (§5.6 item 2)"
            )));
        }
    }

    let total_units = parsed.units.len() as u64;
    let in_flight = parsed.probe_capped_in_flight.len() as u64;
    let mut reading = Reading::new(
        json!({
            "continue": continue_units,
            "pause": paused_units,
            "probe_capped": probe_capped_units,
            "probe_capped_in_flight": in_flight,
            "stop": stopped_units,
            "total": total_units,
        }),
        format!(
            "{continue_units} continue, {paused_units} paused, {probe_capped_units} probe-capped ({in_flight} in flight) and {stopped_units} stopped of {total_units} route units"
        ),
        FreshnessReading::fresh(
            "re-derived in this run from live data/route_lanes.toml, catalog and cic_l README",
        ),
    );
    reading.denominator = Some(DenominatorReading::counting(
        "route units in data/route_lanes.toml",
        parsed.units.iter().map(|unit| unit.id.as_str()),
    )?);
    reading.labels = vec![
        format!("{ROUTE_LANES_TOML} sha256:{toml_sha256}"),
        "Plan §0 ordering rule 1: no CIC_L/model/checker family widened before W5".to_owned(),
        "probe-capped max in flight = 1".to_owned(),
    ];
    reading.non_claims = vec![
        "lane membership authorizes scheduling only; each unit's completion is read from its gate-minted artifact".to_owned(),
    ];
    Ok(Outcome::Measured(Box::new(reading)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> std::path::PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf()
    }

    fn base_seams_toml() -> String {
        let mut out = String::from("schema = \"clean.seams/v1\"\n\n");
        for id in REQUIRED_SEAM_IDS {
            out.push_str(&format!(
                "[[seam]]\nid = \"{id}\"\ntitle = \"Seam {id}\"\nprobe_unit = \"P.{id}\"\nrefutation_criterion = \"Refute {id}\"\nstatus = \"open\"\nevidence_artifact = \"\"\n\n"
            ));
        }
        out
    }

    fn base_route_lanes_toml() -> String {
        let mut out = String::from(
            "schema = \"clean.route-lanes/v1\"\nprobe_capped_max_in_flight = 1\nprobe_capped_in_flight = []\nw5_held_artifact = \"\"\n\n",
        );
        let mut added = BTreeSet::new();
        for req in MANDATORY_PAUSED_UNTIL_W5 {
            if added.insert(*req) {
                out.push_str(&format!(
                    "[[unit]]\nid = \"{req}\"\nlane = \"pause\"\ngroup = \"paused-until-w5\"\n\n"
                ));
            }
        }
        for probe in ALLOWED_PROBE_CAPPED_UNITS {
            if added.insert(*probe) {
                out.push_str(&format!(
                    "[[unit]]\nid = \"{probe}\"\nlane = \"probe-capped\"\ngroup = \"probe\"\n\n"
                ));
            }
        }
        for figure in FIGURES {
            if added.insert(figure.plan_unit) {
                out.push_str(&format!(
                    "[[unit]]\nid = \"{}\"\nlane = \"continue\"\ngroup = \"catalog\"\n\n",
                    figure.plan_unit
                ));
            }
        }
        out.push_str(
            "[[unit]]\nid = \"event-only-bookkeeping\"\nlane = \"stop\"\ngroup = \"stopped\"\n\n",
        );
        out
    }

    #[test]
    fn test_live_repo_seams_and_route_lanes_validate() {
        let root = repo_root();
        let Outcome::Measured(seams) = read_seams(&root).unwrap() else {
            panic!("expected measured seams");
        };
        assert_eq!(seams.value["total"], 7);
        assert_eq!(seams.denominator.as_ref().unwrap().count, 7);
        assert_eq!(seams.freshness.label(), "fresh");

        let Outcome::Measured(lanes) = read_route_lanes(&root).unwrap() else {
            panic!("expected measured route_lanes");
        };
        assert_eq!(lanes.value["pause"], 17);
        assert_eq!(lanes.value["probe_capped_in_flight"], 0);
        assert_eq!(lanes.freshness.label(), "fresh");
    }

    #[test]
    fn test_seams_refuses_prose_only_closure_and_missing_artifacts() {
        let dir = tempfile::tempdir().unwrap();
        let toml_path = dir.path().join(SEAMS_TOML);
        fs::create_dir_all(toml_path.parent().unwrap()).unwrap();
        let base = base_seams_toml();
        fs::write(&toml_path, &base).unwrap();

        let Outcome::Measured(reading) = read_seams(dir.path()).unwrap() else {
            panic!("expected measured seams");
        };
        assert_eq!(reading.value["open"], 7);
        assert_eq!(reading.value["closed"], 0);

        // Arm 1: closed without evidence_artifact -> refused.
        let closed_no_art = base.replacen("status = \"open\"", "status = \"closed\"", 1);
        fs::write(&toml_path, closed_no_art).unwrap();
        assert!(read_seams(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("without an evidence_artifact"));

        // Arm 2: closed with missing evidence_artifact file -> refused.
        let closed_missing_art = base.replacen(
            "status = \"open\"\nevidence_artifact = \"\"",
            "status = \"closed\"\nevidence_artifact = \"reports/missing.md\"",
            1,
        );
        fs::write(&toml_path, &closed_missing_art).unwrap();
        assert!(read_seams(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("cites missing evidence_artifact"));

        // Creating the cited artifact makes closure pass with closed = 1.
        let art_path = dir.path().join("reports/missing.md");
        fs::create_dir_all(art_path.parent().unwrap()).unwrap();
        fs::write(&art_path, "receipt\n").unwrap();
        let Outcome::Measured(closed_ok) = read_seams(dir.path()).unwrap() else {
            panic!("expected measured seams");
        };
        assert_eq!(closed_ok.value["closed"], 1);
        assert_eq!(closed_ok.value["open"], 6);

        // Arm 3: corrupted canonical sequence -> refused.
        let bad_seq = base.replace("id = \"SM7\"", "id = \"SMX\"");
        fs::write(&toml_path, bad_seq).unwrap();
        assert!(read_seams(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("expected canonical seam sequence"));
    }

    #[test]
    fn test_route_lanes_refuses_unpaused_w5_two_probes_and_stale_readme() {
        let dir = tempfile::tempdir().unwrap();
        let toml_path = dir.path().join(ROUTE_LANES_TOML);
        let readme_path = dir.path().join(CIC_L_README);
        fs::create_dir_all(toml_path.parent().unwrap()).unwrap();
        fs::create_dir_all(readme_path.parent().unwrap()).unwrap();

        let base = base_route_lanes_toml();
        fs::write(&toml_path, &base).unwrap();
        fs::write(
            &readme_path,
            "## Open specification items\n\n- **CoreTyping stays minimal.**\n",
        )
        .unwrap();
        read_route_lanes(dir.path()).unwrap();

        // Arm 1: unpausing C6 before W5 holds -> refused.
        let unpaused_c6 = base.replace(
            "id = \"C6\"\nlane = \"pause\"",
            "id = \"C6\"\nlane = \"continue\"",
        );
        fs::write(&toml_path, unpaused_c6).unwrap();
        assert!(read_route_lanes(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("must stay `pause` until W5 holds"));

        // Arm 2: two probe-capped units in flight -> refused.
        let two_probes = base.replace(
            "probe_capped_in_flight = []",
            "probe_capped_in_flight = [\"G.1\", \"G.2\"]",
        );
        fs::write(&toml_path, two_probes).unwrap();
        assert!(read_route_lanes(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("probe_capped_in_flight has 2 entries"));

        // Arm 3: missing w5_held_artifact -> refused.
        let fake_w5 = base.replace(
            "w5_held_artifact = \"\"",
            "w5_held_artifact = \"reports/missing-w5.json\"",
        );
        fs::write(&toml_path, fake_w5).unwrap();
        assert!(read_route_lanes(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("w5_held_artifact"));

        // Arm 4: stale unqualified bullet in theories/cic_l/README.md -> refused.
        fs::write(&toml_path, &base).unwrap();
        fs::write(&readme_path, format!("## Open\n\n{STALE_CIC_L_BULLET}\n")).unwrap();
        assert!(read_route_lanes(dir.path())
            .err()
            .unwrap()
            .to_string()
            .contains("stale unqualified bullet"));
    }
}
