// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch-prep mode: turn a list of candidate corpus serials into a directory of
//! per-theorem Lean submission files plus a manifest, with the **unsupported
//! tail marked for human/agent curation**. This is what makes the next Path-B
//! batch's prep step "select serials → harness → curate only the unsupported
//! tail" instead of hand-translating every proposition.
//!
//! The corpus-reading helpers ([`fetch_line_by_serial`], [`fetch_line_by_name`])
//! seek through the `<corpus>.idx` sidecar when present (falling back to a
//! streaming scan), so a batch touches only the handful of lines it needs.

use std::io::BufRead as _;
use std::path::{Path, PathBuf};

use super::super::isabelle_import::leading_serial;
use super::super::isabelle_index;
use super::super::isabelle_pure::IsaTerm;
use super::census::Census;
use super::types::LeanGoal;
use super::{lean_name_from_isabelle, translate_prop};

/// Errors from the batch-prep / corpus-fetch path.
#[derive(Debug, thiserror::Error)]
pub enum BatchError {
    /// Filesystem failure reading the corpus or writing outputs.
    #[error("isabelle-lean-goal I/O on {path}: {source}")]
    Io {
        /// Path involved.
        path: PathBuf,
        /// Underlying error.
        source: std::io::Error,
    },
    /// A corpus line (or the `prop` field) did not parse as expected JSON.
    #[error("isabelle-lean-goal parse: {0}")]
    Parse(String),
    /// The requested serial is not present in the corpus.
    #[error("serial {0} not found in corpus")]
    SerialNotFound(i64),
    /// The requested theorem name is not present in the corpus.
    #[error("name {0} not found in corpus")]
    NameNotFound(String),
}

fn io_err(path: &Path) -> impl FnOnce(std::io::Error) -> BatchError + '_ {
    move |source| BatchError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// One prepared goal: the identity of a candidate theorem plus the harness
/// verdict ([`LeanGoal`]).
#[derive(Debug, Clone)]
pub struct PreparedGoal {
    /// Stable submission id (e.g. `s756380` or a caller-supplied index).
    pub id: String,
    /// The corpus serial, when known.
    pub serial: Option<i64>,
    /// The Isabelle theorem name.
    pub isabelle: String,
    /// The Lean theorem name (last dotted component).
    pub lean: String,
    /// The translation verdict.
    pub goal: LeanGoal,
}

/// One manifest row (serialized to `manifest.json`).
#[derive(Debug, Clone, serde::Serialize)]
pub struct ManifestEntry {
    /// Submission id.
    pub id: String,
    /// Corpus serial, when known.
    pub serial: Option<i64>,
    /// Isabelle name.
    pub isabelle: String,
    /// Lean name.
    pub lean: String,
    /// `"supported"` or `"unsupported"`.
    pub status: &'static str,
    /// The declined-shape reason (unsupported rows only).
    pub reason: Option<String>,
}

impl From<&PreparedGoal> for ManifestEntry {
    fn from(p: &PreparedGoal) -> Self {
        let (status, reason) = match &p.goal {
            LeanGoal::Supported(_) => ("supported", None),
            LeanGoal::Unsupported(u) => ("unsupported", Some(u.to_string())),
        };
        ManifestEntry {
            id: p.id.clone(),
            serial: p.serial,
            isabelle: p.isabelle.clone(),
            lean: p.lean.clone(),
            status,
            reason,
        }
    }
}

/// Summary of a batch-prep run.
#[derive(Debug, Clone, Copy, serde::Serialize)]
pub struct BatchReport {
    /// Total candidates prepared.
    pub total: usize,
    /// How many produced a faithful Lean statement.
    pub supported: usize,
    /// How many were declined (routed to the curation tail).
    pub unsupported: usize,
}

impl BatchReport {
    /// Supported fraction as a percentage (0 when empty).
    #[must_use]
    pub fn coverage_pct(&self) -> f64 {
        if self.total == 0 {
            0.0
        } else {
            100.0 * self.supported as f64 / self.total as f64
        }
    }
}

/// Extract the `"name"` and `"prop"` of a corpus/seed line, parsing `prop` into
/// an [`IsaTerm`]. Ignores the (possibly absent) proof — this lane translates
/// only the statement.
///
/// # Errors
/// [`BatchError::Parse`] if the line is not an object with a `prop`.
pub fn parse_line_prop(line: &str) -> Result<(String, IsaTerm), BatchError> {
    let v: serde_json::Value =
        serde_json::from_str(line).map_err(|e| BatchError::Parse(e.to_string()))?;
    let name = v
        .get("name")
        .and_then(|n| n.as_str())
        .unwrap_or_default()
        .to_string();
    let prop = v
        .get("prop")
        .ok_or_else(|| BatchError::Parse("line has no `prop` field".to_string()))?;
    let prop: IsaTerm =
        serde_json::from_value(prop.clone()).map_err(|e| BatchError::Parse(e.to_string()))?;
    Ok((name, prop))
}

/// Prepare one goal from a raw corpus line.
///
/// # Errors
/// [`BatchError::Parse`] on a malformed line.
pub fn prepare_from_line(
    id: String,
    serial: Option<i64>,
    line: &str,
) -> Result<PreparedGoal, BatchError> {
    let (isabelle, prop) = parse_line_prop(line)?;
    Ok(prepare(id, serial, &isabelle, &prop))
}

/// Prepare one goal from an already-parsed proposition.
#[must_use]
pub fn prepare(id: String, serial: Option<i64>, isabelle: &str, prop: &IsaTerm) -> PreparedGoal {
    let lean = lean_name_from_isabelle(isabelle);
    let goal = translate_prop(prop, &lean);
    PreparedGoal {
        id,
        serial,
        isabelle: isabelle.to_string(),
        lean,
        goal,
    }
}

/// Write a batch to `out_dir`: supported goals to `goals/<id>.lean` (a
/// `:= by sorry` submission stub), the unsupported tail to
/// `unsupported/<id>.txt` (Isabelle name + reason), and a `manifest.json` over
/// all rows. Returns the coverage summary.
///
/// # Errors
/// [`BatchError::Io`] on any write failure.
pub fn write_batch(out_dir: &Path, goals: &[PreparedGoal]) -> Result<BatchReport, BatchError> {
    let goals_dir = out_dir.join("goals");
    let unsup_dir = out_dir.join("unsupported");
    std::fs::create_dir_all(&goals_dir).map_err(io_err(&goals_dir))?;
    std::fs::create_dir_all(&unsup_dir).map_err(io_err(&unsup_dir))?;

    let mut supported = 0usize;
    let mut unsupported = 0usize;
    for g in goals {
        match &g.goal {
            LeanGoal::Supported(sg) => {
                supported += 1;
                let path = goals_dir.join(format!("{}.lean", g.id));
                let body = format!(
                    "import Mathlib\n\n-- Path-B batch-prep: Isabelle statement re-proved via curation.\n\
                     -- Isabelle: {}\n-- Prove `{}`; DO NOT change the statement.\n{}",
                    g.isabelle,
                    g.lean,
                    sg.sorry_stub()
                );
                std::fs::write(&path, body).map_err(io_err(&path))?;
            }
            LeanGoal::Unsupported(u) => {
                unsupported += 1;
                let path = unsup_dir.join(format!("{}.txt", g.id));
                let body = format!("{}\t{}\t{}\n", g.isabelle, g.lean, u);
                std::fs::write(&path, body).map_err(io_err(&path))?;
            }
        }
    }

    let manifest: Vec<ManifestEntry> = goals.iter().map(ManifestEntry::from).collect();
    let manifest_path = out_dir.join("manifest.json");
    let json =
        serde_json::to_string_pretty(&manifest).map_err(|e| BatchError::Parse(e.to_string()))?;
    std::fs::write(&manifest_path, json + "\n").map_err(io_err(&manifest_path))?;

    // `census.json`: the ranked unknown-const backlog + taxonomy + per-family
    // breakdown, so "68% unknown-const" is emitted as a concrete, prioritized
    // list of the specific constants worth teaching the library next.
    let census = Census::from_goals(goals);
    let census_path = out_dir.join("census.json");
    let census_json =
        serde_json::to_string_pretty(&census).map_err(|e| BatchError::Parse(e.to_string()))?;
    std::fs::write(&census_path, census_json + "\n").map_err(io_err(&census_path))?;

    Ok(BatchReport {
        total: goals.len(),
        supported,
        unsupported,
    })
}

/// Read the raw corpus line for `serial`, via the `.idx` sidecar when present
/// (else a streaming scan).
///
/// # Errors
/// [`BatchError::Io`] / [`BatchError::SerialNotFound`].
pub fn fetch_line_by_serial(corpus: &Path, serial: i64) -> Result<String, BatchError> {
    if let Some(index) = isabelle_index::try_load(corpus) {
        if let Some(entry) = index.get(serial) {
            return index.read_line(corpus, entry).map_err(|e| BatchError::Io {
                path: corpus.to_path_buf(),
                source: std::io::Error::other(e.to_string()),
            });
        }
        return Err(BatchError::SerialNotFound(serial));
    }
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        if leading_serial(&line) == Some(serial) {
            return Ok(line);
        }
    }
    Err(BatchError::SerialNotFound(serial))
}

/// Read the raw corpus line whose `"name"` field is exactly `name`, via the
/// `.idx` sidecar when present (else a streaming scan). Returns the first match.
///
/// # Errors
/// [`BatchError::Io`] / [`BatchError::NameNotFound`].
pub fn fetch_line_by_name(corpus: &Path, name: &str) -> Result<String, BatchError> {
    if let Some(index) = isabelle_index::try_load(corpus) {
        if let Some(entry) = index.entries.iter().find(|e| e.name == name) {
            return index.read_line(corpus, entry).map_err(|e| BatchError::Io {
                path: corpus.to_path_buf(),
                source: std::io::Error::other(e.to_string()),
            });
        }
        return Err(BatchError::NameNotFound(name.to_string()));
    }
    let needle = format!("\"name\":\"{name}\"");
    let reader = std::io::BufReader::new(std::fs::File::open(corpus).map_err(io_err(corpus))?);
    for line in reader.lines() {
        let line = line.map_err(io_err(corpus))?;
        if line.contains(&needle) {
            return Ok(line);
        }
    }
    Err(BatchError::NameNotFound(name.to_string()))
}

/// Read a candidate list file: one serial per non-empty, non-`#` line (a leading
/// `s` is tolerated, e.g. `s756380`).
///
/// # Errors
/// [`BatchError::Io`] on read failure; [`BatchError::Parse`] on a non-numeric
/// entry.
pub fn read_candidate_serials(path: &Path) -> Result<Vec<i64>, BatchError> {
    let text = std::fs::read_to_string(path).map_err(io_err(path))?;
    let mut serials = Vec::new();
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let digits = line.strip_prefix('s').unwrap_or(line);
        let serial: i64 = digits
            .parse()
            .map_err(|_| BatchError::Parse(format!("bad serial line: {raw:?}")))?;
        serials.push(serial);
    }
    Ok(serials)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED_ADD0: &str = include_str!("../../../tests/fixtures/isabelle/pathb_seed_add0.json");

    #[test]
    fn parse_line_prop_extracts_name_and_prop() {
        let (name, _prop) = parse_line_prop(SEED_ADD0).expect("seed parses");
        assert_eq!(name, "Nat.add_0_right");
    }

    #[test]
    fn prepare_from_line_translates_add0() {
        let g = prepare_from_line("s672628".into(), Some(672628), SEED_ADD0).unwrap();
        assert_eq!(g.lean, "add_0_right");
        match g.goal {
            LeanGoal::Supported(sg) => {
                assert!(sg.signature.contains("m + 0 = m"), "sig: {}", sg.signature);
            }
            other => panic!("expected supported, got {other:?}"),
        }
    }

    #[test]
    fn write_batch_marks_supported_and_unsupported() {
        let dir = std::env::temp_dir().join(format!("pathb_batch_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let supported = prepare_from_line("s672628".into(), Some(672628), SEED_ADD0).unwrap();
        // A synthetic unsupported goal (multiset add_mset — outside the library).
        let unsup = PreparedGoal {
            id: "u01".into(),
            serial: None,
            isabelle: "Multiset.foo".into(),
            lean: "foo".into(),
            goal: LeanGoal::Unsupported(super::super::types::Unsupported::UnknownConst(
                "Multiset.add_mset".into(),
            )),
        };
        let report = write_batch(&dir, &[supported, unsup]).unwrap();
        assert_eq!(report.total, 2);
        assert_eq!(report.supported, 1);
        assert_eq!(report.unsupported, 1);
        assert!(dir.join("goals/s672628.lean").exists());
        assert!(dir.join("unsupported/u01.txt").exists());
        assert!(dir.join("manifest.json").exists());
        let manifest = std::fs::read_to_string(dir.join("manifest.json")).unwrap();
        assert!(manifest.contains("\"status\": \"unsupported\""));
        // `census.json` is emitted with the ranked unknown-const backlog.
        assert!(dir.join("census.json").exists());
        let census = std::fs::read_to_string(dir.join("census.json")).unwrap();
        assert!(census.contains("\"unknown_const_rank\""));
        assert!(census.contains("Multiset.add_mset"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    const MINI_CORPUS: &str =
        include_str!("../../../tests/fixtures/isabelle/pathb_mini_corpus.jsonl");

    #[test]
    fn idx_seek_fetches_by_serial_and_name() {
        let dir = std::env::temp_dir().join(format!("pathb_idx_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let corpus = dir.join("corpus.jsonl");
        std::fs::write(&corpus, MINI_CORPUS).unwrap();

        // Build + save the `.idx` sidecar so the seek path (not the scan) runs.
        let index = isabelle_index::build_index(&corpus).unwrap();
        isabelle_index::save_index(&isabelle_index::index_path(&corpus), &index).unwrap();

        // By serial → the exact line, translated faithfully.
        let line = fetch_line_by_serial(&corpus, 672628).unwrap();
        let g = prepare_from_line("s672628".into(), Some(672628), &line).unwrap();
        assert_eq!(g.lean, "add_0_right");
        assert!(matches!(g.goal, LeanGoal::Supported(_)));

        // By name → append_assoc.
        let line = fetch_line_by_name(&corpus, "List.append_assoc").unwrap();
        let g = prepare_from_line("s2781200".into(), Some(2781200), &line).unwrap();
        assert_eq!(g.lean, "append_assoc");
        match g.goal {
            LeanGoal::Supported(sg) => {
                assert!(sg.signature.contains("(xs ++ ys) ++ zs = xs ++ (ys ++ zs)"))
            }
            other => panic!("expected supported, got {other:?}"),
        }

        // A missing serial/name is a typed error, not a panic.
        assert!(matches!(
            fetch_line_by_serial(&corpus, 999),
            Err(BatchError::SerialNotFound(999))
        ));
        assert!(matches!(
            fetch_line_by_name(&corpus, "Nope.nope"),
            Err(BatchError::NameNotFound(_))
        ));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn read_candidate_serials_tolerates_s_prefix_and_comments() {
        let dir = std::env::temp_dir().join(format!("pathb_cand_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("cands.txt");
        std::fs::write(&f, "# header\ns672628\n756380\n\n").unwrap();
        let serials = read_candidate_serials(&f).unwrap();
        assert_eq!(serials, vec![672628, 756380]);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
