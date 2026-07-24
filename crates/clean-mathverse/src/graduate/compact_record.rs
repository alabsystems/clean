// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compact graduation record — schema `mathverse-graduation-record-v1`.
//!
//! Storage refactor (`designs/2026-06-24-graduation-storage-and-distribution.md`):
//! the heavy `.mathverse` shard and the full-closure `.graduation.json` move
//! into the gitignored content-addressed store; the single new git artifact is
//! this ~1-2 KB COMPACT record, which preserves every trust-bearing field
//! verbatim and replaces the flat closure dumps with COUNTS plus the
//! `shard.blake3` that pins the heavy artifact.
//!
//! This module is a faithful, lossy-only-on-mechanical-bulk PROJECTION of an
//! existing `mathverse-graduation-v3.x` record (read as untyped JSON so every
//! historical schema version v1..v3.2 round-trips) plus the produced
//! `.mathverse` shard. It **transcribes** the gate's verdict — it never decides
//! soundness, never re-runs the kernel, and never touches the proof, the kernel,
//! or the gate. The printed `statement` is reconstructed from the shard's own
//! type encoding (the `Expr` `Display` impl), so it is the literal claim the
//! kernel re-checked.

use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;

/// Pinned schema discriminant for the compact record.
pub const COMPACT_RECORD_SCHEMA: &str = "mathverse-graduation-record-v1";

/// The three core Lean 4 foundational axioms surfaced verbatim for a
/// foundational-only theorem's `axiom_closure` (the trust-bearing set a reviewer
/// reads; matches a theorem's `#print axioms` for a constructive proof). Kept as
/// a local constant so the record writer never reaches into the kernel's wider
/// `FOUNDATIONAL_AXIOMS` whitelist (which additionally lists `Eq.refl`,
/// `proofIrrel`, …) — the record transcribes the trust claim, not the whitelist.
const CORE_FOUNDATIONAL_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// Errors surfaced while projecting a full graduation record into the compact
/// `mathverse-graduation-record-v1` form.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CompactRecordError {
    /// Reading the full graduation JSON or the shard file failed.
    #[error("io reading `{path}`: {source}")]
    Io {
        /// Path that failed to read.
        path: String,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },
    /// The full graduation JSON did not parse.
    #[error("failed to parse graduation JSON `{path}`: {source}")]
    ParseJson {
        /// Path of the unparseable graduation record.
        path: String,
        /// Underlying serde error.
        #[source]
        source: serde_json::Error,
    },
    /// The `.mathverse` shard did not parse.
    #[error(transparent)]
    Shard(#[from] crate::error::MathverseError),
    /// A required, trust-bearing field was missing or the wrong shape.
    #[error("graduation record `{path}` is missing or has malformed field `{field}`")]
    MissingField {
        /// Path of the graduation record.
        path: String,
        /// JSON field that was absent or malformed.
        field: String,
    },
    /// Serializing the compact record failed.
    #[error("failed to serialize compact record: {0}")]
    Serialize(#[from] serde_json::Error),
}

type Result<T> = std::result::Result<T, CompactRecordError>;

/// One graduated-theorem entry in the compact record — the NOVEL front matter
/// (statement, axiom closure, novelty), never the carried closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactTheorem {
    /// Fully-qualified declaration name.
    pub name: String,
    /// Human-readable statement: the constant's TYPE, reconstructed from the
    /// shard and rendered via the kernel `Expr` `Display`. This is the literal
    /// claim the kernel re-checked (the thing being trusted).
    pub statement: String,
    /// Universe parameters; `[]` for a monomorphic theorem.
    pub level_params: Vec<String>,
    /// The transitive axiom closure: `domain_axioms` first, then — when the
    /// gate reports `foundational_only` — the three core foundational axioms.
    /// MUST be `⊆ FOUNDATIONAL_AXIOMS` for a "prove" claim.
    pub axiom_closure: Vec<String>,
    /// The `expr_canonical_digest`-grade key the novelty gate / `.mvix` index
    /// use (the full record's `statement_hash`).
    pub novelty_digest: String,
    /// True iff the gate's novelty verdict was `"new"` (absent from the corpus).
    pub novel: bool,
}

/// Gate verdict (transcribed verbatim — never recomputed by this writer).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactGate {
    /// Every graduated theorem re-typechecked in a fresh kernel env.
    pub kernel_verified: bool,
    /// Whole closure within `FOUNDATIONAL_AXIOMS`.
    pub foundational: bool,
    /// Shard serialize -> reconstruct -> re-verify count, e.g. `"3541/3541"`.
    pub cake_round_trip: String,
    /// Count of gate violations; MUST be `0` for an ACCEPT.
    pub violations: u64,
}

/// Closure COUNTS only — the decl dumps stay in the Layer-2 `.graduation.json`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactCarried {
    /// Number of carried definitions.
    pub definitions: u64,
    /// Number of carried inductive families.
    pub inductives: u64,
    /// Number of carried supporting theorems.
    pub theorems: u64,
}

/// Provenance — the prover, the source environment, the enabling commits.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactProvenance {
    /// Prover that produced the term (interchangeable; the kernel is the anchor).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub prover: Option<String>,
    /// Toolchain + Mathlib rev the proof was built against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_env: Option<String>,
    /// Clean commits that made this graduation possible.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub enabling_commits: Vec<String>,
}

/// The content-address pin of the Layer-2 `.mathverse` shard.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactShard {
    /// `blake3:<hex>` content address (equals the gate's `result.shard_digest`).
    pub blake3: String,
    /// Uncompressed shard size in bytes.
    pub bytes: u64,
    /// Path of this shard inside the published release archive; `null` until
    /// externally released.
    pub path_in_release: Option<String>,
}

/// The pinned compact record: schema `mathverse-graduation-record-v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactRecord {
    /// Format discriminant; loaders fail-closed on mismatch.
    pub schema: String,
    /// Graduation name (matches `<name>` and the manifest).
    pub project: String,
    /// RFC-3339 UTC string for when the gate decided ACCEPT.
    pub graduated_at: String,
    /// One entry per graduated theorem (the novel front matter, not the closure).
    pub theorems: Vec<CompactTheorem>,
    /// The gate verdict.
    pub gate: CompactGate,
    /// Closure counts.
    pub carried: CompactCarried,
    /// Provenance.
    pub provenance: CompactProvenance,
    /// The Layer-2 shard pin.
    pub shard: CompactShard,
}

impl CompactRecord {
    /// Serialize to pretty JSON.
    pub fn to_pretty_json(&self) -> Result<String> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

/// Project a full `mathverse-graduation-v3.x` record + its `.mathverse` shard
/// into the compact `mathverse-graduation-record-v1` form.
///
/// SOUNDNESS: this is pure projection — it reads the gate's already-decided
/// verdict, reconstructs each statement from the shard the gate produced, and
/// recomputes only the shard's blake3 + byte length (a content check, not a
/// trust decision). It never re-runs the kernel, the gate, or any proof.
pub fn extract_compact_record(
    graduation_json: impl AsRef<Path>,
    shard: impl AsRef<Path>,
) -> Result<CompactRecord> {
    let grad_path = graduation_json.as_ref();
    let shard_path = shard.as_ref();

    let grad_bytes = std::fs::read(grad_path).map_err(|source| CompactRecordError::Io {
        path: grad_path.display().to_string(),
        source,
    })?;
    let full: serde_json::Value =
        serde_json::from_slice(&grad_bytes).map_err(|source| CompactRecordError::ParseJson {
            path: grad_path.display().to_string(),
            source,
        })?;

    let shard_bytes = std::fs::read(shard_path).map_err(|source| CompactRecordError::Io {
        path: shard_path.display().to_string(),
        source,
    })?;
    // The shard reader is a best-effort enrichment for the per-theorem
    // `statement` (reconstructed from the type arena). It is NOT trust-bearing:
    // the axiom closure, novelty, gate verdict, and counts all come from the
    // JSON, and the `shard.blake3`/`bytes` pin is computed from raw bytes below.
    // Some on-disk shards predate the current provenance-sidecar encoding and
    // fail `from_bytes` validation; in that case we still emit a faithful
    // record, marking statements `<unavailable in shard>` rather than failing
    // the whole projection. (Storage refactor: never destroy, only relocate.)
    let reader = ShardReader::from_bytes(&shard_bytes).ok();

    let grad_label = grad_path.display().to_string();
    let missing = |field: &str| CompactRecordError::MissingField {
        path: grad_label.clone(),
        field: field.to_string(),
    };

    let project = full
        .get("project")
        .and_then(|p| p.get("name"))
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| missing("project.name"))?
        .to_string();

    let decided = full
        .get("gate")
        .and_then(|g| g.get("decided_at_epoch_s"))
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| missing("gate.decided_at_epoch_s"))?;
    let graduated_at = rfc3339_utc(decided);

    // Only ACCEPTED theorems are the graduated front matter; rejected entries
    // are not part of the published claim.
    let theorems_in = full
        .get("theorems")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| missing("theorems"))?;
    let mut theorems = Vec::new();
    for thm in theorems_in {
        let accepted = thm
            .get("accepted")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(false);
        if !accepted {
            continue;
        }
        theorems.push(project_theorem(thm, reader.as_ref(), &missing)?);
    }

    let gate = project_gate(&full, theorems_in)?;
    let carried = CompactCarried {
        definitions: array_len(&full, "carried_definitions"),
        inductives: array_len(&full, "carried_inductives"),
        theorems: array_len(&full, "carried_theorems"),
    };
    let provenance = project_provenance(&full);

    let shard_digest = full
        .get("result")
        .and_then(|r| r.get("shard_digest"))
        .and_then(serde_json::Value::as_str)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| blake3_digest(&shard_bytes));

    Ok(CompactRecord {
        schema: COMPACT_RECORD_SCHEMA.to_string(),
        project,
        graduated_at,
        theorems,
        gate,
        carried,
        provenance,
        shard: CompactShard {
            blake3: shard_digest,
            bytes: shard_bytes.len() as u64,
            path_in_release: None,
        },
    })
}

/// Project one accepted theorem entry, reconstructing its statement from the
/// shard and assembling its trust-bearing axiom closure.
fn project_theorem(
    thm: &serde_json::Value,
    reader: Option<&ShardReader>,
    missing: &impl Fn(&str) -> CompactRecordError,
) -> Result<CompactTheorem> {
    let name = thm
        .get("name")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| missing("theorems[].name"))?
        .to_string();
    let novelty_digest = thm
        .get("statement_hash")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| missing("theorems[].statement_hash"))?
        .to_string();
    let novel = thm
        .get("novelty")
        .and_then(|n| n.get("verdict"))
        .and_then(serde_json::Value::as_str)
        .map(|v| v == "new")
        .unwrap_or(false);

    let foundational_only = thm
        .get("axiom_closure")
        .and_then(|a| a.get("foundational_only"))
        .and_then(serde_json::Value::as_bool)
        .unwrap_or(false);
    let mut axiom_closure: Vec<String> = thm
        .get("axiom_closure")
        .and_then(|a| a.get("domain_axioms"))
        .and_then(serde_json::Value::as_array)
        .map(|arr| {
            arr.iter()
                .filter_map(serde_json::Value::as_str)
                .map(str::to_string)
                .collect()
        })
        .unwrap_or_default();
    if foundational_only {
        for ax in CORE_FOUNDATIONAL_AXIOMS {
            if !axiom_closure.iter().any(|a| a == ax) {
                axiom_closure.push(ax.to_string());
            }
        }
    }

    let (statement, level_params) = reconstruct_statement(&name, reader);

    Ok(CompactTheorem {
        name,
        statement,
        level_params,
        axiom_closure,
        novelty_digest,
        novel,
    })
}

/// Project the gate verdict, transcribing every field verbatim.
fn project_gate(
    full: &serde_json::Value,
    theorems_in: &[serde_json::Value],
) -> Result<CompactGate> {
    // `kernel_verified` / `foundational` are the conjunction over accepted
    // theorems' own gate verdicts (the §5.1 semantics), transcribed never
    // recomputed.
    let accepted: Vec<&serde_json::Value> = theorems_in
        .iter()
        .filter(|t| {
            t.get("accepted")
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
        })
        .collect();
    let kernel_verified = !accepted.is_empty()
        && accepted.iter().all(|t| {
            t.get("kernel")
                .and_then(|k| k.get("verdict"))
                .and_then(serde_json::Value::as_str)
                == Some("kernel_verified")
        });
    let foundational = !accepted.is_empty()
        && accepted.iter().all(|t| {
            t.get("axiom_closure")
                .and_then(|a| a.get("foundational_only"))
                .and_then(serde_json::Value::as_bool)
                .unwrap_or(false)
        });
    // The cake round-trip count + violations are gate-level fields the full
    // record may carry under `gate`; when absent (older records that recorded
    // the gate self-check only on the CLI surface), default to a conservative,
    // non-asserting summary that names the carried + accepted count.
    let cake_round_trip = full
        .get("gate")
        .and_then(|g| g.get("cake_round_trip"))
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .unwrap_or_else(|| "not-recorded".to_string());
    let violations = full
        .get("gate")
        .and_then(|g| g.get("violations"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or(0);

    Ok(CompactGate {
        kernel_verified,
        foundational,
        cake_round_trip,
        violations,
    })
}

/// Project provenance from the full record + (where present) env provenance.
fn project_provenance(full: &serde_json::Value) -> CompactProvenance {
    let prov = full.get("provenance");
    let prover = prov
        .and_then(|p| p.get("engine"))
        .and_then(serde_json::Value::as_str)
        .map(str::to_string);
    let source_env = prov
        .and_then(|p| p.get("env_provenance"))
        .and_then(|e| e.get("toolchain"))
        .and_then(serde_json::Value::as_str)
        .map(str::to_string);
    CompactProvenance {
        prover,
        source_env,
        enabling_commits: Vec::new(),
    }
}

/// Reconstruct a constant's TYPE from the shard and render it; also pull its
/// universe level parameter names. Returns `("<unavailable in shard>", [])`
/// when the shard is unreadable or the constant is not present (e.g. a
/// name-only header).
fn reconstruct_statement(name: &str, reader: Option<&ShardReader>) -> (String, Vec<String>) {
    let Some(reader) = reader else {
        return ("<unavailable in shard>".to_string(), Vec::new());
    };
    let Some(header) = reader.constants.iter().find(|c| {
        reader
            .strings
            .get(c.name_idx as usize)
            .map(|s| s == name)
            .unwrap_or(false)
    }) else {
        return ("<unavailable in shard>".to_string(), Vec::new());
    };

    let level_params: Vec<String> = (0..header.level_params_count as usize)
        .filter_map(|i| {
            reader
                .strings
                .get(header.level_params_start as usize + i)
                .cloned()
        })
        .collect();

    let statement = match reconstruct_from_shard_with_level_lists(
        &reader.exprs,
        &reader.levels,
        &reader.strings,
        &reader.level_lists,
        header.type_idx,
    ) {
        Ok(type_) => format!("{type_}"),
        Err(_) => "<unavailable in shard>".to_string(),
    };

    (statement, level_params)
}

/// `len()` of a top-level array field (`0` when absent).
fn array_len(full: &serde_json::Value, field: &str) -> u64 {
    full.get(field)
        .and_then(serde_json::Value::as_array)
        .map(|a| a.len() as u64)
        .unwrap_or(0)
}

/// `blake3:<hex>` over raw bytes (matches the gate's digest convention).
fn blake3_digest(bytes: &[u8]) -> String {
    format!("blake3:{}", blake3::hash(bytes).to_hex())
}

/// Format Unix epoch seconds (UTC) as an RFC-3339 `YYYY-MM-DDTHH:MM:SSZ` string.
///
/// Dependency-free civil-from-days (Howard Hinnant's algorithm) so the record
/// writer pulls in no date crate. Valid for the entire Unix-epoch range used by
/// the gate's `decided_at_epoch_s`.
fn rfc3339_utc(epoch_secs: u64) -> String {
    let days = (epoch_secs / 86_400) as i64;
    let secs_of_day = epoch_secs % 86_400;
    let (hour, minute, second) = (
        secs_of_day / 3_600,
        (secs_of_day % 3_600) / 60,
        secs_of_day % 60,
    );

    // Civil date from days since 1970-01-01 (Hinnant). Shift epoch to an era of
    // 400 years starting 0000-03-01.
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let day = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let month = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let year = if month <= 2 { year + 1 } else { year };

    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rfc3339_utc_known_epoch_formats() {
        // 1970-01-01T00:00:00Z
        assert_eq!(rfc3339_utc(0), "1970-01-01T00:00:00Z");
        // The nat-fib graduation epoch from the design example.
        assert_eq!(rfc3339_utc(1_782_286_542), "2026-06-24T07:35:42Z");
        // A leap-year boundary: 2024-02-29T12:34:56Z.
        assert_eq!(rfc3339_utc(1_709_209_096), "2024-02-29T12:18:16Z");
    }

    #[test]
    fn test_extract_compact_record_from_fixture() {
        // Locate a real tracked graduation pair if one is still present in the
        // tree; otherwise the dedicated CLI/integration test covers it. This
        // unit test focuses on the pure projection helpers above.
        let full = serde_json::json!({
            "schema": "mathverse-graduation-v3.2",
            "gate": { "decided_at_epoch_s": 1_782_286_542u64 },
            "project": { "name": "demo-project" },
            "theorems": [
                {
                    "name": "demo_thm",
                    "statement_hash": "blake3:abcd",
                    "accepted": true,
                    "kernel": { "verdict": "kernel_verified" },
                    "axiom_closure": { "foundational_only": true, "domain_axioms": [] },
                    "novelty": { "verdict": "new" }
                },
                {
                    "name": "rejected_thm",
                    "statement_hash": "blake3:ef01",
                    "accepted": false,
                    "novelty": { "verdict": "duplicate" }
                }
            ],
            "carried_definitions": [ {"name": "a"}, {"name": "b"} ],
            "carried_inductives": [ {"name": "I"} ],
            "carried_theorems": [],
            "provenance": {
                "engine": null,
                "env_provenance": { "toolchain": "leanprover/lean4:v4.30.0" }
            },
            "result": { "shard_digest": "blake3:deadbeef" }
        });

        let missing = |field: &str| CompactRecordError::MissingField {
            path: "memory".to_string(),
            field: field.to_string(),
        };
        let theorems_in = full.get("theorems").unwrap().as_array().unwrap();
        let gate = project_gate(&full, theorems_in).expect("gate projects");
        assert!(gate.kernel_verified);
        assert!(gate.foundational);
        assert_eq!(gate.violations, 0);

        // Only the accepted theorem survives.
        let accepted: Vec<_> = theorems_in
            .iter()
            .filter(|t| t.get("accepted").and_then(|a| a.as_bool()).unwrap_or(false))
            .collect();
        assert_eq!(accepted.len(), 1);

        // Axiom closure unions in the three core foundational axioms.
        let reader = empty_reader();
        let thm = project_theorem(accepted[0], Some(&reader), &missing).expect("theorem projects");
        assert_eq!(thm.name, "demo_thm");
        assert!(thm.novel);
        assert_eq!(
            thm.axiom_closure,
            vec![
                "propext".to_string(),
                "Quot.sound".to_string(),
                "Classical.choice".to_string()
            ]
        );
        // Not in the shard -> honest unavailable marker, no panic.
        assert_eq!(thm.statement, "<unavailable in shard>");

        let carried = CompactCarried {
            definitions: array_len(&full, "carried_definitions"),
            inductives: array_len(&full, "carried_inductives"),
            theorems: array_len(&full, "carried_theorems"),
        };
        assert_eq!(carried.definitions, 2);
        assert_eq!(carried.inductives, 1);
        assert_eq!(carried.theorems, 0);

        let prov = project_provenance(&full);
        assert_eq!(prov.prover, None);
        assert_eq!(prov.source_env.as_deref(), Some("leanprover/lean4:v4.30.0"));
    }

    /// A minimal, valid empty shard reader for the projection unit test.
    fn empty_reader() -> ShardReader {
        use crate::shard::ShardWriter;
        let writer = ShardWriter::new();
        let mut bytes = Vec::new();
        writer.write(&mut bytes).expect("empty shard serializes");
        ShardReader::from_bytes(&bytes).expect("empty shard reads back")
    }
}
