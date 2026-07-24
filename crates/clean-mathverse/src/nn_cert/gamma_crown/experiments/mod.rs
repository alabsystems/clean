// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! gamma-crown Phase 1 experiment artifact parser (mail #3505).
//!
//! Phase 1 of the gamma-crown response to clean#3433 ships 13 machine-readable
//! JSON artifacts under `gamma-crown/reports/experiments/C00{2,4}/`. Each file
//! describes a single experiment with configurations, per-dim results, and an
//! aggregate summary. Fix commit on gamma-crown main: `883c37149`.
//!
//! This module defines the authoritative clean-side schema for those artifacts
//! so downstream formalization (T20-T22 for C002, T40-T42 for C004) can cite a
//! stable, parsed representation instead of ad-hoc JSON dives.
//!
//! ## Schema
//!
//! Every Phase 1 artifact has the shape:
//!
//! ```json
//! {
//!   "conjecture": "C002" | "C004",
//!   "experiment": "<slug>",
//!   "hypothesis": "<prose>",
//!   "configurations": [{"hidden": u32, "epsilon": f64, "seed": u64}, ...],
//!   "results": [<per-dim record, shape varies by conjecture>],
//!   "summary": {
//!     "mean_ratio": f64,
//!     "min_ratio": f64,
//!     "max_ratio": f64,
//!     "finding": "<prose>"
//!   }
//! }
//! ```
//!
//! C002 per-dim records carry `cross_width`, `perblock_width`, `ratio_pb_cb`.
//! C004 per-dim records carry `crown_width`, `ibp_width`, `ratio_crown_ibp`.
//! We parse both into a single [`ExperimentResult`] enum so Phase 2 ingestion
//! can walk a uniform structure.
//!
//! ## Regression guards
//!
//! - C004 primary: gamma-crown hard-asserts `ratio >= 0.99` across all dims.
//!   [`C004Summary::assert_degeneracy_threshold`] mirrors that guard on the
//!   clean side so our ingestion flags upstream drift.
//! - C002 primary: the empirical gap is 3-100x tighter per-block; the
//!   formalization only needs the "no worse than" direction, which corresponds
//!   to `max_ratio <= 1.0 + slack`. [`C002Summary::assert_firewall_direction`]
//!   enforces that weaker invariant.

use serde::Deserialize;

use crate::error::{MathverseError, MathverseResult};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Which gamma-crown conjecture a Phase 1 artifact documents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Conjecture {
    /// C002 — LayerNorm correlation firewall (per-block vs cross-block).
    C002,
    /// C004 — CROWN backward through LayerNorm degenerates to IBP.
    C004,
}

/// One `{hidden, epsilon, seed}` configuration row from a Phase 1 artifact.
#[derive(Debug, Clone, PartialEq)]
pub struct ExperimentConfig {
    pub hidden: u32,
    pub epsilon: f64,
    pub seed: u64,
}

/// Per-dim result record, specialised by conjecture.
#[derive(Debug, Clone, PartialEq)]
pub enum ExperimentResult {
    /// C002: `(hidden, epsilon, dim, cross_width, perblock_width, ratio_pb_cb)`
    C002 {
        hidden: u32,
        epsilon: f64,
        dim: u32,
        cross_width: f64,
        perblock_width: f64,
        ratio_pb_cb: f64,
    },
    /// C004: `(hidden, epsilon, dim, crown_width, ibp_width, ratio_crown_ibp)`
    C004 {
        hidden: u32,
        epsilon: f64,
        dim: u32,
        crown_width: f64,
        ibp_width: f64,
        ratio_crown_ibp: f64,
    },
}

/// Shared `summary` block for C002 artifacts.
#[derive(Debug, Clone, PartialEq)]
pub struct C002Summary {
    pub mean_ratio: f64,
    pub min_ratio: f64,
    pub max_ratio: f64,
    pub finding: String,
}

impl C002Summary {
    /// Assert the firewall direction (per-block no worse than cross-block).
    ///
    /// This is the formalization target for T20-T22: we only prove
    /// `perblock <= cross` up to numerical slack. `slack` is added to the
    /// pure-1.0 threshold to tolerate float rounding on the upstream side.
    pub fn assert_firewall_direction(&self, slack: f64) -> Result<(), String> {
        debug_assert!(slack >= 0.0, "slack must be non-negative");
        if self.max_ratio > 1.0 + slack {
            return Err(format!(
                "C002 firewall violated: max_ratio={} exceeds 1.0 + slack={}",
                self.max_ratio,
                1.0 + slack
            ));
        }
        Ok(())
    }
}

/// Shared `summary` block for C004 artifacts.
#[derive(Debug, Clone, PartialEq)]
pub struct C004Summary {
    pub mean_ratio: f64,
    pub min_ratio: f64,
    pub max_ratio: f64,
    pub finding: String,
}

impl C004Summary {
    /// Assert the degeneracy threshold used by gamma-crown's primary guard.
    ///
    /// gamma-crown `reports/experiments/C004/primary.json` hard-asserts
    /// `ratio >= 0.99` across all dims (per mail #3505). Mirror that guard
    /// here so ingestion rejects artifacts that drift out of the published
    /// regression window.
    pub fn assert_degeneracy_threshold(&self, threshold: f64) -> Result<(), String> {
        debug_assert!(
            (0.0..=1.0).contains(&threshold),
            "threshold must be in [0,1]"
        );
        if self.min_ratio < threshold {
            return Err(format!(
                "C004 degeneracy threshold violated: min_ratio={} below threshold={}",
                self.min_ratio, threshold
            ));
        }
        Ok(())
    }
}

/// Parsed Phase 1 artifact, discriminated by conjecture.
#[derive(Debug, Clone, PartialEq)]
pub enum Phase1Artifact {
    C002 {
        experiment: String,
        hypothesis: String,
        configurations: Vec<ExperimentConfig>,
        results: Vec<ExperimentResult>,
        summary: C002Summary,
    },
    C004 {
        experiment: String,
        hypothesis: String,
        configurations: Vec<ExperimentConfig>,
        results: Vec<ExperimentResult>,
        summary: C004Summary,
    },
}

impl Phase1Artifact {
    pub fn conjecture(&self) -> Conjecture {
        match self {
            Self::C002 { .. } => Conjecture::C002,
            Self::C004 { .. } => Conjecture::C004,
        }
    }

    pub fn experiment(&self) -> &str {
        match self {
            Self::C002 { experiment, .. } | Self::C004 { experiment, .. } => experiment,
        }
    }

    pub fn results(&self) -> &[ExperimentResult] {
        match self {
            Self::C002 { results, .. } | Self::C004 { results, .. } => results,
        }
    }

    pub fn configurations(&self) -> &[ExperimentConfig] {
        match self {
            Self::C002 { configurations, .. } | Self::C004 { configurations, .. } => configurations,
        }
    }
}

// ---------------------------------------------------------------------------
// Raw (serde) schema — mirrors gamma-crown's JSON exactly.
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct RawArtifact {
    conjecture: String,
    experiment: String,
    #[serde(default)]
    hypothesis: Option<String>,
    #[serde(default)]
    configurations: Vec<RawConfig>,
    #[serde(default)]
    results: Vec<serde_json::Value>,
    summary: RawSummary,
}

#[derive(Deserialize)]
struct RawConfig {
    hidden: u32,
    epsilon: f64,
    #[serde(default)]
    seed: u64,
}

#[derive(Deserialize)]
struct RawSummary {
    mean_ratio: f64,
    min_ratio: f64,
    max_ratio: f64,
    #[serde(default)]
    finding: String,
}

#[derive(Deserialize)]
struct RawC002Row {
    hidden: u32,
    epsilon: f64,
    dim: u32,
    cross_width: f64,
    perblock_width: f64,
    ratio_pb_cb: f64,
}

#[derive(Deserialize)]
struct RawC004Row {
    hidden: u32,
    epsilon: f64,
    dim: u32,
    crown_width: f64,
    ibp_width: f64,
    ratio_crown_ibp: f64,
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Parse a Phase 1 artifact (C002 or C004) from JSON.
///
/// # Errors
///
/// * `MathverseError::Json` on malformed JSON.
/// * `MathverseError::ImportFailed` if the `conjecture` field is not `C002` or
///   `C004`, or if any per-dim result row is missing fields required for that
///   conjecture.
pub fn parse_phase1_artifact(json: &str) -> MathverseResult<Phase1Artifact> {
    let raw: RawArtifact = serde_json::from_str(json).map_err(MathverseError::Json)?;

    let configurations = raw
        .configurations
        .into_iter()
        .map(|c| ExperimentConfig {
            hidden: c.hidden,
            epsilon: c.epsilon,
            seed: c.seed,
        })
        .collect();

    match raw.conjecture.as_str() {
        "C002" => Ok(Phase1Artifact::C002 {
            experiment: raw.experiment,
            hypothesis: raw.hypothesis.unwrap_or_default(),
            configurations,
            results: parse_c002_rows(&raw.results)?,
            summary: C002Summary {
                mean_ratio: raw.summary.mean_ratio,
                min_ratio: raw.summary.min_ratio,
                max_ratio: raw.summary.max_ratio,
                finding: raw.summary.finding,
            },
        }),
        "C004" => Ok(Phase1Artifact::C004 {
            experiment: raw.experiment,
            hypothesis: raw.hypothesis.unwrap_or_default(),
            configurations,
            results: parse_c004_rows(&raw.results)?,
            summary: C004Summary {
                mean_ratio: raw.summary.mean_ratio,
                min_ratio: raw.summary.min_ratio,
                max_ratio: raw.summary.max_ratio,
                finding: raw.summary.finding,
            },
        }),
        other => Err(MathverseError::ImportFailed {
            system: "gamma-crown/phase1".to_string(),
            reason: format!("unsupported conjecture `{other}`: Phase 1 only ships C002 and C004"),
        }),
    }
}

fn parse_c002_rows(rows: &[serde_json::Value]) -> MathverseResult<Vec<ExperimentResult>> {
    rows.iter()
        .enumerate()
        .map(|(idx, v)| {
            let row: RawC002Row =
                serde_json::from_value(v.clone()).map_err(|e| MathverseError::ImportFailed {
                    system: "gamma-crown/phase1".to_string(),
                    reason: format!("C002 row {idx}: {e}"),
                })?;
            Ok(ExperimentResult::C002 {
                hidden: row.hidden,
                epsilon: row.epsilon,
                dim: row.dim,
                cross_width: row.cross_width,
                perblock_width: row.perblock_width,
                ratio_pb_cb: row.ratio_pb_cb,
            })
        })
        .collect()
}

fn parse_c004_rows(rows: &[serde_json::Value]) -> MathverseResult<Vec<ExperimentResult>> {
    rows.iter()
        .enumerate()
        .map(|(idx, v)| {
            let row: RawC004Row =
                serde_json::from_value(v.clone()).map_err(|e| MathverseError::ImportFailed {
                    system: "gamma-crown/phase1".to_string(),
                    reason: format!("C004 row {idx}: {e}"),
                })?;
            Ok(ExperimentResult::C004 {
                hidden: row.hidden,
                epsilon: row.epsilon,
                dim: row.dim,
                crown_width: row.crown_width,
                ibp_width: row.ibp_width,
                ratio_crown_ibp: row.ratio_crown_ibp,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests;
