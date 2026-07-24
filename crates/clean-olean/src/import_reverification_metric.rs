// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dep-closure re-verified-fraction metric (Pillar-2 item 5).
//!
//! # What this measures
//!
//! The shared base environment holds `.olean`-imported dependency TYPES/values
//! that were registered STRUCTURALLY (`extend_constants_structural`) —
//! admitted WITHOUT a Clean-kernel type-check and stored `Unverified`
//! (`needs_recheck == true`). That is an honest residual TCB. This module turns
//! that residual into a MEASURED, monotonically-ratcheting-UP number: over a
//! bounded lane (e.g. the `Init` bootstrap closure or a named shard's
//! dependency closure), it runs the kernel's `add_decl`-equivalent re-check
//! ([`typecheck_constants_full`]) and records the fraction of imported
//! constants the Clean kernel genuinely re-verified.
//!
//! The point is measurability + ratchet, not a soundness gate: the number
//! going UP means the import-trust residual is SHRINKING. It should only ever
//! rise (a regression that drops it is a real signal), which
//! [`ImportReverificationMetric::ratchet_regressed`] detects.
//!
//! # SOUNDNESS
//!
//! [`typecheck_constants_full`] runs against an immutable `&Environment`, so it
//! can only ADD verification knowledge — it never mutates the env, never admits
//! a false proof (an ill-typed constant fails on its own merits), and never
//! changes any other constant's verdict. `reverified` counts exactly the
//! constants that PASSED that re-check; the metric is therefore an honest lower
//! bound on genuinely-kernel-verified imports for the lane.
//!
//! # Boundedness
//!
//! Measurement is over a TRACTABLE lane only (the caller supplies the target
//! name set — typically an `Init`/`Std` closure or one named shard), NOT the
//! Mathverse millions. The Mathverse corpus stays on the structural import path
//! by design (re-checking it is a separate performance effort).

use crate::verify_batch_full::typecheck_constants_full;
use clean_kernel::env::Environment;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::Path;

/// Schema version for the persisted metric JSON.
pub const METRIC_SCHEMA_VERSION: u32 = 1;

/// The dep-closure re-verified-fraction metric for one import lane.
///
/// Serialized to `data/import_reverification_metric.json` (well-formed JSON).
/// `fraction == reverified / total_imported` (0.0 when the lane is empty).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ImportReverificationMetric {
    /// Metric schema version.
    pub schema_version: u32,
    /// The bounded lane this fraction was measured over (e.g. `"Init"` or a
    /// named shard). Purely descriptive.
    pub lane: String,
    /// Total imported constants considered in the lane (the denominator).
    pub total_imported: usize,
    /// Constants the Clean kernel genuinely RE-VERIFIED via the
    /// `add_decl`-equivalent re-check (the numerator).
    pub reverified: usize,
    /// `reverified / total_imported` in `[0.0, 1.0]` (0.0 when the lane is
    /// empty). This is the number the ratchet drives UP over time.
    pub fraction: f64,
    /// Optional creation timestamp. Omitted from the JSON when `None` so a
    /// deterministic (timestamp-free) metric can be produced for reproducible
    /// tooling; set from a caller-supplied value when a timestamp is wanted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<String>,
    /// Optional free-form note (e.g. explaining an unmeasured `0/0` baseline).
    /// Omitted from the JSON when `None`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

impl ImportReverificationMetric {
    /// Build a metric from raw counts, computing `fraction` consistently.
    ///
    /// `reverified` is clamped to `total_imported` (a re-check can never verify
    /// MORE constants than the lane contains), keeping `fraction <= 1.0`.
    #[must_use]
    pub fn new(
        lane: impl Into<String>,
        total_imported: usize,
        reverified: usize,
        timestamp: Option<String>,
    ) -> Self {
        let reverified = reverified.min(total_imported);
        let fraction = if total_imported == 0 {
            0.0
        } else {
            reverified as f64 / total_imported as f64
        };
        Self {
            schema_version: METRIC_SCHEMA_VERSION,
            lane: lane.into(),
            total_imported,
            reverified,
            fraction,
            timestamp,
            note: None,
        }
    }

    /// Attach a free-form note (builder).
    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Whether `self` is a MONOTONIC regression relative to a `prior` metric for
    /// the same lane: the re-verified fraction dropped.
    ///
    /// This is the ratchet check: the fraction should only ever RISE. Returns
    /// `true` when `self.fraction` is strictly below `prior.fraction` (by more
    /// than a tiny float epsilon, so an exactly-equal re-measurement is NOT a
    /// regression). A different `lane` is not comparable and returns `false`.
    #[must_use]
    pub fn ratchet_regressed(&self, prior: &ImportReverificationMetric) -> bool {
        if self.lane != prior.lane {
            return false;
        }
        // Small epsilon so float re-computation noise on an unchanged lane does
        // not spuriously trip the ratchet.
        const EPS: f64 = 1e-9;
        self.fraction + EPS < prior.fraction
    }

    /// Serialize to pretty JSON.
    ///
    /// # Errors
    ///
    /// Returns [`serde_json::Error`] if serialization fails (should not happen
    /// for this plain-data struct).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Write the metric as pretty JSON to `path`, honoring the ratchet: if a
    /// prior metric for the SAME lane already exists at `path` and this
    /// measurement REGRESSED (fraction dropped), the file is NOT overwritten and
    /// an error is returned instead — the ratchet only goes up.
    ///
    /// A prior file for a DIFFERENT lane (or an unreadable/absent file) is
    /// treated as "no comparable baseline" and the write proceeds.
    ///
    /// # Errors
    ///
    /// Returns [`MetricError`] on a ratchet regression or an I/O/serialization
    /// failure.
    pub fn write_ratcheting(&self, path: &Path) -> Result<(), MetricError> {
        if let Ok(prior_bytes) = std::fs::read(path) {
            if let Ok(prior) = serde_json::from_slice::<ImportReverificationMetric>(&prior_bytes) {
                if self.ratchet_regressed(&prior) {
                    return Err(MetricError::RatchetRegressed {
                        lane: self.lane.clone(),
                        prior: prior.fraction,
                        now: self.fraction,
                    });
                }
            }
        }
        let json = self.to_json().map_err(MetricError::Serialize)?;
        std::fs::write(path, json).map_err(MetricError::Io)?;
        Ok(())
    }
}

/// Errors from writing/ratcheting the import-reverification metric.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum MetricError {
    /// The new measurement regressed below the recorded baseline for its lane.
    #[error(
        "import re-verification ratchet regressed for lane `{lane}`: \
         fraction {now} < prior {prior} (the re-verified fraction must only rise)"
    )]
    RatchetRegressed {
        /// The lane whose fraction regressed.
        lane: String,
        /// The prior recorded fraction.
        prior: f64,
        /// The regressed new fraction.
        now: f64,
    },
    /// JSON serialization failed.
    #[error("serializing import re-verification metric: {0}")]
    Serialize(#[source] serde_json::Error),
    /// Writing the metric file failed.
    #[error("writing import re-verification metric: {0}")]
    Io(#[source] std::io::Error),
}

/// Compute the dep-closure re-verified-fraction metric over a bounded lane.
///
/// Runs [`typecheck_constants_full`] over `lane_names` (the lane's imported
/// constants — typically an `Init`/`Std` closure or one named shard) against
/// the immutable `env`, then reports `reverified / total` where `total` is the
/// number of lane names actually present in `env` and `reverified` is the
/// passing count.
///
/// `max_heartbeats` is a pure per-constant RESOURCE budget (`0` = unlimited);
/// on exhaustion the kernel conservatively rejects, so it can never inflate the
/// re-verified count — it only lets valid-but-slow constants complete.
///
/// SOUNDNESS: read-only over `env`; the returned fraction is an honest lower
/// bound on genuinely-kernel-verified imports for the lane (see module docs).
#[must_use]
pub fn compute_import_reverification_metric(
    env: &Environment,
    lane: impl Into<String>,
    lane_names: &BTreeSet<String>,
    max_heartbeats: u32,
    timestamp: Option<String>,
) -> ImportReverificationMetric {
    // Denominator: only names actually registered in this env are "imported".
    let total = lane_names
        .iter()
        .filter(|n| name_is_registered(env, n))
        .count();
    // Numerator: the kernel add_decl-equivalent re-check pass count.
    let (reverified, _fail, _errors) = typecheck_constants_full(env, lane_names, max_heartbeats);
    ImportReverificationMetric::new(lane, total, reverified, timestamp)
}

/// Whether `name` names a registered declaration (constant/inductive/
/// constructor/recursor) in `env` — the exact set `typecheck_constants_full`
/// iterates.
fn name_is_registered(env: &Environment, name: &str) -> bool {
    let kname = clean_kernel::name::Name::from_string(name);
    env.get_const(&kname).is_some()
        || env.get_inductive(&kname).is_some()
        || env.get_constructor(&kname).is_some()
        || env.get_recursor(&kname).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::{
        ConstantInfo, ConstantKind, ConstantOrigin, Declaration, Reducibility,
    };
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;
    use clean_kernel::name::Name;
    use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;

    fn id_ty_val() -> (Expr, Expr) {
        let id_ty = Expr::pi(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let id_val = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        (id_ty, id_val)
    }

    #[test]
    fn test_metric_new_computes_fraction_and_clamps() {
        let m = ImportReverificationMetric::new("Init", 4, 3, None);
        assert_eq!(m.total_imported, 4);
        assert_eq!(m.reverified, 3);
        assert!((m.fraction - 0.75).abs() < 1e-12);
        assert_eq!(m.schema_version, METRIC_SCHEMA_VERSION);
        assert!(m.timestamp.is_none());

        // Empty lane => fraction 0.0, never NaN.
        let empty = ImportReverificationMetric::new("Init", 0, 0, None);
        assert_eq!(empty.fraction, 0.0);

        // reverified is clamped to total (can never exceed the denominator).
        let clamped = ImportReverificationMetric::new("Init", 2, 5, None);
        assert_eq!(clamped.reverified, 2);
        assert!((clamped.fraction - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_metric_json_is_well_formed_and_round_trips() {
        let m = ImportReverificationMetric::new("Init", 10, 7, Some("2026-07-01".into()));
        let json = m.to_json().expect("serialize");
        // Well-formed + contains the load-bearing fields.
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("valid JSON");
        assert_eq!(parsed["total_imported"], 10);
        assert_eq!(parsed["reverified"], 7);
        assert_eq!(parsed["lane"], "Init");
        assert!((parsed["fraction"].as_f64().unwrap() - 0.7).abs() < 1e-12);
        assert_eq!(parsed["timestamp"], "2026-07-01");
        // Round-trips back to an equal struct.
        let back: ImportReverificationMetric = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(back, m);
    }

    #[test]
    fn test_timestamp_omitted_when_none() {
        let m = ImportReverificationMetric::new("Init", 1, 1, None);
        let json = m.to_json().expect("serialize");
        assert!(
            !json.contains("timestamp"),
            "None timestamp must be omitted from the JSON: {json}"
        );
    }

    #[test]
    fn test_ratchet_regression_detection() {
        let base = ImportReverificationMetric::new("Init", 100, 50, None); // 0.50
        let up = ImportReverificationMetric::new("Init", 100, 60, None); // 0.60
        let down = ImportReverificationMetric::new("Init", 100, 40, None); // 0.40
        let same = ImportReverificationMetric::new("Init", 100, 50, None); // 0.50

        assert!(
            !up.ratchet_regressed(&base),
            "rising fraction is not a regression"
        );
        assert!(
            down.ratchet_regressed(&base),
            "falling fraction IS a regression"
        );
        assert!(
            !same.ratchet_regressed(&base),
            "an unchanged fraction is not a regression"
        );
        // A different lane is not comparable.
        let other = ImportReverificationMetric::new("Std", 100, 1, None);
        assert!(!other.ratchet_regressed(&base));
    }

    #[test]
    fn test_write_ratcheting_refuses_regression_but_allows_rise() {
        let dir = std::env::temp_dir().join(format!(
            "clean-reverify-metric-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        std::fs::create_dir_all(&dir).expect("mk tmp");
        let path = dir.join("import_reverification_metric.json");

        // First write establishes the baseline.
        let base = ImportReverificationMetric::new("Init", 100, 50, None);
        base.write_ratcheting(&path).expect("first write");
        // A regression is REFUSED (ratchet only goes up) and does not overwrite.
        let down = ImportReverificationMetric::new("Init", 100, 40, None);
        let err = down
            .write_ratcheting(&path)
            .expect_err("regression must be refused");
        assert!(matches!(err, MetricError::RatchetRegressed { .. }));
        // The on-disk value is still the baseline.
        let on_disk: ImportReverificationMetric =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(on_disk.reverified, 50);
        // A rise is accepted and overwrites.
        let up = ImportReverificationMetric::new("Init", 100, 70, None);
        up.write_ratcheting(&path).expect("rise write");
        let on_disk2: ImportReverificationMetric =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(on_disk2.reverified, 70);

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// CORE (no toolchain): compute the metric over an in-memory lane of
    /// STRUCTURALLY-imported constants. Three are well-typed and re-verify; one
    /// is ill-typed and does not — so the fraction is exactly 3/4, and the
    /// denominator counts only registered lane names.
    #[test]
    fn test_compute_metric_over_in_memory_lane() {
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let (id_ty, id_val) = id_ty_val();

        for n in ["imp.A", "imp.B", "imp.C"] {
            env.add_decl(Declaration::Definition {
                name: Name::from_string(n),
                level_params: vec![],
                type_: id_ty.clone(),
                value: id_val.clone(),
                is_reducible: false,
            })
            .expect("well-typed import registers");
            env.set_constant_origin(
                Name::from_string(n),
                ConstantOrigin::olean_import(Some("Imp".into())),
            );
        }
        // One ill-typed structural import (value is a function; stated type Prop).
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            Name::from_string("imp.BAD"),
            vec![],
            Expr::sort(Level::zero()),
            Some(id_val),
            Reducibility::Opaque,
            ConstantKind::Opaque,
        ));
        env.set_constant_origin(
            Name::from_string("imp.BAD"),
            ConstantOrigin::olean_import(Some("Imp".into())),
        );

        let lane_names: BTreeSet<String> = ["imp.A", "imp.B", "imp.C", "imp.BAD"]
            .into_iter()
            .map(str::to_string)
            // A name NOT in the env must not inflate the denominator.
            .chain(std::iter::once("imp.NOT_REGISTERED".to_string()))
            .collect();

        let m = compute_import_reverification_metric(
            &env,
            "Imp",
            &lane_names,
            DEFAULT_HEARTBEAT_LIMIT,
            None,
        );
        assert_eq!(m.total_imported, 4, "unregistered name must not count");
        assert_eq!(m.reverified, 3, "the ill-typed import must not re-verify");
        assert!((m.fraction - 0.75).abs() < 1e-12);
    }
}
