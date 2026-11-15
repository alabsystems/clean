// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bounded local import-check accounting, not fresh declaration admission.
//!
//! [`typecheck_constants_full`] checks targets against an already populated,
//! immutable environment. Dependencies remain assumed; passing does not prove
//! dependency-closed admission, eliminate import trust, or change proof grade.
//! The historical field `reverified` records one local pass per exact typed
//! declaration identity, not per constant/inductive/constructor/recursor role.
//!
//! Raw counts and failures are retained. Missing or ambiguous targets,
//! conflicting role mirrors, impossible counts, and empty lanes have no numeric
//! fraction. Only valid, nonempty accounting can participate in the diagnostic
//! ratchet. A higher fraction is more local checks passing, not a soundness gate.

use crate::verify_batch_full::{local_roster::resolve_targets, typecheck_constants_full};
use clean_kernel::env::Environment;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
#[cfg(any(test, feature = "cli"))]
use std::path::Path;

/// Schema version for the persisted metric JSON.
pub const METRIC_SCHEMA_VERSION: u32 = 2;

/// Whether the raw local-check counts define a meaningful fraction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MetricState {
    /// Nonempty, internally consistent counts; still only local checking.
    ValidLocalCheckCounts,
    /// There are no resolved declarations over which to measure a fraction.
    EmptyDenominator,
    /// The raw pass count exceeds the observed declaration population.
    InvalidNumerator,
    /// Missing/ambiguous targets or inconsistent role mirrors were observed.
    InvalidTargetAccounting,
    /// Observed pass/fail counts do not partition the resolved declarations.
    InvalidCheckAccounting,
}

/// The local-check pass-fraction metric for one import lane (historically
/// named the "dep-closure re-verified fraction"; it re-derives nothing about
/// the dependency closure — see [`crate::recheck_closed::RecheckLevel`]).
///
/// Serialized to `data/import_reverification_metric.json` (well-formed JSON).
/// A numeric fraction exists only for valid nonempty local accounting.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ImportReverificationMetric {
    /// Metric schema version.
    pub schema_version: u32,
    /// The bounded lane this fraction was measured over (e.g. `"Init"` or a
    /// named shard). Purely descriptive.
    pub lane: String,
    /// Exact typed declaration identities observed in the requested lane.
    pub total_imported: usize,
    /// Raw local pass count (historical field name); never clamped.
    pub reverified: usize,
    /// `Some(reverified / total_imported)` only when accounting is valid.
    /// `None` serializes as JSON null, never an invented zero or clamped one.
    pub fraction: Option<f64>,
    /// Explicit validity of the raw counts, independently checked before use.
    pub state: MetricState,
    /// Raw failed count when actually measured; `None` for counts-only callers.
    /// This may include missing-target failures with no declaration identity.
    pub check_failed: Option<usize>,
    /// Exact errors retained from the local checker, not inferred from counts.
    pub check_errors: BTreeMap<String, String>,
    /// Exact target-resolution and role-mirror accounting errors.
    pub accounting_errors: BTreeMap<String, String>,
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
    /// Impossible counts and an empty denominator remain visible and have no
    /// fraction. Counts-only construction does not invent a failure count.
    #[must_use]
    pub fn new(
        lane: impl Into<String>,
        total_imported: usize,
        reverified: usize,
        timestamp: Option<String>,
    ) -> Self {
        let mut metric = Self {
            schema_version: METRIC_SCHEMA_VERSION,
            lane: lane.into(),
            total_imported,
            reverified,
            fraction: None,
            state: MetricState::EmptyDenominator,
            check_failed: None,
            check_errors: BTreeMap::new(),
            accounting_errors: BTreeMap::new(),
            timestamp,
            note: None,
        };
        metric.refresh_accounting();
        metric
    }

    /// Attach actually observed checker results, preserving every raw error.
    #[must_use]
    pub fn with_check_results(
        mut self,
        failed: usize,
        check_errors: BTreeMap<String, String>,
        accounting_errors: BTreeMap<String, String>,
    ) -> Self {
        self.check_failed = Some(failed);
        self.check_errors = check_errors;
        self.accounting_errors = accounting_errors;
        self.refresh_accounting();
        self
    }

    fn accounting_state(&self) -> MetricState {
        if !self.accounting_errors.is_empty() {
            MetricState::InvalidTargetAccounting
        } else if self.reverified > self.total_imported {
            MetricState::InvalidNumerator
        } else if self.check_failed.is_some_and(|failed| {
            self.reverified.checked_add(failed) != Some(self.total_imported)
                // With unambiguous coherent targets the checker retains one
                // error-map entry per failed declaration, merging role errors.
                || self.check_errors.len() != failed
        }) || (self.check_failed.is_none() && !self.check_errors.is_empty())
        {
            MetricState::InvalidCheckAccounting
        } else if self.total_imported == 0 {
            MetricState::EmptyDenominator
        } else {
            MetricState::ValidLocalCheckCounts
        }
    }

    fn refresh_accounting(&mut self) {
        self.state = self.accounting_state();
        self.fraction = if self.state == MetricState::ValidLocalCheckCounts {
            Some(self.reverified as f64 / self.total_imported as f64)
        } else {
            None
        };
    }

    /// Validate schema, raw counts, declared state, and stored fraction.
    ///
    /// Public fields and deserialized data are diagnostic claims, so consumers
    /// must not trust their cached fraction or validity label independently.
    ///
    /// # Errors
    /// Returns [`MetricError::InvalidMetric`] for absent/invalid accounting,
    /// stale schemas, or contradictory serialized fields.
    pub fn checked_fraction(&self) -> Result<f64, MetricError> {
        let invalid = |reason: String| MetricError::InvalidMetric {
            lane: self.lane.clone(),
            reason,
        };
        if self.schema_version != METRIC_SCHEMA_VERSION {
            return Err(invalid(format!(
                "schema {} is not schema {}; old clamped counts require remeasurement",
                self.schema_version, METRIC_SCHEMA_VERSION
            )));
        }
        let expected = self.accounting_state();
        if self.state != expected {
            return Err(invalid(format!(
                "declared state {:?} contradicts raw accounting {:?}",
                self.state, expected
            )));
        }
        if expected != MetricState::ValidLocalCheckCounts {
            return Err(invalid(format!("no numeric fraction for {expected:?}")));
        }
        let fraction = self.reverified as f64 / self.total_imported as f64;
        if self.fraction != Some(fraction) {
            return Err(invalid("stored fraction contradicts raw counts".to_owned()));
        }
        Ok(fraction)
    }

    /// Attach a free-form note (builder).
    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Whether `self` is a MONOTONIC regression relative to a `prior` metric for
    /// the same lane: the local-check pass fraction dropped.
    ///
    /// Comparison uses exact integer ratios, not rounded floats. A different
    /// valid lane is not comparable and returns `Ok(false)`.
    ///
    /// # Errors
    /// Either invalid measurement is refused, even when lanes differ.
    pub fn ratchet_regressed(
        &self,
        prior: &ImportReverificationMetric,
    ) -> Result<bool, MetricError> {
        self.checked_fraction()?;
        prior.checked_fraction()?;
        if self.lane != prior.lane {
            return Ok(false);
        }
        Ok((self.reverified as u128) * (prior.total_imported as u128)
            < (prior.reverified as u128) * (self.total_imported as u128))
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
    /// Only an absent prior file means there is no baseline. Unreadable,
    /// malformed, old-schema, or internally invalid prior data is not replaced.
    /// A different valid lane is not comparable, preserving the legacy policy.
    ///
    /// # Errors
    ///
    /// Returns [`MetricError`] on a ratchet regression or an I/O/serialization
    /// failure.
    #[cfg(any(test, feature = "cli"))]
    pub(crate) fn write_ratcheting(&self, path: &Path) -> Result<(), MetricError> {
        let now = self.checked_fraction()?;
        match std::fs::read(path) {
            Ok(prior_bytes) => {
                let prior = serde_json::from_slice::<ImportReverificationMetric>(&prior_bytes)
                    .map_err(MetricError::DeserializePrior)?;
                if self.ratchet_regressed(&prior)? {
                    return Err(MetricError::RatchetRegressed {
                        lane: self.lane.clone(),
                        prior: prior.checked_fraction()?,
                        now,
                    });
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(MetricError::Io(error)),
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
    /// No meaningful validated fraction exists for these raw fields.
    #[error("invalid local import-check accounting for lane `{lane}`: {reason}")]
    InvalidMetric {
        /// Descriptive lane label.
        lane: String,
        /// The exact internal inconsistency or unmeasured state.
        reason: String,
    },
    /// The new measurement regressed below the recorded baseline for its lane.
    #[error(
        "import local-check ratchet regressed for lane `{lane}`: \
         local assumed-environment pass fraction {now} < prior {prior} (it must \
         only rise; this is not a dependency-closed re-check)"
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
    #[error("serializing import local-check metric: {0}")]
    Serialize(#[source] serde_json::Error),
    /// The existing baseline is not valid current-schema metric JSON.
    #[error("reading prior import metric (old or malformed baselines require remeasurement): {0}")]
    DeserializePrior(#[source] serde_json::Error),
    /// Reading or writing the metric file failed.
    #[error("reading or writing import local-check metric: {0}")]
    Io(#[source] std::io::Error),
}

/// Compute the local-check pass-fraction metric over a bounded lane.
///
/// Runs [`typecheck_constants_full`] over `lane_names` (the lane's imported
/// constants — typically an `Init`/`Std` closure or one named shard) against
/// the immutable `env`. The denominator is the exact typed target roster,
/// including every candidate of an ambiguous display label. A missing target
/// has no invented declaration row; its explicit error invalidates the fraction.
///
/// `max_heartbeats` is a pure per-constant RESOURCE budget (`0` = unlimited);
/// exhaustion is retained as a local-check failure. All environment dependencies
/// remain assumed; this is not `add_decl`-equivalent fresh admission.
#[must_use]
pub fn compute_import_reverification_metric(
    env: &Environment,
    lane: impl Into<String>,
    lane_names: &BTreeSet<String>,
    max_heartbeats: u32,
    timestamp: Option<String>,
) -> ImportReverificationMetric {
    let roster = resolve_targets(env, lane_names);
    let (reverified, failed, errors) = typecheck_constants_full(env, lane_names, max_heartbeats);
    ImportReverificationMetric::new(lane, roster.declarations.len(), reverified, timestamp)
        .with_check_results(failed, errors, roster.accounting_errors)
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
    fn metric_review_surplus_is_retained_and_fraction_is_invalid() {
        let metric = ImportReverificationMetric::new("review", 2, 5, None);
        assert_eq!(metric.reverified, 5, "raw numerator must not be clamped");
        let json: serde_json::Value = serde_json::from_str(&metric.to_json().unwrap()).unwrap();
        assert!(
            json["fraction"].is_null(),
            "invalid accounting has no numeric fraction"
        );
    }

    #[test]
    fn metric_review_empty_denominator_has_no_fraction() {
        let metric = ImportReverificationMetric::new("review", 0, 0, None);
        let json: serde_json::Value = serde_json::from_str(&metric.to_json().unwrap()).unwrap();
        assert!(
            json["fraction"].is_null(),
            "an empty lane is unmeasured, not zero percent"
        );
    }

    #[test]
    fn metric_review_invalid_measurement_does_not_write() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("metric.json");
        let metric = ImportReverificationMetric::new("review", 2, 5, None);
        assert!(metric.write_ratcheting(&path).is_err());
        assert!(
            !path.exists(),
            "invalid metric must not establish a ratchet baseline"
        );
    }

    #[test]
    fn metric_review_malformed_prior_is_not_overwritten() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("metric.json");
        let original = b"not valid metric JSON";
        std::fs::write(&path, original).unwrap();
        let metric = ImportReverificationMetric::new("review", 2, 1, None);
        assert!(metric.write_ratcheting(&path).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), original);
    }

    #[test]
    fn metric_review_compute_retains_check_failures() {
        let mut env = Environment::default();
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            Name::from_string("bad"),
            vec![],
            Expr::bvar(0),
            None,
            Reducibility::Opaque,
            ConstantKind::Opaque,
        ));
        let metric = compute_import_reverification_metric(
            &env,
            "review",
            &BTreeSet::from(["bad".to_owned()]),
            DEFAULT_HEARTBEAT_LIMIT,
            None,
        );
        let json: serde_json::Value = serde_json::from_str(&metric.to_json().unwrap()).unwrap();
        assert_eq!(metric.total_imported, 1);
        assert_eq!(metric.reverified, 0);
        assert_eq!(json["check_failed"], 1);
        assert_eq!(json["check_errors"].as_object().map(|o| o.len()), Some(1));
    }

    #[test]
    fn test_metric_new_computes_fraction_and_retains_invalid_counts() {
        let m = ImportReverificationMetric::new("Init", 4, 3, None);
        assert_eq!(m.total_imported, 4);
        assert_eq!(m.reverified, 3);
        assert_eq!(m.fraction, Some(0.75));
        assert_eq!(m.checked_fraction().unwrap(), 0.75);
        assert_eq!(m.state, MetricState::ValidLocalCheckCounts);
        assert_eq!(m.schema_version, METRIC_SCHEMA_VERSION);
        assert!(m.timestamp.is_none());

        // Empty lane has no measurement, not an invented zero percent.
        let empty = ImportReverificationMetric::new("Init", 0, 0, None);
        assert_eq!(empty.fraction, None);
        assert_eq!(empty.state, MetricState::EmptyDenominator);

        // An impossible numerator stays visible rather than becoming 100%.
        let invalid = ImportReverificationMetric::new("Init", 2, 5, None);
        assert_eq!(invalid.reverified, 5);
        assert_eq!(invalid.fraction, None);
        assert_eq!(invalid.state, MetricState::InvalidNumerator);
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
    fn test_actual_init_ratio_and_neighbors_round_trip_and_re_ratchet_exactly() {
        // The real Init observation was 63,340 / 63,363. serde_json's default
        // approximate parser changed this fraction by one ULP on a round trip.
        // Keep the authentic ratio and its neighbors, without adding tolerance.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("metric.json");
        for passed in [63_339, 63_340, 63_341] {
            let metric = ImportReverificationMetric::new("Init", 63_363, passed, None);
            let encoded = metric.to_json().unwrap();
            let decoded: ImportReverificationMetric = serde_json::from_str(&encoded).unwrap();
            assert_eq!(decoded, metric);
            assert_eq!(
                decoded.checked_fraction().unwrap(),
                metric.checked_fraction().unwrap()
            );
            metric.write_ratcheting(&path).unwrap();
            let reread: ImportReverificationMetric =
                serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
            assert_eq!(reread, metric);
            assert!(!reread.ratchet_regressed(&metric).unwrap());
            reread.write_ratcheting(&path).unwrap();

            // A different cached value is still refused even one ULP away.
            let mut altered = decoded;
            let bits = altered.checked_fraction().unwrap().to_bits();
            altered.fraction = Some(f64::from_bits(bits + 1));
            assert!(altered.checked_fraction().is_err());
            assert!(altered.write_ratcheting(&path).is_err());
            assert_eq!(std::fs::read_to_string(&path).unwrap(), encoded);
        }
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
            !up.ratchet_regressed(&base).unwrap(),
            "rising fraction is not a regression"
        );
        assert!(
            down.ratchet_regressed(&base).unwrap(),
            "falling fraction IS a regression"
        );
        assert!(
            !same.ratchet_regressed(&base).unwrap(),
            "an unchanged fraction is not a regression"
        );
        // A different lane is not comparable.
        let other = ImportReverificationMetric::new("Std", 100, 1, None);
        assert!(!other.ratchet_regressed(&base).unwrap());
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
        // The message names the level that ran, not a closure re-check.
        let message = err.to_string();
        assert!(message.contains("local assumed-environment"), "{message}");
        assert!(
            message.contains("not a dependency-closed re-check"),
            "{message}"
        );
        assert!(
            !message.contains(&["re-verified", " fraction"].concat()),
            "{message}"
        );
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
    /// is ill-typed and does not — so valid local accounting is exactly 3/4.
    /// Adding a missing target must invalidate, not silently narrow, that lane.
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
        assert_eq!(m.checked_fraction().unwrap(), 0.75);
        assert_eq!(m.check_failed, Some(1));
        assert_eq!(m.check_errors.len(), 1);
        assert!(m.accounting_errors.is_empty());

        let mut missing_names = lane_names;
        missing_names.insert("imp.NOT_REGISTERED".to_owned());
        let missing = compute_import_reverification_metric(
            &env,
            "Imp",
            &missing_names,
            DEFAULT_HEARTBEAT_LIMIT,
            None,
        );
        assert_eq!(
            missing.total_imported, 4,
            "missing label is not an invented declaration"
        );
        assert_eq!(missing.reverified, 3, "raw local pass count is retained");
        assert_eq!(missing.check_failed, Some(2));
        assert!(!missing.accounting_errors.is_empty());
        assert_eq!(missing.fraction, None);
        assert_eq!(missing.state, MetricState::InvalidTargetAccounting);
        assert!(missing.checked_fraction().is_err());
    }

    #[test]
    fn test_invalid_current_or_prior_refuses_ratchet_even_across_lanes() {
        let valid = ImportReverificationMetric::new("Init", 1, 1, None);
        for invalid in [
            ImportReverificationMetric::new("Init", 0, 0, None),
            ImportReverificationMetric::new("Other", 2, 5, None),
        ] {
            assert!(invalid.ratchet_regressed(&valid).is_err());
            assert!(valid.ratchet_regressed(&invalid).is_err());
        }
    }

    #[test]
    fn test_ratchet_compares_integer_ratios_below_float_resolution() {
        let base = ImportReverificationMetric::new("Init", usize::MAX, usize::MAX, None);
        let lower = ImportReverificationMetric::new("Init", usize::MAX, usize::MAX - 1, None);
        assert!(lower.ratchet_regressed(&base).unwrap());
        assert!(!base.ratchet_regressed(&lower).unwrap());
    }

    #[test]
    fn test_serialized_claims_are_revalidated() {
        let original = ImportReverificationMetric::new("Init", 10, 7, None);
        for (field, replacement) in [
            ("schema_version", serde_json::json!(1)),
            ("fraction", serde_json::json!(1.0)),
            ("fraction", serde_json::Value::Null),
            ("state", serde_json::json!("empty-denominator")),
            ("reverified", serde_json::json!(11)),
            ("check_failed", serde_json::json!(4)),
            (
                "accounting_errors",
                serde_json::json!({"missing": "absent target"}),
            ),
        ] {
            let mut json = serde_json::to_value(&original).unwrap();
            json[field] = replacement;
            let mutated: ImportReverificationMetric = serde_json::from_value(json).unwrap();
            assert!(
                mutated.checked_fraction().is_err(),
                "accepted mutated {field}"
            );
        }
        let mut nan = original;
        nan.fraction = Some(f64::NAN);
        assert!(nan.checked_fraction().is_err());
    }

    #[test]
    fn test_invalid_or_old_schema_prior_is_not_replaced() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("metric.json");
        let next = ImportReverificationMetric::new("Init", 10, 9, None);
        let mut old_schema = ImportReverificationMetric::new("Init", 10, 7, None);
        old_schema.schema_version = 1;
        for prior in [
            old_schema,
            ImportReverificationMetric::new("Other", 2, 5, None),
        ] {
            let bytes = prior.to_json().unwrap();
            std::fs::write(&path, &bytes).unwrap();
            assert!(next.write_ratcheting(&path).is_err());
            assert_eq!(std::fs::read_to_string(&path).unwrap(), bytes);
        }
        assert!(
            next.write_ratcheting(dir.path()).is_err(),
            "unreadable prior is not absent"
        );
        assert!(dir.path().is_dir());
    }

    #[test]
    fn test_observed_failure_counts_must_partition_valid_targets() {
        let partial = ImportReverificationMetric::new("Init", 4, 3, None).with_check_results(
            1,
            BTreeMap::from([("bad".to_owned(), "wrong type".to_owned())]),
            BTreeMap::new(),
        );
        assert_eq!(partial.checked_fraction().unwrap(), 0.75);
        assert_eq!(partial.check_failed, Some(1));
        assert_eq!(partial.check_errors["bad"], "wrong type");
        for failed in [0, 2, usize::MAX] {
            let invalid = ImportReverificationMetric::new("Init", 4, 3, None).with_check_results(
                failed,
                BTreeMap::new(),
                BTreeMap::new(),
            );
            assert_eq!(invalid.check_failed, Some(failed));
            assert_eq!(invalid.state, MetricState::InvalidCheckAccounting);
            assert_eq!(invalid.fraction, None);
        }
        let contradictory = ImportReverificationMetric::new("Init", 4, 4, None).with_check_results(
            0,
            BTreeMap::from([("bad".to_owned(), "error".to_owned())]),
            BTreeMap::new(),
        );
        assert!(contradictory.checked_fraction().is_err());
    }

    #[test]
    fn test_dropped_or_extra_failure_messages_invalidate_consistent_counts() {
        for errors in [
            BTreeMap::new(),
            BTreeMap::from([
                ("bad".to_owned(), "wrong type".to_owned()),
                ("extra".to_owned(), "unaccounted failure".to_owned()),
            ]),
        ] {
            let metric = ImportReverificationMetric::new("Init", 4, 3, None).with_check_results(
                1,
                errors.clone(),
                BTreeMap::new(),
            );
            assert_eq!(metric.reverified, 3);
            assert_eq!(metric.check_failed, Some(1));
            assert_eq!(metric.check_errors, errors);
            assert_eq!(metric.state, MetricState::InvalidCheckAccounting);
            assert_eq!(metric.fraction, None);
            assert!(metric.checked_fraction().is_err());
        }
    }

    #[test]
    fn test_ambiguous_display_retains_both_typed_targets_without_fraction() {
        let mut env = Environment::default();
        let (type_, value) = id_ty_val();
        for name in [Name::from_string("imp.X"), Name::anon().str("imp.X")] {
            env.add_decl(Declaration::Definition {
                name,
                level_params: vec![],
                type_: type_.clone(),
                value: value.clone(),
                is_reducible: false,
            })
            .unwrap();
        }
        let metric = compute_import_reverification_metric(
            &env,
            "ambiguous",
            &BTreeSet::from(["imp.X".to_owned()]),
            DEFAULT_HEARTBEAT_LIMIT,
            None,
        );
        assert_eq!(metric.total_imported, 2);
        assert_eq!(metric.reverified, 0);
        assert_eq!(metric.check_failed, Some(2));
        assert!(!metric.accounting_errors.is_empty());
        assert_eq!(metric.state, MetricState::InvalidTargetAccounting);
        assert_eq!(metric.fraction, None);
    }

    #[test]
    fn test_only_missing_target_retains_failure_without_invented_denominator() {
        let metric = compute_import_reverification_metric(
            &Environment::default(),
            "missing",
            &BTreeSet::from(["absent".to_owned()]),
            DEFAULT_HEARTBEAT_LIMIT,
            None,
        );
        assert_eq!(
            (
                metric.total_imported,
                metric.reverified,
                metric.check_failed
            ),
            (0, 0, Some(1))
        );
        assert_eq!(metric.state, MetricState::InvalidTargetAccounting);
        assert_eq!(metric.fraction, None);
        assert!(!metric.check_errors.is_empty());
    }
}
