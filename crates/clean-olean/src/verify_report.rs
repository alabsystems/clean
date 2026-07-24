// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structured JSON verification report for the olean batch pipeline.
//!
//! Produces a comprehensive report capturing:
//! - Aggregate pass/fail counts by error category
//! - Per-module summaries with timing
//! - Heartbeat usage statistics (min/max/avg/p99)
//! - Failure details (constant name, error category, abbreviated message)
//! - Overall timing
//!
//! Used by CI systems and researchers analysing verification gaps.

use crate::verify_batch::{error_category, BatchSummary, ModuleResult};
use crate::verify_parallel::ErrorSummary;
use serde::Serialize;
use std::collections::BTreeMap;
use std::io;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

/// Schema version for forward compatibility.
const REPORT_VERSION: &str = "1.0";

/// Maximum length of an abbreviated error message in a `FailureDetail`.
const MAX_ERROR_MSG_LEN: usize = 200;

// -- Top-level report ---------------------------------------------------------

/// Comprehensive verification report emitted as JSON.
#[derive(Debug, Clone, Serialize)]
pub struct VerificationReport {
    /// Schema version string.
    pub version: String,
    /// ISO-8601 timestamp of report generation.
    pub timestamp: String,
    /// Root directory that was verified.
    pub root_dir: String,

    // -- Aggregate counts -----------------------------------------------------
    /// Total .olean files discovered on disk.
    pub total_files: usize,
    /// Number of modules actually processed (may be limited by `--limit`).
    pub modules_processed: usize,
    /// Modules that loaded successfully.
    pub modules_load_ok: usize,
    /// Modules that failed to load.
    pub modules_load_fail: usize,
    /// Total constants registered across all loaded modules.
    pub constants_total: usize,
    /// Constants that passed type-checking under [`Self::validation_mode`].
    pub types_ok: usize,
    /// Constants that failed type-checking.
    pub types_fail: usize,
    /// Constants skipped (e.g. already known).
    pub constants_skipped: usize,
    /// Pass rate as a percentage (0.0 -- 100.0).
    pub pass_rate_pct: f64,
    /// AUDIT-CRITICAL honest label: which validation mode produced `types_ok` /
    /// `types_fail` / `pass_rate_pct`.
    ///
    /// `"type-only-infer"` => only the TYPE was checked (`infer_type`,
    /// `infer_only=true`); the proof VALUE was NOT re-checked, so a pass is NOT
    /// Clean-kernel verification. `"kernel-verified-full"` => `add_decl`-
    /// equivalent (`infer_sort` on types + `check_type` on values); a pass IS a
    /// genuine Clean-kernel verification of the proof value. These two numbers
    /// must never be conflated.
    pub validation_mode: String,
    /// `true` iff `validation_mode` is the full `add_decl`-equivalent re-check
    /// (i.e. `types_ok` counts genuinely kernel-verified proof values).
    pub kernel_verified_values: bool,

    // -- Error breakdown ------------------------------------------------------
    /// Errors grouped by category with counts.
    pub error_categories: BTreeMap<String, usize>,

    // -- Failure details ------------------------------------------------------
    /// Individual failure records (all failures, not just a sample).
    pub failures: Vec<FailureDetail>,

    // -- Heartbeat / timing stats ---------------------------------------------
    /// Per-module elapsed-time statistics in milliseconds.
    pub timing_stats: TimingStats,

    // -- Per-module detail -----------------------------------------------------
    /// Per-module summary (compact form).
    pub modules: Vec<ModuleSummary>,

    // -- Overall timing -------------------------------------------------------
    /// Wall-clock seconds for the entire verification run.
    pub elapsed_secs: f64,
}

/// A single type-checking failure.
#[derive(Debug, Clone, Serialize)]
pub struct FailureDetail {
    /// Fully-qualified constant name.
    pub constant: String,
    /// Module the constant belongs to.
    pub module: String,
    /// Error category (from `error_category` classifier).
    pub category: String,
    /// Abbreviated error message (truncated to [`MAX_ERROR_MSG_LEN`] chars).
    pub message: String,
}

/// Descriptive statistics over per-module elapsed times (milliseconds).
#[derive(Debug, Clone, Serialize)]
pub struct TimingStats {
    pub count: usize,
    pub min_ms: u64,
    pub max_ms: u64,
    pub avg_ms: f64,
    pub median_ms: u64,
    pub p99_ms: u64,
    pub total_ms: u64,
}

/// Compact per-module summary for the report (omits raw error maps).
#[derive(Debug, Clone, Serialize)]
pub struct ModuleSummary {
    pub module_name: String,
    pub path: String,
    pub load_ok: bool,
    pub constants_added: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub elapsed_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub load_error: Option<String>,
}

// -- Construction -------------------------------------------------------------

/// Build a [`VerificationReport`] from a [`BatchSummary`] and optional
/// [`ErrorSummary`].
#[must_use]
pub fn build_verification_report(
    summary: &BatchSummary,
    error_summary: Option<&ErrorSummary>,
) -> VerificationReport {
    let timestamp = iso8601_now();

    // Collect all failures across modules.
    let mut failures = Vec::new();
    for module in &summary.modules {
        for (constant, err_msg) in &module.tc_errors {
            failures.push(FailureDetail {
                constant: constant.clone(),
                module: module.module_name.clone(),
                category: error_category(err_msg),
                message: abbreviate(err_msg, MAX_ERROR_MSG_LEN),
            });
        }
    }

    // Per-module timing stats.
    let timing_stats = compute_timing_stats(&summary.modules);

    // Compact module summaries.
    let modules: Vec<ModuleSummary> = summary
        .modules
        .iter()
        .map(|m| ModuleSummary {
            module_name: m.module_name.clone(),
            path: m.path.clone(),
            load_ok: m.load_ok,
            constants_added: m.constants_added,
            tc_pass: m.tc_pass,
            tc_fail: m.tc_fail,
            elapsed_ms: m.elapsed_ms,
            load_error: m.load_error.clone(),
        })
        .collect();

    // Error categories: prefer the ErrorSummary if available (it has
    // per-category counts from TC errors only), otherwise fall back to
    // the BatchSummary error_categories which includes load errors.
    let error_categories = if let Some(es) = error_summary {
        es.by_category
            .iter()
            .map(|(cat, detail)| (cat.clone(), detail.count))
            .collect()
    } else {
        summary.error_categories.clone()
    };

    VerificationReport {
        version: REPORT_VERSION.to_string(),
        timestamp,
        root_dir: summary.root_dir.clone(),
        total_files: summary.total_files,
        modules_processed: summary.processed_files,
        modules_load_ok: summary.load_success,
        modules_load_fail: summary.load_failure,
        constants_total: summary.total_constants,
        types_ok: summary.tc_pass,
        types_fail: summary.tc_fail,
        constants_skipped: summary.total_skipped,
        pass_rate_pct: summary.pass_rate_pct,
        validation_mode: summary.validation_label.clone(),
        kernel_verified_values: summary.validation_mode.is_kernel_verified(),
        error_categories,
        failures,
        timing_stats,
        modules,
        elapsed_secs: summary.total_elapsed_secs,
    }
}

// -- File output --------------------------------------------------------------

/// Serialize the report to JSON and write it to the given path.
///
/// Creates parent directories if they do not exist.
pub fn write_report_to_file(report: &VerificationReport, path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let json = serde_json::to_string_pretty(report)
        .map_err(|e| io::Error::other(format!("json serialize: {e}")))?;
    std::fs::write(path, json)
}

// -- Helpers ------------------------------------------------------------------

/// Truncate a string to at most `max` characters, appending "..." if truncated.
pub(crate) fn abbreviate(s: &str, max: usize) -> String {
    if s.len() <= max {
        s.to_string()
    } else {
        let mut truncated: String = s.chars().take(max.saturating_sub(3)).collect();
        truncated.push_str("...");
        truncated
    }
}

/// Produce an ISO-8601 timestamp from the current system time.
///
/// Format: "YYYY-MM-DDTHH:MM:SSZ" (UTC, no fractional seconds).
fn iso8601_now() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    format_epoch_as_iso8601(secs)
}

/// Convert epoch seconds to ISO-8601 UTC string.
pub(crate) fn format_epoch_as_iso8601(epoch_secs: u64) -> String {
    // Manual UTC breakdown avoids pulling in `chrono`.
    let s = epoch_secs;
    let secs_per_day: u64 = 86400;
    let days = s / secs_per_day;
    let day_secs = s % secs_per_day;
    let hours = day_secs / 3600;
    let minutes = (day_secs % 3600) / 60;
    let seconds = day_secs % 60;

    // Days since 1970-01-01 -> (year, month, day) using the civil-from-days
    // algorithm (Howard Hinnant, public domain).
    let (year, month, day) = civil_from_days(days as i64);

    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

/// Convert days since Unix epoch to (year, month, day).
///
/// Adapted from Howard Hinnant's `civil_from_days` algorithm.
fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u32;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d)
}

/// Compute descriptive timing statistics over module elapsed times.
pub(crate) fn compute_timing_stats(modules: &[ModuleResult]) -> TimingStats {
    if modules.is_empty() {
        return TimingStats {
            count: 0,
            min_ms: 0,
            max_ms: 0,
            avg_ms: 0.0,
            median_ms: 0,
            p99_ms: 0,
            total_ms: 0,
        };
    }

    let mut times: Vec<u64> = modules.iter().map(|m| m.elapsed_ms).collect();
    times.sort_unstable();

    let count = times.len();
    let total: u64 = times.iter().sum();
    let min_ms = times[0];
    let max_ms = times[count - 1];
    let avg_ms = total as f64 / count as f64;
    let median_ms = times[count / 2];
    let p99_idx = ((count as f64 * 0.99).ceil() as usize).min(count) - 1;
    let p99_ms = times[p99_idx];

    TimingStats {
        count,
        min_ms,
        max_ms,
        avg_ms,
        median_ms,
        p99_ms,
        total_ms: total,
    }
}
