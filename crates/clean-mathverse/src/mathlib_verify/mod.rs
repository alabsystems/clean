// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathlib `.olean` verification pipeline.
//!
//! Extends the Lean 4 stdlib verify-olean pipeline to Mathlib's ~7,873 `.olean`
//! files. Discovers files, groups by module hierarchy, processes each through
//! the kernel TypeChecker, and produces a structured JSON report.
//!
//! Uses the existing `clean-olean` verify_batch infrastructure for per-module
//! loading, dependency ordering, and type-checking.

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use clean_kernel::env::Environment;
use clean_olean::default_search_paths;
use clean_olean::verify_batch::{
    build_dependency_order, build_summary, collect_new_env_names, discover_olean_files,
    preload_init_if_needed, relative_display, verify_one_module, BatchSummary, ModuleResult,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tracing::info;

#[cfg(test)]
mod tests;

// ════════════════════════════════════════════════════════════════════════════
// Error types
// ════════════════════════════════════════════════════════════════════════════

/// Error categories for Mathlib verification failures.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MathLibErrorKind {
    /// Failed to load/parse the .olean file.
    OleanLoadFailed,
    /// Kernel type-check failure on one or more constants.
    TypeCheckFailed,
    /// Heartbeat limit exceeded during verification.
    HeartbeatExceeded,
    /// Stack overflow during deep term processing.
    StackOverflow,
    /// Failed to write output shard.
    ShardWriteFailed,
}

impl std::fmt::Display for MathLibErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OleanLoadFailed => write!(f, "olean_load_failed"),
            Self::TypeCheckFailed => write!(f, "type_check_failed"),
            Self::HeartbeatExceeded => write!(f, "heartbeat_exceeded"),
            Self::StackOverflow => write!(f, "stack_overflow"),
            Self::ShardWriteFailed => write!(f, "shard_write_failed"),
        }
    }
}

/// Classify an error string into a `MathLibErrorKind`.
#[must_use]
pub fn classify_error(error_msg: &str) -> MathLibErrorKind {
    let lower = error_msg.to_lowercase();
    if lower.contains("heartbeat") || lower.contains("deterministic timeout") {
        MathLibErrorKind::HeartbeatExceeded
    } else if lower.contains("stack overflow")
        || lower.contains("stack_overflow")
        || lower.contains("overflowed its stack")
    {
        MathLibErrorKind::StackOverflow
    } else if lower.contains("shard") || lower.contains("write failed") {
        MathLibErrorKind::ShardWriteFailed
    } else if lower.contains("load") || lower.contains("parse") || lower.contains("olean") {
        MathLibErrorKind::OleanLoadFailed
    } else {
        MathLibErrorKind::TypeCheckFailed
    }
}

#[derive(Debug, Error)]
pub enum MathLibVerifyError {
    #[error("mathlib path does not exist: {0}")]
    PathNotFound(PathBuf),

    #[error("no .olean files found under {0}")]
    NoOleanFiles(PathBuf),

    #[error("io: {0}")]
    Io(#[from] std::io::Error),

    #[error("json: {0}")]
    Json(#[from] serde_json::Error),
}

pub type MathLibVerifyResult<T> = Result<T, MathLibVerifyError>;

// ════════════════════════════════════════════════════════════════════════════
// Configuration
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for Mathlib verification runs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MathLibVerifyConfig {
    /// Root directory containing Mathlib .olean files.
    pub mathlib_path: PathBuf,
    /// Number of modules to process before emitting a progress line.
    pub progress_interval: usize,
    /// Maximum stack size in bytes for deep-term processing (0 = default).
    pub stack_size_bytes: usize,
    /// Heartbeat limit per module (0 = unlimited).
    pub heartbeat_limit: u64,
    /// Optional JSON report output path.
    pub report_path: Option<PathBuf>,
    /// Additional search paths for .olean resolution.
    pub extra_search_paths: Vec<PathBuf>,
}

impl Default for MathLibVerifyConfig {
    fn default() -> Self {
        Self {
            mathlib_path: PathBuf::new(),
            progress_interval: 100,
            stack_size_bytes: 0,
            heartbeat_limit: 0,
            report_path: None,
            extra_search_paths: Vec::new(),
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Result types
// ════════════════════════════════════════════════════════════════════════════

/// Per-file verification outcome with error classification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FileResult {
    pub module_name: String,
    pub rel_path: String,
    pub verified_ok: bool,
    pub constants_added: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub elapsed_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_kind: Option<MathLibErrorKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_detail: Option<String>,
}

/// Summary report for a Mathlib verification run.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MathLibVerifyReport {
    pub mathlib_path: String,
    pub total_olean_files: usize,
    pub modules_processed: usize,
    pub modules_loaded: usize,
    pub modules_failed: usize,
    pub total_constants: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub total_skipped: usize,
    pub pass_rate_pct: f64,
    pub total_elapsed_secs: f64,
    pub error_breakdown: BTreeMap<String, usize>,
    /// Top-level module groups (e.g. "Mathlib.Data", "Mathlib.Algebra").
    pub module_groups: BTreeMap<String, ModuleGroupStats>,
    pub files: Vec<FileResult>,
}

/// Stats for a top-level module group.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ModuleGroupStats {
    pub module_count: usize,
    pub tc_pass: usize,
    pub tc_fail: usize,
    pub load_failures: usize,
}

// ════════════════════════════════════════════════════════════════════════════
// Core API
// ════════════════════════════════════════════════════════════════════════════

/// Run Mathlib verification over all `.olean` files under `config.mathlib_path`.
///
/// Discovers files, builds dependency order, processes each module through
/// the verify-olean pipeline, classifies errors, and produces a report.
pub fn run_mathlib_verify(
    config: &MathLibVerifyConfig,
) -> MathLibVerifyResult<MathLibVerifyReport> {
    let root = &config.mathlib_path;
    if !root.is_dir() {
        return Err(MathLibVerifyError::PathNotFound(root.clone()));
    }

    let olean_files = discover_olean_files(root);
    if olean_files.is_empty() {
        return Err(MathLibVerifyError::NoOleanFiles(root.clone()));
    }

    let (ordered_modules, _parse_failures) = build_dependency_order(&olean_files, root);

    let mut search_paths = default_search_paths();
    search_paths.push(root.to_path_buf());
    for extra in &config.extra_search_paths {
        search_paths.push(extra.clone());
    }

    let mut env = Environment::default();
    preload_init_if_needed(&mut env, root, &search_paths);

    let start = Instant::now();
    let mut known_names: HashSet<String> = HashSet::new();
    collect_new_env_names(&env, &mut known_names);

    let mut file_results = Vec::with_capacity(ordered_modules.len());

    for (idx, desc) in ordered_modules.iter().enumerate() {
        let rel_path = relative_display(&desc.path, root);
        let module_result = verify_one_module(
            &mut env,
            &desc.module_name,
            &rel_path,
            &search_paths,
            &mut known_names,
            false,
        );

        let file_result = convert_module_result(&module_result);
        file_results.push(file_result);

        if config.progress_interval > 0 && (idx + 1) % config.progress_interval == 0 {
            let elapsed = start.elapsed();
            let rate = (idx + 1) as f64 / elapsed.as_secs_f64().max(0.001);
            info!(
                processed = idx + 1,
                total = ordered_modules.len(),
                rate = format_args!("{rate:.1}"),
                elapsed_secs = format_args!("{:.1}", elapsed.as_secs_f64()),
                "mathlib verify progress",
            );
        }
    }

    let elapsed = start.elapsed();
    let batch = build_summary(
        root,
        olean_files.len(),
        ordered_modules.len(),
        ordered_modules
            .iter()
            .enumerate()
            .map(|(i, desc)| {
                let fr = &file_results[i];
                ModuleResult {
                    path: fr.rel_path.clone(),
                    module_name: desc.module_name.clone(),
                    load_ok: fr.verified_ok
                        || fr
                            .error_kind
                            .as_ref()
                            .is_some_and(|k| *k != MathLibErrorKind::OleanLoadFailed),
                    constants_added: fr.constants_added,
                    constants_skipped: 0,
                    tc_pass: fr.tc_pass,
                    tc_fail: fr.tc_fail,
                    elapsed_ms: fr.elapsed_ms,
                    load_error: if fr.error_kind.as_ref()
                        == Some(&MathLibErrorKind::OleanLoadFailed)
                    {
                        fr.error_detail.clone()
                    } else {
                        None
                    },
                    tc_errors: BTreeMap::new(),
                }
            })
            .collect(),
        elapsed,
    );

    let report = build_report(&config.mathlib_path, &batch, file_results, elapsed);
    Ok(report)
}

// ════════════════════════════════════════════════════════════════════════════
// Internal helpers
// ════════════════════════════════════════════════════════════════════════════

/// Convert a `ModuleResult` from the verify_batch layer into our `FileResult`
/// with error classification.
fn convert_module_result(mr: &ModuleResult) -> FileResult {
    let (error_kind, error_detail) = if let Some(ref err) = mr.load_error {
        (Some(classify_error(err)), Some(err.clone()))
    } else if mr.tc_fail > 0 {
        let detail = if mr.tc_errors.is_empty() {
            format!("{} type-check failures", mr.tc_fail)
        } else {
            mr.tc_errors.values().next().cloned().unwrap_or_default()
        };
        (Some(classify_error(&detail)), Some(detail))
    } else {
        (None, None)
    };

    FileResult {
        module_name: mr.module_name.clone(),
        rel_path: mr.path.clone(),
        verified_ok: mr.load_ok && mr.tc_fail == 0,
        constants_added: mr.constants_added,
        tc_pass: mr.tc_pass,
        tc_fail: mr.tc_fail,
        elapsed_ms: mr.elapsed_ms,
        error_kind,
        error_detail,
    }
}

/// Build the summary report from batch results and file-level data.
fn build_report(
    mathlib_path: &Path,
    batch: &BatchSummary,
    files: Vec<FileResult>,
    elapsed: Duration,
) -> MathLibVerifyReport {
    let mut error_breakdown: BTreeMap<String, usize> = BTreeMap::new();
    let mut module_groups: BTreeMap<String, ModuleGroupStats> = BTreeMap::new();

    for fr in &files {
        // Error breakdown
        if let Some(ref kind) = fr.error_kind {
            *error_breakdown.entry(kind.to_string()).or_default() += 1;
        }

        // Module group stats (first two components: "Mathlib.Data" etc.)
        let group = module_group_name(&fr.module_name);
        let stats = module_groups.entry(group).or_default();
        stats.module_count += 1;
        stats.tc_pass += fr.tc_pass;
        stats.tc_fail += fr.tc_fail;
        if !fr.verified_ok && fr.error_kind.as_ref() == Some(&MathLibErrorKind::OleanLoadFailed) {
            stats.load_failures += 1;
        }
    }

    MathLibVerifyReport {
        mathlib_path: mathlib_path.to_string_lossy().to_string(),
        total_olean_files: batch.total_files,
        modules_processed: batch.processed_files,
        modules_loaded: batch.load_success,
        modules_failed: batch.load_failure,
        total_constants: batch.total_constants,
        tc_pass: batch.tc_pass,
        tc_fail: batch.tc_fail,
        total_skipped: batch.total_skipped,
        pass_rate_pct: batch.pass_rate_pct,
        total_elapsed_secs: elapsed.as_secs_f64(),
        error_breakdown,
        module_groups,
        files,
    }
}

/// Extract the top-level module group from a fully-qualified name.
/// "Mathlib.Data.Nat.Basic" -> "Mathlib.Data"
/// "Init.Prelude" -> "Init"
#[must_use]
pub(crate) fn module_group_name(module_name: &str) -> String {
    let parts: Vec<&str> = module_name.splitn(3, '.').collect();
    if parts.len() >= 2 {
        format!("{}.{}", parts[0], parts[1])
    } else {
        parts[0].to_string()
    }
}

/// Save a report as JSON to the given path.
pub fn save_report(report: &MathLibVerifyReport, path: &Path) -> MathLibVerifyResult<()> {
    let json = serde_json::to_string_pretty(report)?;
    std::fs::write(path, json)?;
    Ok(())
}
