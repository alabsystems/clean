// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parallel batch type-checking for arXiv formalizations.
//!
//! Provides [`batch_typecheck`] which runs simulated type-checks across
//! statements in parallel using a rayon thread pool, with per-statement
//! timeout tracking, timing statistics, and JSON persistence.

use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use rayon::prelude::*;
use rayon::ThreadPoolBuilder;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::error::MathverseResult;

const REPORT_FILE_NAME: &str = "batch_typecheck_report.json";

// ════════════════════════════════════════════════════════════════════════════
// Configuration & Types
// ════════════════════════════════════════════════════════════════════════════

/// Configuration for batch type-checking.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchTypecheckConfig {
    pub timeout_ms: u64,
    pub max_parallel: usize,
    pub allow_sorry: bool,
    pub output_dir: Option<PathBuf>,
}

impl Default for BatchTypecheckConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 60_000,
            max_parallel: 4,
            allow_sorry: false,
            output_dir: None,
        }
    }
}

/// Outcome for a single statement type-check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TypecheckStatus {
    Passed,
    Failed(String),
    Timeout,
    Skipped(String),
}

/// Input statement for batch type-checking.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statement {
    pub name: String,
    pub paper_id: String,
    pub lean_code: String,
}

/// Per-statement batch type-check result.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatementResult {
    pub name: String,
    pub paper_id: String,
    pub lean_code: String,
    pub status: TypecheckStatus,
    pub elapsed_ms: u64,
    pub error_detail: Option<String>,
}

/// Aggregate batch type-check report.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BatchReport {
    pub total: usize,
    pub passed: usize,
    pub failed: usize,
    pub timed_out: usize,
    pub skipped: usize,
    pub pass_rate: f64,
    pub mean_elapsed_ms: f64,
    pub median_elapsed_ms: f64,
    pub p99_elapsed_ms: f64,
    pub total_elapsed_ms: u64,
    pub results: Vec<StatementResult>,
}

// ════════════════════════════════════════════════════════════════════════════
// Core API
// ════════════════════════════════════════════════════════════════════════════

/// Run batch type-checking with parallel execution and per-statement accounting.
pub fn batch_typecheck(statements: &[Statement], config: &BatchTypecheckConfig) -> BatchReport {
    let batch_start = Instant::now();
    let results = run_parallel(statements, config);
    let report = build_report(results, batch_start.elapsed());
    maybe_save_report(&report, config);
    report
}

/// Compute mean, median, and p99 timing statistics.
#[must_use]
pub fn compute_timing_stats(elapsed_ms: &[u64]) -> (f64, f64, f64) {
    if elapsed_ms.is_empty() {
        return (0.0, 0.0, 0.0);
    }
    let sum: u128 = elapsed_ms.iter().map(|&v| u128::from(v)).sum();
    let mean = sum as f64 / elapsed_ms.len() as f64;
    let mut sorted = elapsed_ms.to_vec();
    sorted.sort_unstable();
    let median = if sorted.len().is_multiple_of(2) {
        let upper = sorted.len() / 2;
        (sorted[upper - 1] as f64 + sorted[upper] as f64) / 2.0
    } else {
        sorted[sorted.len() / 2] as f64
    };
    let p99_index = sorted.len().saturating_mul(99).saturating_sub(1) / 100;
    let p99 = sorted[p99_index] as f64;
    (mean, median, p99)
}

/// Save a batch report as JSON.
pub fn save_report(report: &BatchReport, path: &Path) -> MathverseResult<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, report)?;
    writer.flush()?;
    Ok(())
}

/// Load a batch report from JSON.
pub fn load_report(path: &Path) -> MathverseResult<BatchReport> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    Ok(serde_json::from_reader(reader)?)
}

// ════════════════════════════════════════════════════════════════════════════
// Internal helpers
// ════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Error)]
enum SimulatedTypecheckError {
    #[error("statement contains `sorry` but allow_sorry=false")]
    SorryNotAllowed,
    #[error("statement must contain a `theorem` or `def` declaration")]
    MissingDeclarationKeyword,
}

fn run_parallel(statements: &[Statement], config: &BatchTypecheckConfig) -> Vec<StatementResult> {
    let completed = AtomicUsize::new(0);
    let total = statements.len();
    let worker_count = config.max_parallel.max(1);

    match ThreadPoolBuilder::new().num_threads(worker_count).build() {
        Ok(pool) => pool.install(|| {
            statements
                .par_iter()
                .map(|s| typecheck_one(s, config, &completed, total))
                .collect()
        }),
        Err(_) => statements
            .iter()
            .map(|s| typecheck_one(s, config, &completed, total))
            .collect(),
    }
}

fn build_report(results: Vec<StatementResult>, elapsed: Duration) -> BatchReport {
    let elapsed_values: Vec<u64> = results.iter().map(|r| r.elapsed_ms).collect();
    let (mean, median, p99) = compute_timing_stats(&elapsed_values);
    let total = results.len();
    let passed = results
        .iter()
        .filter(|r| matches!(r.status, TypecheckStatus::Passed))
        .count();
    let failed = results
        .iter()
        .filter(|r| matches!(r.status, TypecheckStatus::Failed(_)))
        .count();
    let timed_out = results
        .iter()
        .filter(|r| matches!(r.status, TypecheckStatus::Timeout))
        .count();
    let skipped = results
        .iter()
        .filter(|r| matches!(r.status, TypecheckStatus::Skipped(_)))
        .count();
    BatchReport {
        total,
        passed,
        failed,
        timed_out,
        skipped,
        pass_rate: if total == 0 {
            0.0
        } else {
            passed as f64 / total as f64
        },
        mean_elapsed_ms: mean,
        median_elapsed_ms: median,
        p99_elapsed_ms: p99,
        total_elapsed_ms: duration_to_millis_u64(elapsed),
        results,
    }
}

fn maybe_save_report(report: &BatchReport, config: &BatchTypecheckConfig) {
    if let Some(output_dir) = &config.output_dir {
        let _ = std::fs::create_dir_all(output_dir);
        let _ = save_report(report, &output_dir.join(REPORT_FILE_NAME));
    }
}

fn typecheck_one(
    statement: &Statement,
    config: &BatchTypecheckConfig,
    completed: &AtomicUsize,
    _total: usize,
) -> StatementResult {
    let start = Instant::now();
    let sim = simulate_typecheck(&statement.lean_code, config.allow_sorry);
    let elapsed_ms = duration_to_millis_u64(start.elapsed());

    let (status, error_detail) = if elapsed_ms > config.timeout_ms {
        (
            TypecheckStatus::Timeout,
            Some(format!("exceeded {}ms timeout", config.timeout_ms)),
        )
    } else {
        match sim {
            Ok(()) => (TypecheckStatus::Passed, None),
            Err(e) => classify_error(e),
        }
    };

    completed.fetch_add(1, Ordering::Relaxed);

    StatementResult {
        name: statement.name.clone(),
        paper_id: statement.paper_id.clone(),
        lean_code: statement.lean_code.clone(),
        status,
        elapsed_ms,
        error_detail,
    }
}

fn classify_error(error: SimulatedTypecheckError) -> (TypecheckStatus, Option<String>) {
    let detail = error.to_string();
    let status = match &error {
        SimulatedTypecheckError::SorryNotAllowed => {
            TypecheckStatus::Skipped("contains `sorry`".to_owned())
        }
        SimulatedTypecheckError::MissingDeclarationKeyword => {
            TypecheckStatus::Failed("missing `theorem` or `def` keyword".to_owned())
        }
    };
    (status, Some(detail))
}

fn simulate_typecheck(lean_code: &str, allow_sorry: bool) -> Result<(), SimulatedTypecheckError> {
    if let Some(delay_ms) = extract_delay_ms(lean_code) {
        thread::sleep(Duration::from_millis(delay_ms));
    }
    if contains_token(lean_code, "sorry") && !allow_sorry {
        return Err(SimulatedTypecheckError::SorryNotAllowed);
    }
    if !contains_token(lean_code, "theorem") && !contains_token(lean_code, "def") {
        return Err(SimulatedTypecheckError::MissingDeclarationKeyword);
    }
    Ok(())
}

fn extract_delay_ms(lean_code: &str) -> Option<u64> {
    ["mathverse_delay_ms:", "simulate_delay_ms:"]
        .iter()
        .find_map(|marker| {
            let start = lean_code.find(marker)?;
            let suffix = &lean_code[start + marker.len()..];
            let digits: String = suffix
                .chars()
                .skip_while(|c| c.is_whitespace())
                .take_while(|c| c.is_ascii_digit())
                .collect();
            if digits.is_empty() {
                None
            } else {
                digits.parse::<u64>().ok()
            }
        })
}

#[must_use]
fn contains_token(haystack: &str, needle: &str) -> bool {
    haystack
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|tok| tok == needle)
}

#[must_use]
fn duration_to_millis_u64(duration: Duration) -> u64 {
    let millis = duration.as_millis();
    if millis > u128::from(u64::MAX) {
        u64::MAX
    } else {
        millis as u64
    }
}

#[cfg(test)]
mod tests;
