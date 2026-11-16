// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Serde-facing data shapes for the benchmark comparison report.
//!
//! These types ARE the on-disk/JSON contract that `scripts/bench_compare.py`
//! produced, so they are kept apart from the classification logic in
//! [`super`]: field names and nesting here are part of the report format,
//! not an implementation detail of how a comparison is computed.

use serde::{Deserialize, Serialize};

/// One benchmark timing sample.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub struct BenchSample {
    /// Nanoseconds per iteration.
    pub ns_per_iter: u64,
}

/// A benchmark that exists only in the candidate run.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
pub struct NewBenchmark {
    /// Benchmark name.
    pub name: String,
    /// Candidate nanoseconds per iteration.
    pub ns_per_iter: u64,
}

/// A benchmark change present in both baseline and candidate runs.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct BenchChange {
    /// Benchmark name.
    pub name: String,
    /// Baseline nanoseconds per iteration.
    pub baseline_ns: u64,
    /// Candidate nanoseconds per iteration.
    pub candidate_ns: u64,
    /// Percent change, rounded to two decimal places.
    pub change_pct: f64,
}

/// Classified benchmark comparison.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct BenchComparison {
    /// Benchmarks slower than the threshold.
    pub regressions: Vec<BenchChange>,
    /// Benchmarks faster than the threshold.
    pub improvements: Vec<BenchChange>,
    /// Benchmarks within the threshold.
    pub unchanged: Vec<BenchChange>,
    /// Benchmarks that exist only in the candidate run.
    pub new_benchmarks: Vec<NewBenchmark>,
}

/// Metadata carried into a benchmark comparison report.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct BenchReportMetadata {
    /// Baseline git commit, or `unknown` if the source did not record it.
    pub baseline_commit: String,
    /// Candidate git commit, or `unknown` if the source did not record it.
    pub candidate_commit: String,
    /// Baseline `CARGO_BUILD_JOBS` value, or `unknown` if unavailable.
    pub baseline_cargo_build_jobs: String,
    /// Candidate `CARGO_BUILD_JOBS` value, or `unknown` if unavailable.
    pub candidate_cargo_build_jobs: String,
    /// Baseline cargo command, or `unknown` if unavailable.
    pub baseline_cargo_command: String,
    /// Candidate cargo command, or `unknown` if unavailable.
    pub candidate_cargo_command: String,
    /// Regression threshold percentage used for classification.
    pub threshold_pct: f64,
}

/// Summary counts for a benchmark comparison report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize)]
pub struct BenchReportSummary {
    /// Number of regressions.
    pub regressions: usize,
    /// Number of improvements.
    pub improvements: usize,
    /// Number of unchanged benchmarks.
    pub unchanged: usize,
    /// Number of candidate-only benchmarks.
    pub new: usize,
}

/// JSON-compatible benchmark comparison report.
#[derive(Debug, Clone, PartialEq, Deserialize, Serialize)]
pub struct BenchReport {
    /// Baseline git commit.
    pub baseline_commit: String,
    /// Candidate git commit.
    pub candidate_commit: String,
    /// Baseline `CARGO_BUILD_JOBS` value.
    pub baseline_cargo_build_jobs: String,
    /// Candidate `CARGO_BUILD_JOBS` value.
    pub candidate_cargo_build_jobs: String,
    /// Baseline cargo command.
    pub baseline_cargo_command: String,
    /// Candidate cargo command.
    pub candidate_cargo_command: String,
    /// Regression threshold percentage.
    pub threshold_pct: f64,
    /// Summary counts matching the Python report shape.
    pub summary: BenchReportSummary,
    /// Benchmarks slower than the threshold.
    pub regressions: Vec<BenchChange>,
    /// Benchmarks faster than the threshold.
    pub improvements: Vec<BenchChange>,
    /// Benchmarks that exist only in the candidate run.
    pub new_benchmarks: Vec<NewBenchmark>,
}
