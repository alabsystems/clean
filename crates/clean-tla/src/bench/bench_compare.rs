// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deterministic benchmark comparison core.
//!
//! This mirrors the pure classification logic from `scripts/bench_compare.py`
//! without doing file IO or CLI/report wiring.

use std::collections::BTreeMap;

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

/// Classify candidate benchmark samples against a baseline.
///
/// Candidate ordering is deterministic because callers pass `BTreeMap`, and
/// the returned vectors follow candidate key order. A zero baseline sample is
/// skipped to match the Python implementation's divide-by-zero guard.
pub fn classify_benchmarks(
    baseline: &BTreeMap<String, BenchSample>,
    candidate: &BTreeMap<String, BenchSample>,
    threshold_pct: f64,
) -> BenchComparison {
    let mut comparison = BenchComparison {
        regressions: Vec::new(),
        improvements: Vec::new(),
        unchanged: Vec::new(),
        new_benchmarks: Vec::new(),
    };

    for (name, candidate_sample) in candidate {
        let Some(baseline_sample) = baseline.get(name) else {
            comparison.new_benchmarks.push(NewBenchmark {
                name: name.clone(),
                ns_per_iter: candidate_sample.ns_per_iter,
            });
            continue;
        };

        if baseline_sample.ns_per_iter == 0 {
            continue;
        }

        let raw_change_pct = ((candidate_sample.ns_per_iter as f64
            - baseline_sample.ns_per_iter as f64)
            / baseline_sample.ns_per_iter as f64)
            * 100.0;
        let change = BenchChange {
            name: name.clone(),
            baseline_ns: baseline_sample.ns_per_iter,
            candidate_ns: candidate_sample.ns_per_iter,
            change_pct: round_two_decimals(raw_change_pct),
        };

        if raw_change_pct > threshold_pct {
            comparison.regressions.push(change);
        } else if raw_change_pct < -threshold_pct {
            comparison.improvements.push(change);
        } else {
            comparison.unchanged.push(change);
        }
    }

    comparison
}

/// Classify plain benchmark name-to-nanoseconds maps.
///
/// This is a convenience boundary for callers migrating from script-level JSON
/// parsing: callers can normalize raw timing maps without constructing
/// `BenchSample` values themselves. `BTreeMap` keeps input and output ordering
/// deterministic.
pub fn classify_benchmark_ns_maps(
    baseline_ns: &BTreeMap<String, u64>,
    candidate_ns: &BTreeMap<String, u64>,
    threshold_pct: f64,
) -> BenchComparison {
    let baseline = normalize_benchmark_ns_map(baseline_ns);
    let candidate = normalize_benchmark_ns_map(candidate_ns);
    classify_benchmarks(&baseline, &candidate, threshold_pct)
}

/// Build the deterministic JSON-compatible report shape from a comparison.
pub fn build_benchmark_report(
    metadata: BenchReportMetadata,
    comparison: &BenchComparison,
) -> BenchReport {
    BenchReport {
        baseline_commit: metadata.baseline_commit,
        candidate_commit: metadata.candidate_commit,
        baseline_cargo_build_jobs: metadata.baseline_cargo_build_jobs,
        candidate_cargo_build_jobs: metadata.candidate_cargo_build_jobs,
        baseline_cargo_command: metadata.baseline_cargo_command,
        candidate_cargo_command: metadata.candidate_cargo_command,
        threshold_pct: metadata.threshold_pct,
        summary: BenchReportSummary {
            regressions: comparison.regressions.len(),
            improvements: comparison.improvements.len(),
            unchanged: comparison.unchanged.len(),
            new: comparison.new_benchmarks.len(),
        },
        regressions: comparison.regressions.clone(),
        improvements: comparison.improvements.clone(),
        new_benchmarks: comparison.new_benchmarks.clone(),
    }
}

/// Normalize plain benchmark name-to-nanoseconds maps into `BenchSample` maps.
pub fn normalize_benchmark_ns_map(
    samples: &BTreeMap<String, u64>,
) -> BTreeMap<String, BenchSample> {
    samples
        .iter()
        .map(|(name, ns_per_iter)| {
            (
                name.clone(),
                BenchSample {
                    ns_per_iter: *ns_per_iter,
                },
            )
        })
        .collect()
}

fn round_two_decimals(value: f64) -> f64 {
    (value * 100.0).round() / 100.0
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(ns_per_iter: u64) -> BenchSample {
        BenchSample { ns_per_iter }
    }

    fn benchmarks(entries: &[(&str, u64)]) -> BTreeMap<String, BenchSample> {
        entries
            .iter()
            .map(|(name, ns_per_iter)| ((*name).to_string(), sample(*ns_per_iter)))
            .collect()
    }

    fn ns_map(entries: &[(&str, u64)]) -> BTreeMap<String, u64> {
        entries
            .iter()
            .map(|(name, ns_per_iter)| ((*name).to_string(), *ns_per_iter))
            .collect()
    }

    fn report_metadata() -> BenchReportMetadata {
        BenchReportMetadata {
            baseline_commit: "base".to_string(),
            candidate_commit: "candidate".to_string(),
            baseline_cargo_build_jobs: "1".to_string(),
            candidate_cargo_build_jobs: "1".to_string(),
            baseline_cargo_command: "CARGO_BUILD_JOBS=1 cargo bench -j 1".to_string(),
            candidate_cargo_command: "CARGO_BUILD_JOBS=1 cargo bench -j 1".to_string(),
            threshold_pct: 10.0,
        }
    }

    #[test]
    fn bench_compare_classifies_regressions() {
        let baseline = benchmarks(&[("suite::slow", 100)]);
        let candidate = benchmarks(&[("suite::slow", 125)]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.regressions,
            vec![BenchChange {
                name: "suite::slow".to_string(),
                baseline_ns: 100,
                candidate_ns: 125,
                change_pct: 25.0,
            }],
            "25% slower benchmark should be classified as regression",
        );
        assert!(
            comparison.improvements.is_empty(),
            "regression case should not record improvements",
        );
    }

    #[test]
    fn bench_compare_classifies_improvements() {
        let baseline = benchmarks(&[("suite::fast", 100)]);
        let candidate = benchmarks(&[("suite::fast", 75)]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.improvements,
            vec![BenchChange {
                name: "suite::fast".to_string(),
                baseline_ns: 100,
                candidate_ns: 75,
                change_pct: -25.0,
            }],
            "25% faster benchmark should be classified as improvement",
        );
        assert!(
            comparison.regressions.is_empty(),
            "improvement case should not record regressions",
        );
    }

    #[test]
    fn bench_compare_classifies_unchanged_within_threshold() {
        let baseline = benchmarks(&[("suite::steady", 100)]);
        let candidate = benchmarks(&[("suite::steady", 105)]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.unchanged,
            vec![BenchChange {
                name: "suite::steady".to_string(),
                baseline_ns: 100,
                candidate_ns: 105,
                change_pct: 5.0,
            }],
            "5% slower benchmark should remain unchanged at a 10% threshold",
        );
    }

    #[test]
    fn bench_compare_records_new_benchmarks() {
        let baseline = benchmarks(&[]);
        let candidate = benchmarks(&[("suite::new", 42)]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.new_benchmarks,
            vec![NewBenchmark {
                name: "suite::new".to_string(),
                ns_per_iter: 42,
            }],
            "candidate-only benchmark should be recorded as new",
        );
    }

    #[test]
    fn bench_compare_skips_zero_baseline_samples() {
        let baseline = benchmarks(&[("suite::zero", 0)]);
        let candidate = benchmarks(&[("suite::zero", 100)]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison,
            BenchComparison {
                regressions: vec![],
                improvements: vec![],
                unchanged: vec![],
                new_benchmarks: vec![],
            },
            "zero baseline should be skipped rather than classified",
        );
    }

    #[test]
    fn bench_compare_returns_deterministic_candidate_key_order() {
        let baseline = benchmarks(&[
            ("suite::z_regression", 100),
            ("suite::a_improvement", 100),
            ("suite::m_unchanged", 100),
        ]);
        let candidate = benchmarks(&[
            ("suite::z_regression", 125),
            ("suite::new_b", 50),
            ("suite::a_improvement", 75),
            ("suite::new_a", 25),
            ("suite::m_unchanged", 105),
        ]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.improvements[0].name, "suite::a_improvement",
            "improvements should follow sorted candidate key order",
        );
        assert_eq!(
            comparison.unchanged[0].name, "suite::m_unchanged",
            "unchanged results should follow sorted candidate key order",
        );
        assert_eq!(
            comparison.regressions[0].name, "suite::z_regression",
            "regressions should follow sorted candidate key order",
        );
        assert_eq!(
            comparison
                .new_benchmarks
                .iter()
                .map(|benchmark| benchmark.name.as_str())
                .collect::<Vec<_>>(),
            vec!["suite::new_a", "suite::new_b"],
            "new benchmarks should follow sorted candidate key order",
        );
    }

    #[test]
    fn bench_compare_normalizes_plain_ns_maps() {
        let baseline = ns_map(&[("suite::slow", 100), ("suite::zero", 0)]);
        let candidate = ns_map(&[
            ("suite::slow", 125),
            ("suite::new_b", 50),
            ("suite::new_a", 25),
            ("suite::zero", 100),
        ]);

        let comparison = classify_benchmark_ns_maps(&baseline, &candidate, 10.0);

        assert_eq!(
            comparison.regressions,
            vec![BenchChange {
                name: "suite::slow".to_string(),
                baseline_ns: 100,
                candidate_ns: 125,
                change_pct: 25.0,
            }],
            "plain map helper should classify existing samples",
        );
        assert_eq!(
            comparison
                .new_benchmarks
                .iter()
                .map(|benchmark| benchmark.name.as_str())
                .collect::<Vec<_>>(),
            vec!["suite::new_a", "suite::new_b"],
            "plain map helper should preserve deterministic candidate ordering",
        );
        assert!(
            comparison
                .regressions
                .iter()
                .all(|change| change.name != "suite::zero"),
            "plain map helper should preserve zero-baseline skip behavior",
        );
    }

    #[test]
    fn bench_compare_builds_deterministic_report_shape() {
        let baseline = benchmarks(&[
            ("suite::a_improvement", 100),
            ("suite::m_unchanged", 100),
            ("suite::z_regression", 100),
        ]);
        let candidate = benchmarks(&[
            ("suite::z_regression", 125),
            ("suite::new_b", 50),
            ("suite::a_improvement", 75),
            ("suite::new_a", 25),
            ("suite::m_unchanged", 105),
        ]);

        let comparison = classify_benchmarks(&baseline, &candidate, 10.0);
        let report = build_benchmark_report(report_metadata(), &comparison);

        assert_eq!(report.baseline_commit, "base");
        assert_eq!(report.candidate_commit, "candidate");
        assert_eq!(report.baseline_cargo_build_jobs, "1");
        assert_eq!(report.candidate_cargo_build_jobs, "1");
        assert_eq!(report.threshold_pct, 10.0);
        assert_eq!(
            report.summary,
            BenchReportSummary {
                regressions: 1,
                improvements: 1,
                unchanged: 1,
                new: 2,
            },
            "report summary should count all classified buckets",
        );
        assert_eq!(
            report
                .regressions
                .iter()
                .map(|change| change.name.as_str())
                .collect::<Vec<_>>(),
            vec!["suite::z_regression"],
            "report should keep deterministic regression ordering",
        );
        assert_eq!(
            report
                .improvements
                .iter()
                .map(|change| change.name.as_str())
                .collect::<Vec<_>>(),
            vec!["suite::a_improvement"],
            "report should keep deterministic improvement ordering",
        );
        assert_eq!(
            report
                .new_benchmarks
                .iter()
                .map(|benchmark| benchmark.name.as_str())
                .collect::<Vec<_>>(),
            vec!["suite::new_a", "suite::new_b"],
            "report should keep deterministic new-benchmark ordering",
        );
    }
}
