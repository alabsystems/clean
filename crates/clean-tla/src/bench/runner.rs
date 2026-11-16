// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Benchmark Runner for TLAPS Obligations
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! Runs benchmark suites and collects statistics.
//!
//! ## Backend Support
//!
//! The runner supports pluggable proof backends via the `ProofBackend` trait.
//! Use `run_with_backend` or `run_with_registry` for backend-based proving.

use crate::bench::backend::{NativeTacticBackend, ProofBackend, ProofContext, ProofOutcome};
use crate::bench::schema::BenchmarkObligation;
use crate::tactic::prove_tla_obligation;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

/// Result of running a single benchmark
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    /// Obligation ID
    pub id: String,

    /// Category (extracted from id path)
    pub category: String,

    /// Whether the proof succeeded
    pub proved: bool,

    /// Whether the result matches expected
    pub correct: bool,

    /// Expected result
    pub expected: bool,

    /// Time taken in milliseconds
    pub time_ms: u64,

    /// Tactics tried
    pub tactics_tried: Vec<String>,

    /// Certificate (if proved)
    pub certificate: Option<String>,

    /// Error message (if failed)
    pub error: Option<String>,

    /// Backend that produced this result (if using backend-based runner)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub backend: Option<String>,
}

/// Summary statistics for a benchmark run
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkSummary {
    /// Total number of obligations
    pub total: usize,

    /// Number proved
    pub proved: usize,

    /// Number failed
    pub failed: usize,

    /// Number with correct result (matches expected)
    pub correct: usize,

    /// Number with incorrect result (doesn't match expected)
    pub incorrect: usize,

    /// Success rate (proved/total)
    pub success_rate: f64,

    /// Correctness rate (correct/total)
    pub correctness_rate: f64,

    /// Average time per obligation (ms)
    pub avg_time_ms: f64,

    /// Statistics by category
    pub by_category: HashMap<String, CategoryStats>,
}

/// Statistics for a single category
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CategoryStats {
    pub total: usize,
    pub proved: usize,
    pub failed: usize,
    pub correct: usize,
    pub success_rate: f64,
    pub avg_time_ms: f64,
}

/// Benchmark runner
pub struct BenchmarkRunner {
    /// Results collected
    results: Vec<BenchmarkResult>,
    /// Proof backend (defaults to NativeTacticBackend)
    backend: Arc<dyn ProofBackend>,
    /// Proof context for backend calls
    context: ProofContext,
}

impl BenchmarkRunner {
    /// Create a new benchmark runner with the default native backend
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
            backend: Arc::new(NativeTacticBackend::new()),
            context: ProofContext::new(),
        }
    }

    /// Create a benchmark runner with a specific backend
    pub fn with_backend(backend: Arc<dyn ProofBackend>) -> Self {
        Self {
            results: Vec::new(),
            backend,
            context: ProofContext::new(),
        }
    }

    /// Set the proof context (timeout, trace options, etc.)
    pub fn with_context(mut self, context: ProofContext) -> Self {
        self.context = context;
        self
    }

    /// Run a single obligation using the legacy direct call
    ///
    /// This method calls `prove_tla_obligation` directly for backward compatibility.
    /// For backend-based proving, use `run_with_backend`.
    pub fn run_obligation(&mut self, obligation: &BenchmarkObligation) -> BenchmarkResult {
        let category = extract_category(&obligation.id);

        // Convert to TlaObligation
        let tla_obligation = match obligation.to_tla_obligation() {
            Ok(o) => o,
            Err(e) => {
                return BenchmarkResult {
                    id: obligation.id.clone(),
                    category,
                    proved: false,
                    correct: !obligation.expected_result, // If expected true, this is incorrect
                    expected: obligation.expected_result,
                    time_ms: 0,
                    tactics_tried: vec![],
                    certificate: None,
                    error: Some(format!("Parse error: {}", e)),
                    backend: None,
                };
            }
        };

        // Time the proof
        let start = Instant::now();
        let result = prove_tla_obligation(&tla_obligation);
        let elapsed_ms = start.elapsed().as_millis() as u64;

        let correct = result.proved == obligation.expected_result;

        let bench_result = BenchmarkResult {
            id: obligation.id.clone(),
            category,
            proved: result.proved,
            correct,
            expected: obligation.expected_result,
            time_ms: elapsed_ms,
            tactics_tried: result.tactics_tried,
            certificate: result.certificate,
            error: result.error,
            backend: None,
        };

        self.results.push(bench_result.clone());
        bench_result
    }

    /// Run a single obligation using the configured backend
    ///
    /// Uses the ProofBackend trait for pluggable proof strategies.
    pub fn run_with_backend(&mut self, obligation: &BenchmarkObligation) -> BenchmarkResult {
        let category = extract_category(&obligation.id);

        // Convert to TlaObligation
        let tla_obligation = match obligation.to_tla_obligation() {
            Ok(o) => o,
            Err(e) => {
                return BenchmarkResult {
                    id: obligation.id.clone(),
                    category,
                    proved: false,
                    correct: !obligation.expected_result,
                    expected: obligation.expected_result,
                    time_ms: 0,
                    tactics_tried: vec![],
                    certificate: None,
                    error: Some(format!("Parse error: {}", e)),
                    backend: Some(self.backend.name().to_string()),
                };
            }
        };

        // Check if backend supports this obligation
        if !self.backend.supports(&tla_obligation) {
            return BenchmarkResult {
                id: obligation.id.clone(),
                category,
                proved: false,
                correct: !obligation.expected_result,
                expected: obligation.expected_result,
                time_ms: 0,
                tactics_tried: vec![],
                certificate: None,
                error: Some(format!(
                    "Backend '{}' does not support this obligation",
                    self.backend.name()
                )),
                backend: Some(self.backend.name().to_string()),
            };
        }

        // Run through backend
        let result = self.backend.prove(&tla_obligation, &self.context);
        let elapsed_ms = result.duration.as_millis() as u64;

        let proved = result.outcome.is_proved();
        let correct = proved == obligation.expected_result;

        let error = match &result.outcome {
            ProofOutcome::Failed { message, .. } => Some(message.clone()),
            ProofOutcome::Unknown { reason } => Some(format!("Unknown: {}", reason)),
            ProofOutcome::Proved => None,
        };

        let bench_result = BenchmarkResult {
            id: obligation.id.clone(),
            category,
            proved,
            correct,
            expected: obligation.expected_result,
            time_ms: elapsed_ms,
            tactics_tried: result.tactics_tried,
            certificate: result.certificate,
            error,
            backend: Some(self.backend.name().to_string()),
        };

        self.results.push(bench_result.clone());
        bench_result
    }

    /// Run all obligations from a directory
    pub fn run_directory(&mut self, path: &Path) -> Result<(), String> {
        let pattern = path.join("**/*.json");
        let pattern_str = pattern.to_string_lossy();

        for entry in glob::glob(&pattern_str).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let obligation = BenchmarkObligation::load(&entry)?;
            self.run_obligation(&obligation);
        }

        Ok(())
    }

    /// Get all results
    pub fn results(&self) -> &[BenchmarkResult] {
        &self.results
    }

    /// Compute summary statistics
    pub fn summary(&self) -> BenchmarkSummary {
        let total = self.results.len();
        let proved: usize = self.results.iter().filter(|r| r.proved).count();
        let failed = total - proved;
        let correct: usize = self.results.iter().filter(|r| r.correct).count();
        let incorrect = total - correct;

        let total_time: u64 = self.results.iter().map(|r| r.time_ms).sum();
        let avg_time_ms = if total > 0 {
            total_time as f64 / total as f64
        } else {
            0.0
        };

        let success_rate = if total > 0 {
            proved as f64 / total as f64
        } else {
            0.0
        };

        let correctness_rate = if total > 0 {
            correct as f64 / total as f64
        } else {
            0.0
        };

        // Group by category
        let mut by_category: HashMap<String, Vec<&BenchmarkResult>> = HashMap::new();
        for result in &self.results {
            by_category
                .entry(result.category.clone())
                .or_default()
                .push(result);
        }

        let category_stats: HashMap<String, CategoryStats> = by_category
            .into_iter()
            .map(|(cat, results)| {
                let cat_total = results.len();
                let cat_proved: usize = results.iter().filter(|r| r.proved).count();
                let cat_correct: usize = results.iter().filter(|r| r.correct).count();
                let cat_time: u64 = results.iter().map(|r| r.time_ms).sum();

                let stats = CategoryStats {
                    total: cat_total,
                    proved: cat_proved,
                    failed: cat_total - cat_proved,
                    correct: cat_correct,
                    success_rate: if cat_total > 0 {
                        cat_proved as f64 / cat_total as f64
                    } else {
                        0.0
                    },
                    avg_time_ms: if cat_total > 0 {
                        cat_time as f64 / cat_total as f64
                    } else {
                        0.0
                    },
                };

                (cat, stats)
            })
            .collect();

        BenchmarkSummary {
            total,
            proved,
            failed,
            correct,
            incorrect,
            success_rate,
            correctness_rate,
            avg_time_ms,
            by_category: category_stats,
        }
    }

    /// Print summary to stdout
    pub fn print_summary(&self) {
        let summary = self.summary();

        println!("\n=== TLAPS Benchmark Summary ===\n");
        println!(
            "Total: {} | Proved: {} | Failed: {} | Correct: {} | Incorrect: {}",
            summary.total, summary.proved, summary.failed, summary.correct, summary.incorrect
        );
        println!(
            "Success rate: {:.1}% | Correctness rate: {:.1}%",
            summary.success_rate * 100.0,
            summary.correctness_rate * 100.0
        );
        println!("Average time: {:.2}ms\n", summary.avg_time_ms);

        println!("By Category:");
        println!(
            "{:<20} {:>6} {:>6} {:>6} {:>8} {:>8}",
            "Category", "Total", "Proved", "Failed", "Rate", "Avg ms"
        );
        println!("{}", "-".repeat(60));

        let mut categories: Vec<_> = summary.by_category.iter().collect();
        categories.sort_by_key(|(k, _)| k.as_str());

        for (cat, stats) in categories {
            println!(
                "{:<20} {:>6} {:>6} {:>6} {:>7.1}% {:>7.2}",
                cat,
                stats.total,
                stats.proved,
                stats.failed,
                stats.success_rate * 100.0,
                stats.avg_time_ms
            );
        }
        println!();
    }

    /// Print detailed results for failed obligations
    pub fn print_failures(&self) {
        let failures: Vec<_> = self.results.iter().filter(|r| !r.correct).collect();

        if failures.is_empty() {
            println!("No failures!");
            return;
        }

        println!("\n=== Failed Obligations ===\n");
        for result in failures {
            println!(
                "- {} (expected: {}, got: {})",
                result.id,
                if result.expected {
                    "provable"
                } else {
                    "unprovable"
                },
                if result.proved { "proved" } else { "failed" }
            );
            if let Some(ref err) = result.error {
                println!("  Error: {}", err);
            }
            println!("  Tactics tried: {:?}", result.tactics_tried);
        }
    }
}

impl Default for BenchmarkRunner {
    fn default() -> Self {
        Self::new()
    }
}

/// Extract category from obligation ID (first path component)
fn extract_category(id: &str) -> String {
    id.split('/').next().unwrap_or("unknown").to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_category() {
        assert_eq!(
            extract_category("nat_induction/sum_formula"),
            "nat_induction"
        );
        assert_eq!(extract_category("temporal/always_intro"), "temporal");
        assert_eq!(extract_category("simple"), "simple");
    }

    #[test]
    fn test_runner_with_backend() {
        let backend = Arc::new(NativeTacticBackend::new());
        let runner = BenchmarkRunner::with_backend(backend);
        // Verify backend is set correctly
        assert!(Arc::strong_count(&runner.backend) >= 1);
    }

    #[test]
    fn test_runner_with_context() {
        use std::time::Duration;

        let context = ProofContext::new()
            .with_timeout(Duration::from_secs(10))
            .with_trace(true);

        let runner = BenchmarkRunner::new().with_context(context);
        assert!(runner.context.trace);
        assert_eq!(runner.context.timeout, Some(Duration::from_secs(10)));
    }
}
