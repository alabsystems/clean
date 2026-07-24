// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Geometry Benchmark Runner
//!
//! This module provides infrastructure for running geometry proof benchmarks,
//! tracking results, and generating reports.
//!
//! ## Directory Structure
//!
//! ```text
//! benchmarks/geometry/<suite>/
//!   <problem_id>/
//!     problem.json        # Problem specification
//!     derivation.txt      # Solver derivation (Newclid/AlphaGeometry format)
//!     derivation.json     # Or JSON format derivation
//!     cert/               # Generated certificates
//!
//! results/geometry/
//!   <date>/
//!     run.jsonl           # Line-delimited JSON results
//!     leaderboard.md      # Rendered leaderboard
//! ```
//!
//! ## Usage
//!
//! ```text
//! let runner = BenchmarkRunner::new("benchmarks/geometry/alphageometry")?;
//!
//! // Load and run all problems
//! let results = runner.run_all()?;
//!
//! // Save results
//! runner.save_results(&results, "results/geometry/2026-01-15")?;
//! ```

use super::derivation::{DerivationParseError, DerivationTrace};
mod goal_match;

use super::geometry::{GeomStep, GeometryCertError, GeometryCertGenerator};
use super::problem::{
    AuxConstruction, BenchmarkResult, GeometryProblem, ProblemParseError, ProblemSolution,
};
use super::CertVerifier;
use crate::env::Environment;
use goal_match::{final_step_signature, goal_signature};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Errors that can occur during benchmarking.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum BenchmarkError {
    /// IO error reading/writing files
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    /// Problem parsing error
    #[error("Problem parse error: {0}")]
    ProblemParse(#[from] ProblemParseError),
    /// Derivation parsing error
    #[error("Derivation parse error: {0}")]
    DerivationParse(#[from] DerivationParseError),
    /// Certificate generation error
    #[error("Certificate generation error: {0}")]
    CertGeneration(#[from] GeometryCertError),
    /// Missing required file
    #[error("Missing file: {0}")]
    MissingFile(String),
    /// Invalid benchmark structure
    #[error("Invalid structure: {0}")]
    InvalidStructure(String),
}

/// Configuration for benchmark runs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkConfig {
    /// Timeout per problem (milliseconds)
    pub timeout_ms: u64,

    /// Whether to verify generated certificates
    pub verify_certs: bool,

    /// Whether to save certificates to disk
    pub save_certs: bool,

    /// Maximum problems to run (0 = all)
    pub max_problems: usize,

    /// Whether to continue on errors
    pub continue_on_error: bool,

    /// Problem IDs to skip
    #[serde(default)]
    pub skip_problems: Vec<String>,

    /// Only run these problem IDs (empty = all)
    #[serde(default)]
    pub only_problems: Vec<String>,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 60_000, // 1 minute
            verify_certs: true,
            save_certs: true,
            max_problems: 0,
            continue_on_error: true,
            skip_problems: Vec::new(),
            only_problems: Vec::new(),
        }
    }
}

/// A benchmark problem with its derivation.
#[derive(Debug)]
pub struct BenchmarkProblem {
    /// Problem ID (directory name)
    pub id: String,

    /// Problem directory path
    pub path: PathBuf,

    /// Parsed problem specification
    pub problem: GeometryProblem,

    /// Derivation trace (if available)
    pub derivation: Option<DerivationTrace>,
}

/// Runner for geometry benchmarks.
pub struct BenchmarkRunner {
    /// Root directory containing problem subdirectories
    suite_dir: PathBuf,

    /// Suite name (extracted from path)
    suite_name: String,

    /// Configuration
    config: BenchmarkConfig,

    /// Certificate generator
    generator: Option<GeometryCertGenerator>,
}

impl BenchmarkRunner {
    /// Create a new benchmark runner for a suite directory.
    pub fn new<P: AsRef<Path>>(suite_dir: P) -> Result<Self, BenchmarkError> {
        let suite_dir = suite_dir.as_ref().to_path_buf();

        let suite_name = suite_dir
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("unknown")
            .to_string();

        Ok(Self {
            suite_dir,
            suite_name,
            config: BenchmarkConfig::default(),
            generator: None,
        })
    }

    /// Set the benchmark configuration.
    pub fn with_config(mut self, config: BenchmarkConfig) -> Self {
        self.config = config;
        self
    }

    /// Initialize the certificate generator.
    pub fn init_generator(&mut self) -> Result<(), BenchmarkError> {
        let mut env = Environment::new();
        env.init_computational_geometry().map_err(|e| {
            BenchmarkError::CertGeneration(GeometryCertError::InvalidDerivation(format!(
                "Failed to init geometry: {:?}",
                e
            )))
        })?;

        self.generator = Some(GeometryCertGenerator::new(env)?);
        Ok(())
    }

    /// Discover all problems in the suite directory.
    pub fn discover_problems(&self) -> Result<Vec<BenchmarkProblem>, BenchmarkError> {
        let mut problems = Vec::new();

        if !self.suite_dir.exists() {
            return Err(BenchmarkError::InvalidStructure(format!(
                "Suite directory does not exist: {}",
                self.suite_dir.display()
            )));
        }

        // Each subdirectory is a problem
        for entry in std::fs::read_dir(&self.suite_dir)? {
            let entry = entry?;
            let path = entry.path();

            if !path.is_dir() {
                continue;
            }

            let problem_id = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("unknown")
                .to_string();

            // Check skip/only filters
            if !self.config.skip_problems.is_empty()
                && self.config.skip_problems.contains(&problem_id)
            {
                continue;
            }

            if !self.config.only_problems.is_empty()
                && !self.config.only_problems.contains(&problem_id)
            {
                continue;
            }

            // Load problem.json
            let problem_path = path.join("problem.json");
            if !problem_path.exists() {
                continue; // Not a valid problem directory
            }

            match GeometryProblem::from_file(&problem_path) {
                Ok(problem) => {
                    // Try to load derivation
                    let derivation = self.load_derivation(&path, &problem_id).ok();

                    problems.push(BenchmarkProblem {
                        id: problem_id,
                        path,
                        problem,
                        derivation,
                    });
                }
                Err(e) if self.config.continue_on_error => {
                    eprintln!("Warning: Failed to load problem {}: {}", problem_id, e);
                }
                Err(e) => return Err(e.into()),
            }
        }

        // Apply max_problems limit
        if self.config.max_problems > 0 && problems.len() > self.config.max_problems {
            problems.truncate(self.config.max_problems);
        }

        Ok(problems)
    }

    /// Load derivation for a problem.
    fn load_derivation(
        &self,
        problem_dir: &Path,
        problem_id: &str,
    ) -> Result<DerivationTrace, BenchmarkError> {
        // Try JSON format first
        let json_path = problem_dir.join("derivation.json");
        if json_path.exists() {
            let content = std::fs::read_to_string(&json_path)?;
            return Ok(DerivationTrace::from_json(&content)?);
        }

        // Try text format (Newclid/AlphaGeometry)
        let txt_path = problem_dir.join("derivation.txt");
        if txt_path.exists() {
            let content = std::fs::read_to_string(&txt_path)?;
            return Ok(DerivationTrace::parse_auto(&content, problem_id)?);
        }

        Err(BenchmarkError::MissingFile(format!(
            "No derivation found for {}",
            problem_id
        )))
    }

    /// Run benchmark on all discovered problems.
    pub fn run_all(&mut self) -> Result<BenchmarkResult, BenchmarkError> {
        let problems = self.discover_problems()?;

        // Initialize generator if needed and verification is enabled
        if self.config.verify_certs && self.generator.is_none() {
            self.init_generator()?;
        }

        let mut result = BenchmarkResult {
            total: problems.len(),
            ..Default::default()
        };

        let total_start = Instant::now();

        for problem in problems {
            let solution = self.run_single(&problem);
            match &solution {
                Ok(sol) if sol.solved => result.solved += 1,
                Ok(_) => result.unsolved += 1,
                Err(_) => result.errors += 1,
            }

            result
                .results
                .push(solution.unwrap_or_else(|e| ProblemSolution {
                    problem_id: problem.id.clone(),
                    solved: false,
                    solve_time_ms: 0,
                    derivation: None,
                    aux_constructions: Vec::new(),
                    error: Some(format!("{}", e)),
                }));
        }

        result.total_time_ms = total_start.elapsed().as_millis() as u64;
        Ok(result)
    }

    /// Run benchmark on a single problem.
    pub fn run_single(
        &mut self,
        problem: &BenchmarkProblem,
    ) -> Result<ProblemSolution, BenchmarkError> {
        let start = Instant::now();

        // Check if we have a derivation
        let derivation = match &problem.derivation {
            Some(d) => d.clone(),
            None => {
                return Ok(ProblemSolution {
                    problem_id: problem.id.clone(),
                    solved: false,
                    solve_time_ms: 0,
                    derivation: None,
                    aux_constructions: Vec::new(),
                    error: Some("No derivation available".to_string()),
                });
            }
        };

        let expected_goal = goal_signature(&problem.problem)?;
        let actual_goal = final_step_signature(&derivation);

        // Generate certificates and verify if enabled
        let mut cert_success = actual_goal.as_ref() == Some(&expected_goal);
        let mut verification_errors = Vec::new();
        if !cert_success {
            let actual = actual_goal.as_ref().map_or_else(
                || "no goal-producing final step".to_string(),
                |signature| signature.display(),
            );
            verification_errors.push(format!(
                "Goal mismatch: expected {}, got {}",
                expected_goal.display(),
                actual
            ));
        }

        if self.config.verify_certs {
            if let Some(ref mut generator) = self.generator {
                for step in &derivation.steps {
                    match generator.step_to_cert_with_expr(step) {
                        Ok((cert, expr)) => {
                            // Verify the certificate with CertVerifier
                            let mut verifier =
                                CertVerifier::with_mode(generator.env(), generator.env().mode());
                            if let Err(e) = verifier.verify(&cert, &expr) {
                                verification_errors.push(format!("Verification failed: {}", e));
                                cert_success = false;
                                if !self.config.continue_on_error {
                                    return Err(BenchmarkError::InvalidStructure(format!(
                                        "Certificate verification failed: {}",
                                        e
                                    )));
                                }
                            }
                        }
                        Err(e) => {
                            verification_errors
                                .push(format!("Certificate generation failed: {}", e));
                            cert_success = false;
                            if !self.config.continue_on_error {
                                return Err(e.into());
                            }
                        }
                    }
                }
            }
        }

        let solve_time = start.elapsed().as_millis() as u64;

        // Extract auxiliary constructions from derivation steps
        let aux_constructions: Vec<AuxConstruction> = derivation
            .steps
            .iter()
            .filter_map(|step| match step {
                GeomStep::Construct { kind, name, from } => Some(AuxConstruction {
                    name: name.clone(),
                    construction_type: kind.clone(),
                    from_objects: from.clone(),
                    justification: None,
                }),
                _ => None,
            })
            .collect();

        Ok(ProblemSolution {
            problem_id: problem.id.clone(),
            solved: cert_success && derivation.complete,
            solve_time_ms: solve_time,
            derivation: Some(derivation.steps),
            aux_constructions,
            error: if verification_errors.is_empty() {
                None
            } else {
                Some(verification_errors.join("; "))
            },
        })
    }

    /// Save benchmark results to a directory.
    pub fn save_results<P: AsRef<Path>>(
        &self,
        results: &BenchmarkResult,
        output_dir: P,
    ) -> Result<(), BenchmarkError> {
        let output_dir = output_dir.as_ref();
        std::fs::create_dir_all(output_dir)?;

        // Save detailed results as JSONL
        let jsonl_path = output_dir.join("run.jsonl");
        let mut jsonl_content = String::new();
        for sol in &results.results {
            let line = serde_json::to_string(sol)
                .map_err(|e| BenchmarkError::Io(std::io::Error::other(e.to_string())))?;
            jsonl_content.push_str(&line);
            jsonl_content.push('\n');
        }
        std::fs::write(&jsonl_path, jsonl_content)?;

        // Save summary as JSON
        let summary_path = output_dir.join("summary.json");
        let summary = serde_json::to_string_pretty(results)
            .map_err(|e| BenchmarkError::Io(std::io::Error::other(e.to_string())))?;
        std::fs::write(&summary_path, summary)?;

        // Generate leaderboard markdown
        let leaderboard = self.generate_leaderboard(results);
        let leaderboard_path = output_dir.join("leaderboard.md");
        std::fs::write(&leaderboard_path, leaderboard)?;

        Ok(())
    }

    /// Generate a markdown leaderboard.
    fn generate_leaderboard(&self, results: &BenchmarkResult) -> String {
        let mut md = String::new();

        md.push_str(&format!("# {} Benchmark Results\n\n", self.suite_name));
        // Use std::time::SystemTime for timestamp (avoids chrono dependency)
        use std::time::SystemTime;
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        md.push_str(&format!("**Timestamp:** {} (Unix epoch)\n\n", now));

        md.push_str("## Summary\n\n");
        md.push_str("| Metric | Value |\n");
        md.push_str("|--------|-------|\n");
        md.push_str(&format!("| Total Problems | {} |\n", results.total));
        md.push_str(&format!("| Solved | {} |\n", results.solved));
        md.push_str(&format!("| Unsolved | {} |\n", results.unsolved));
        md.push_str(&format!("| Errors | {} |\n", results.errors));
        md.push_str(&format!("| Solve Rate | {:.1}% |\n", results.solve_rate()));
        md.push_str(&format!(
            "| Avg Solve Time | {:.1} ms |\n",
            results.avg_solve_time_ms()
        ));
        md.push_str(&format!("| Total Time | {} ms |\n", results.total_time_ms));

        md.push_str("\n## Problem Details\n\n");
        md.push_str("| Problem ID | Status | Time (ms) | Error |\n");
        md.push_str("|------------|--------|-----------|-------|\n");

        for sol in &results.results {
            let status = if sol.solved {
                "✓"
            } else if sol.error.is_some() {
                "✗"
            } else {
                "-"
            };
            let error = sol
                .error
                .as_ref()
                .map(|e| e.chars().take(50).collect::<String>())
                .unwrap_or_default();
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                sol.problem_id, status, sol.solve_time_ms, error
            ));
        }

        md
    }

    /// Get the suite name.
    pub fn suite_name(&self) -> &str {
        &self.suite_name
    }

    /// Get the configuration.
    pub fn config(&self) -> &BenchmarkConfig {
        &self.config
    }
}

/// Statistics collected during benchmark runs.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BenchmarkStats {
    /// Problems by difficulty
    pub by_difficulty: HashMap<u8, DifficultyStats>,

    /// Problems by tag
    pub by_tag: HashMap<String, usize>,

    /// Certificate generation timing
    pub cert_gen_time_ms: u64,

    /// Certificate verification timing
    pub cert_verify_time_ms: u64,

    /// Total auxiliary constructions across all problems
    pub total_aux_constructions: usize,
}

/// Statistics for a difficulty level.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DifficultyStats {
    /// Total problems at this difficulty
    pub total: usize,

    /// Solved problems
    pub solved: usize,

    /// Average solve time
    pub avg_time_ms: f64,
}

#[cfg(test)]
mod tests {
    use super::test_support::create_test_suite;
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_discover_problems() {
        let (_temp, suite_dir) = create_test_suite();
        let runner = BenchmarkRunner::new(&suite_dir).unwrap();
        let problems = runner.discover_problems().unwrap();

        assert_eq!(problems.len(), 1);
        assert_eq!(problems[0].id, "test_problem_1");
        let _deriv = problems[0]
            .derivation
            .as_ref()
            .expect("discovered problem should have derivation");
    }

    #[test]
    fn test_run_single() {
        let (_temp, suite_dir) = create_test_suite();
        let mut runner = BenchmarkRunner::new(&suite_dir)
            .unwrap()
            .with_config(BenchmarkConfig {
                verify_certs: false, // Skip cert verification for this test
                ..Default::default()
            });

        let problems = runner.discover_problems().unwrap();
        let result = runner.run_single(&problems[0]).unwrap();

        assert_eq!(result.problem_id, "test_problem_1");
        let _deriv = result
            .derivation
            .as_ref()
            .expect("benchmark result should have derivation");
    }

    #[test]
    fn test_save_results() {
        let (_temp, suite_dir) = create_test_suite();
        let output_temp = TempDir::new().unwrap();
        let output_dir = output_temp.path().join("results");

        let runner = BenchmarkRunner::new(&suite_dir).unwrap();

        let results = BenchmarkResult {
            total: 2,
            solved: 1,
            unsolved: 1,
            errors: 0,
            total_time_ms: 100,
            results: vec![
                ProblemSolution {
                    problem_id: "p1".to_string(),
                    solved: true,
                    solve_time_ms: 50,
                    derivation: None,
                    aux_constructions: Vec::new(),
                    error: None,
                },
                ProblemSolution {
                    problem_id: "p2".to_string(),
                    solved: false,
                    solve_time_ms: 50,
                    derivation: None,
                    aux_constructions: Vec::new(),
                    error: Some("timeout".to_string()),
                },
            ],
        };

        runner.save_results(&results, &output_dir).unwrap();

        assert!(output_dir.join("run.jsonl").exists());
        assert!(output_dir.join("summary.json").exists());
        assert!(output_dir.join("leaderboard.md").exists());
    }

    #[test]
    fn test_benchmark_config() {
        let config = BenchmarkConfig {
            timeout_ms: 30_000,
            skip_problems: vec!["skip_me".to_string()],
            ..Default::default()
        };

        let (_temp, suite_dir) = create_test_suite();

        // Create another problem to skip
        let skip_dir = suite_dir.join("skip_me");
        std::fs::create_dir_all(&skip_dir).unwrap();
        std::fs::write(
            skip_dir.join("problem.json"),
            r#"{"id":"skip_me","objects":{},"constraints":[],"goal":{"type":"collinear","points":[]}}"#,
        )
        .unwrap();

        let runner = BenchmarkRunner::new(&suite_dir)
            .unwrap()
            .with_config(config);
        let problems = runner.discover_problems().unwrap();

        // Should only have the one non-skipped problem
        assert_eq!(problems.len(), 1);
        assert_eq!(problems[0].id, "test_problem_1");
    }

    // ════════════════════════════════════════════════════════════════════════
    // Integration Test: Run AlphaGeometry Suite with Certificate Verification
    // ════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_run_alphageometry_suite_with_verify_certs() {
        // This test runs the actual alphageometry benchmark suite
        // with certificate verification enabled (verify_certs=true)
        let suite_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("benchmarks/geometry/alphageometry");

        if !suite_dir.exists() {
            eprintln!(
                "Skipping test: alphageometry suite not found at {:?}",
                suite_dir
            );
            return;
        }

        let config = BenchmarkConfig {
            verify_certs: true,      // Enable certificate verification
            save_certs: false,       // Don't save certs to disk
            continue_on_error: true, // Continue even if some problems fail
            max_problems: 0,         // Run all problems
            ..Default::default()
        };

        let mut runner = BenchmarkRunner::new(&suite_dir)
            .expect("Failed to create benchmark runner")
            .with_config(config);

        // Initialize the certificate generator
        runner.init_generator().expect("Failed to init generator");

        // Discover problems
        let problems = runner
            .discover_problems()
            .expect("Failed to discover problems");
        eprintln!("Discovered {} problems", problems.len());

        // Count problems with derivations
        let with_derivations = problems.iter().filter(|p| p.derivation.is_some()).count();
        eprintln!("Problems with derivations: {}", with_derivations);

        // Run benchmark
        let results = runner.run_all().expect("Failed to run benchmark");

        // Print results summary
        eprintln!("\n=== AlphaGeometry Benchmark Results ===");
        eprintln!("Total: {}", results.total);
        eprintln!("Solved (cert verified): {}", results.solved);
        eprintln!("Unsolved: {}", results.unsolved);
        eprintln!("Errors: {}", results.errors);
        eprintln!("Solve rate: {:.1}%", results.solve_rate());
        eprintln!("Total time: {} ms", results.total_time_ms);
        eprintln!();

        // Print details for problems with errors
        let errors: Vec<_> = results
            .results
            .iter()
            .filter(|r| r.error.is_some())
            .collect();
        if !errors.is_empty() {
            eprintln!("=== Problems with Errors ===");
            for sol in &errors[..errors.len().min(10)] {
                eprintln!("  {} - {:?}", sol.problem_id, sol.error);
            }
            if errors.len() > 10 {
                eprintln!("  ... and {} more", errors.len() - 10);
            }
        }

        // Basic assertions
        assert!(results.total > 0, "Should have some problems to run");
        assert!(
            with_derivations > 0,
            "Should have some problems with derivations"
        );

        // We expect some problems to fail verification due to TypeMismatch
        // (geometry constants don't have proper Pi types yet)
        // But the infrastructure should work without panicking
        eprintln!(
            "\nTest passed: benchmark ran {} problems with cert verification",
            results.total
        );
    }

    #[test]
    fn test_benchmark_with_verify_certs_on_synthetic() {
        // Test certificate verification on synthetic problems with simple derivations
        let temp = TempDir::new().unwrap();
        let suite_dir = temp.path().join("synthetic_suite");
        std::fs::create_dir_all(&suite_dir).unwrap();

        // Create multiple synthetic problems with derivations
        for i in 0..10 {
            let problem_dir = suite_dir.join(format!("problem_{}", i));
            std::fs::create_dir_all(&problem_dir).unwrap();

            let problem_json = format!(
                r#"{{
                    "id": "problem_{}",
                    "objects": {{
                        "A{}": {{"type": "point"}},
                        "B{}": {{"type": "point"}},
                        "C{}": {{"type": "point"}}
                    }},
                    "constraints": [
                        {{"type": "not_equal", "a": "A{}", "b": "B{}"}}
                    ],
                    "goal": {{"type": "collinear", "points": ["A{}", "B{}", "C{}"]}}
                }}"#,
                i, i, i, i, i, i, i, i, i
            );
            std::fs::write(problem_dir.join("problem.json"), problem_json).unwrap();

            // Add a simple derivation
            let derivation = format!(
                r#"
                GIVEN collinear(A{}, B{}, C{})
                AXIOM on_line(A{}, l{})
                "#,
                i, i, i, i, i
            );
            std::fs::write(problem_dir.join("derivation.txt"), derivation).unwrap();
        }

        let config = BenchmarkConfig {
            verify_certs: true,
            continue_on_error: true,
            ..Default::default()
        };

        let mut runner = BenchmarkRunner::new(&suite_dir)
            .unwrap()
            .with_config(config);

        let results = runner.run_all().unwrap();

        assert_eq!(results.total, 10, "Should have 10 synthetic problems");
        eprintln!(
            "Synthetic benchmark: {} total, {} solved, {} errors",
            results.total, results.solved, results.errors
        );
    }
}

#[cfg(test)]
mod goal_match_tests;
#[cfg(test)]
mod test_support;
