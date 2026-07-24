// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use crate::rpc::{error_codes, RequestId};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;
use std::time::{Duration, Instant};

const BENCHMARK_TIMEOUT_MS: u64 = 5_000;
const SEARCH_METHOD_LABEL: &str = "search_proof:auto_only";
const CASCADE_METHOD_LABEL: &str = "prove:auto_cascade";

/// miniF2F-style benchmark category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum BenchmarkCategory {
    Algebra,
    NumberTheory,
    Combinatorics,
    Analysis,
    Logic,
}

impl fmt::Display for BenchmarkCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Algebra => "Algebra",
            Self::NumberTheory => "Number Theory",
            Self::Combinatorics => "Combinatorics",
            Self::Analysis => "Analysis",
            Self::Logic => "Logic",
        };
        f.write_str(text)
    }
}

/// Benchmark difficulty bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum BenchmarkDifficulty {
    Easy,
    Medium,
    Hard,
}

impl fmt::Display for BenchmarkDifficulty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Easy => "Easy",
            Self::Medium => "Medium",
            Self::Hard => "Hard",
        };
        f.write_str(text)
    }
}

/// Coarse benchmark outcome bucket.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
#[serde(rename_all = "snake_case")]
pub enum BenchmarkResult {
    Proved,
    Disproved,
    Timeout,
    Error,
}

impl fmt::Display for BenchmarkResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Proved => "Proved",
            Self::Disproved => "Disproved",
            Self::Timeout => "Timeout",
            Self::Error => "Error",
        };
        f.write_str(text)
    }
}

/// Single benchmark problem definition.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchmarkProblem {
    pub name: String,
    pub lean_statement: String,
    pub category: BenchmarkCategory,
    pub difficulty: BenchmarkDifficulty,
}

impl BenchmarkProblem {
    fn new(
        name: impl Into<String>,
        lean_statement: impl Into<String>,
        category: BenchmarkCategory,
        difficulty: BenchmarkDifficulty,
    ) -> Self {
        Self {
            name: name.into(),
            lean_statement: lean_statement.into(),
            category,
            difficulty,
        }
    }
}

/// Outcome for a single benchmark problem.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchmarkOutcome {
    pub problem_name: String,
    pub result: BenchmarkResult,
    pub time_ns: u64,
    pub method_used: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
}

/// Aggregated statistics for one benchmark category.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BenchmarkCategoryStats {
    pub category: BenchmarkCategory,
    pub total_problems: usize,
    pub proved_count: usize,
    pub disproved_count: usize,
    pub timeout_count: usize,
    pub error_count: usize,
    /// Fraction in the range `[0.0, 1.0]`.
    pub pass_rate: f64,
    pub total_time_ns: u64,
}

/// Full benchmark report.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BenchmarkReport {
    pub total_problems: usize,
    pub proved_count: usize,
    pub disproved_count: usize,
    pub timeout_count: usize,
    pub error_count: usize,
    /// Fraction in the range `[0.0, 1.0]`.
    pub pass_rate: f64,
    pub per_category_stats: Vec<BenchmarkCategoryStats>,
    pub total_time_ns: u64,
}

/// Helper: create a `ServerState` pre-loaded with the kernel prelude (Nat, Bool, Eq, List, …).
fn prelude_state() -> ServerState {
    let env =
        clean_kernel::Environment::try_with_prelude().expect("try_with_prelude should succeed");
    ServerState::new().with_env(env)
}

fn algebra_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new(
            "alg_add_comm",
            "forall (a b : Nat), a + b = b + a",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "alg_mul_one",
            "forall (a : Nat), a * 1 = a",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "alg_one_mul",
            "forall (a : Nat), 1 * a = a",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "alg_add_assoc",
            "forall (a b c : Nat), (a + b) + c = a + (b + c)",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "alg_left_distrib",
            "forall (a b c : Nat), a * (b + c) = a * b + a * c",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Hard,
        ),
        BenchmarkProblem::new(
            "alg_right_distrib",
            "forall (a b c : Nat), (a + b) * c = a * c + b * c",
            BenchmarkCategory::Algebra,
            BenchmarkDifficulty::Hard,
        ),
    ]
}

fn number_theory_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new(
            "nt_succ_ne_zero",
            "forall (n : Nat), Not (Nat.succ n = 0)",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "nt_zero_add",
            "forall (n : Nat), 0 + n = n",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "nt_mul_zero",
            "forall (n : Nat), n * 0 = 0",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "nt_zero_mul",
            "forall (n : Nat), 0 * n = 0",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "nt_succ_injective",
            "forall (m n : Nat), Nat.succ m = Nat.succ n -> m = n",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "nt_add_one_eq_succ",
            "forall (n : Nat), n + 1 = Nat.succ n",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Medium,
        ),
    ]
}

fn combinatorics_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new("comb_length_refl", "forall (xs : List Nat), List.length xs = List.length xs", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Easy),
        BenchmarkProblem::new("comb_length_cons", "forall (x : Nat) (xs : List Nat), List.length (List.cons x xs) = Nat.succ (List.length xs)", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Easy),
        BenchmarkProblem::new("comb_append_nil", "forall (xs : List Nat), List.append xs List.nil = xs", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Medium),
        BenchmarkProblem::new("comb_nil_append", "forall (xs : List Nat), List.append List.nil xs = xs", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Medium),
        BenchmarkProblem::new("comb_cons_ne_nil", "forall (x : Nat) (xs : List Nat), Not (List.cons x xs = List.nil)", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Medium),
        BenchmarkProblem::new("comb_cons_injective_tail", "forall (x : Nat) (xs ys : List Nat), List.cons x xs = List.cons x ys -> xs = ys", BenchmarkCategory::Combinatorics, BenchmarkDifficulty::Hard),
    ]
}

fn analysis_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new(
            "ana_le_refl",
            "forall (n : Nat), n <= n",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "ana_le_succ_self",
            "forall (n : Nat), n <= Nat.succ n",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "ana_le_add_right",
            "forall (a b : Nat), a <= a + b",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "ana_le_add_left",
            "forall (a b : Nat), b <= a + b",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "ana_le_trans",
            "forall (a b c : Nat), a <= b -> b <= c -> a <= c",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Hard,
        ),
        BenchmarkProblem::new(
            "ana_succ_le_succ",
            "forall (a b : Nat), a <= b -> Nat.succ a <= Nat.succ b",
            BenchmarkCategory::Analysis,
            BenchmarkDifficulty::Hard,
        ),
    ]
}

fn logic_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new(
            "logic_true",
            "True",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "logic_identity",
            "forall (p : Prop), p -> p",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "logic_and_elim_left",
            "forall (p q : Prop), p /\\ q -> p",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "logic_or_intro_left",
            "forall (p q : Prop), p -> p \\/ q",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "logic_double_neg_intro",
            "forall (p : Prop), p -> Not (Not p)",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Medium,
        ),
        BenchmarkProblem::new(
            "logic_imp_trans",
            "forall (p q r : Prop), (p -> q) -> (q -> r) -> p -> r",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Hard,
        ),
    ]
}

/// Build the full 30-problem benchmark set from per-category helpers.
fn benchmark_problems() -> Vec<BenchmarkProblem> {
    let mut problems = Vec::with_capacity(30);
    problems.extend(algebra_problems());
    problems.extend(number_theory_problems());
    problems.extend(combinatorics_problems());
    problems.extend(analysis_problems());
    problems.extend(logic_problems());
    problems
}

fn benchmark_smoke_problems() -> Vec<BenchmarkProblem> {
    vec![
        BenchmarkProblem::new(
            "logic_true",
            "True",
            BenchmarkCategory::Logic,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "nt_zero_add",
            "forall (n : Nat), 0 + n = n",
            BenchmarkCategory::NumberTheory,
            BenchmarkDifficulty::Easy,
        ),
        BenchmarkProblem::new(
            "comb_length_refl",
            "forall (xs : List Nat), List.length xs = List.length xs",
            BenchmarkCategory::Combinatorics,
            BenchmarkDifficulty::Easy,
        ),
    ]
}

async fn run_search_benchmark(
    state: &ServerState,
    problems: &[BenchmarkProblem],
) -> (Vec<BenchmarkOutcome>, BenchmarkReport) {
    let mut outcomes = Vec::with_capacity(problems.len());

    for (index, problem) in problems.iter().enumerate() {
        let params = SearchProofParams {
            theorem: problem.lean_statement.clone(),
            strategy: SearchStrategy::AutoOnly,
            hypotheses: Vec::new(),
            max_depth: None,
            beam_width: None,
            timeout_ms: Some(BENCHMARK_TIMEOUT_MS),
        };

        let request_id = RequestId::String(format!("minif2f-search-{index}"));
        let started = Instant::now();
        let response = handle_search_proof(state, request_id, params).await;
        let elapsed_ns = duration_to_ns(started.elapsed());

        outcomes.push(classify_search_response(problem, response, elapsed_ns));
    }

    let report = build_benchmark_report(problems, &outcomes);
    (outcomes, report)
}

async fn exercise_handle_prove(
    state: &ServerState,
    problems: &[BenchmarkProblem],
) -> Vec<ProveResult> {
    let mut results = Vec::with_capacity(problems.len());

    for (index, problem) in problems.iter().enumerate() {
        let params = ProveParams {
            goal: problem.lean_statement.clone(),
            hypotheses: Vec::new(),
            timeout_ms: Some(BENCHMARK_TIMEOUT_MS),
            strategy: None,
        };

        let response = handle_prove(state, RequestId::Number(index as i64 + 1), params).await;
        assert!(
            response.error.is_none(),
            "handle_prove should accept benchmark statement {}: {:?}",
            problem.name,
            response.error
        );

        let result_value = response
            .result
            .expect("prove response should contain a result payload");
        let prove_result: ProveResult =
            serde_json::from_value(result_value).expect("prove result should deserialize");
        results.push(prove_result);
    }

    results
}

fn classify_search_response(
    problem: &BenchmarkProblem,
    response: crate::rpc::Response,
    elapsed_ns: u64,
) -> BenchmarkOutcome {
    if let Some(error) = response.error {
        let result = if error.code == error_codes::TIMEOUT {
            BenchmarkResult::Timeout
        } else {
            BenchmarkResult::Error
        };

        return BenchmarkOutcome {
            problem_name: problem.name.clone(),
            result,
            time_ns: elapsed_ns,
            method_used: SEARCH_METHOD_LABEL.to_string(),
            error_message: Some(error.message),
        };
    }

    let Some(value) = response.result else {
        return BenchmarkOutcome {
            problem_name: problem.name.clone(),
            result: BenchmarkResult::Error,
            time_ns: elapsed_ns,
            method_used: SEARCH_METHOD_LABEL.to_string(),
            error_message: Some("searchProof returned neither result nor error".to_string()),
        };
    };

    match serde_json::from_value::<SearchProofResult>(value) {
        Ok(result) => {
            let bucket = match result.status {
                ProveStatus::Verified | ProveStatus::Unverified if result.found => {
                    BenchmarkResult::Proved
                }
                ProveStatus::Verified | ProveStatus::Unverified => BenchmarkResult::Error,
                // A kernel-rejected proof term is a failure, never a Proved bucket.
                ProveStatus::KernelRejected => BenchmarkResult::Error,
                ProveStatus::Refuted => BenchmarkResult::Disproved,
                ProveStatus::Unknown => BenchmarkResult::Error,
            };

            BenchmarkOutcome {
                problem_name: problem.name.clone(),
                result: bucket,
                time_ns: if result.time_ns == 0 {
                    elapsed_ns
                } else {
                    result.time_ns
                },
                method_used: result
                    .method
                    .unwrap_or_else(|| SEARCH_METHOD_LABEL.to_string()),
                error_message: result.reason,
            }
        }
        Err(error) => BenchmarkOutcome {
            problem_name: problem.name.clone(),
            result: BenchmarkResult::Error,
            time_ns: elapsed_ns,
            method_used: SEARCH_METHOD_LABEL.to_string(),
            error_message: Some(format!("failed to decode SearchProofResult: {error}")),
        },
    }
}

fn build_benchmark_report(
    problems: &[BenchmarkProblem],
    outcomes: &[BenchmarkOutcome],
) -> BenchmarkReport {
    let total_problems = problems.len();
    let proved_count = outcomes
        .iter()
        .filter(|outcome| outcome.result == BenchmarkResult::Proved)
        .count();
    let disproved_count = outcomes
        .iter()
        .filter(|outcome| outcome.result == BenchmarkResult::Disproved)
        .count();
    let timeout_count = outcomes
        .iter()
        .filter(|outcome| outcome.result == BenchmarkResult::Timeout)
        .count();
    let error_count = outcomes
        .iter()
        .filter(|outcome| outcome.result == BenchmarkResult::Error)
        .count();
    let total_time_ns = outcomes
        .iter()
        .fold(0u64, |sum, outcome| sum.saturating_add(outcome.time_ns));

    let mut per_category: BTreeMap<BenchmarkCategory, Vec<&BenchmarkOutcome>> = BTreeMap::new();
    for (problem, outcome) in problems.iter().zip(outcomes.iter()) {
        per_category
            .entry(problem.category)
            .or_default()
            .push(outcome);
    }

    let per_category_stats = per_category
        .into_iter()
        .map(|(category, entries)| {
            let total = entries.len();
            let proved = entries
                .iter()
                .filter(|outcome| outcome.result == BenchmarkResult::Proved)
                .count();
            let disproved = entries
                .iter()
                .filter(|outcome| outcome.result == BenchmarkResult::Disproved)
                .count();
            let timeout = entries
                .iter()
                .filter(|outcome| outcome.result == BenchmarkResult::Timeout)
                .count();
            let error = entries
                .iter()
                .filter(|outcome| outcome.result == BenchmarkResult::Error)
                .count();
            let category_time_ns = entries
                .iter()
                .fold(0u64, |sum, outcome| sum.saturating_add(outcome.time_ns));

            BenchmarkCategoryStats {
                category,
                total_problems: total,
                proved_count: proved,
                disproved_count: disproved,
                timeout_count: timeout,
                error_count: error,
                pass_rate: ratio(proved, total),
                total_time_ns: category_time_ns,
            }
        })
        .collect();

    BenchmarkReport {
        total_problems,
        proved_count,
        disproved_count,
        timeout_count,
        error_count,
        pass_rate: ratio(proved_count, total_problems),
        per_category_stats,
        total_time_ns,
    }
}

fn render_markdown_report(
    problems: &[BenchmarkProblem],
    outcomes: &[BenchmarkOutcome],
    report: &BenchmarkReport,
) -> String {
    let mut markdown = String::new();
    markdown.push_str("# miniF2F Benchmark Report\n\n");
    markdown.push_str("| Metric | Value |\n");
    markdown.push_str("| --- | --- |\n");
    markdown.push_str(&format!("| Total problems | {} |\n", report.total_problems));
    markdown.push_str(&format!("| Proved | {} |\n", report.proved_count));
    markdown.push_str(&format!("| Disproved | {} |\n", report.disproved_count));
    markdown.push_str(&format!("| Timeout | {} |\n", report.timeout_count));
    markdown.push_str(&format!("| Error | {} |\n", report.error_count));
    markdown.push_str(&format!(
        "| Pass rate | {:.1}% |\n",
        report.pass_rate * 100.0
    ));
    markdown.push_str(&format!(
        "| Total time | {} |\n",
        format_duration_ns(report.total_time_ns)
    ));

    markdown.push_str("\n## Per-Category Stats\n\n");
    markdown.push_str(
        "| Category | Total | Proved | Disproved | Timeout | Error | Pass rate | Time |\n",
    );
    markdown.push_str("| --- | --- | --- | --- | --- | --- | --- | --- |\n");
    for stats in &report.per_category_stats {
        markdown.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {:.1}% | {} |\n",
            stats.category,
            stats.total_problems,
            stats.proved_count,
            stats.disproved_count,
            stats.timeout_count,
            stats.error_count,
            stats.pass_rate * 100.0,
            format_duration_ns(stats.total_time_ns)
        ));
    }

    markdown.push_str("\n## Problem Results\n\n");
    markdown.push_str("| Problem | Category | Difficulty | Result | Method | Time | Error |\n");
    markdown.push_str("| --- | --- | --- | --- | --- | --- | --- |\n");
    for (problem, outcome) in problems.iter().zip(outcomes.iter()) {
        markdown.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            problem.name,
            problem.category,
            problem.difficulty,
            outcome.result,
            outcome.method_used,
            format_duration_ns(outcome.time_ns),
            outcome.error_message.as_deref().unwrap_or("-"),
        ));
    }

    markdown
}

fn duration_to_ns(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn ratio(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        0.0
    } else {
        numerator as f64 / denominator as f64
    }
}

fn format_duration_ns(time_ns: u64) -> String {
    format!("{:.2} ms", time_ns as f64 / 1_000_000.0)
}

fn assert_report_is_consistent(report: &BenchmarkReport) {
    assert_eq!(
        report.proved_count + report.disproved_count + report.timeout_count + report.error_count,
        report.total_problems,
        "top-level benchmark counts should cover every problem"
    );

    let category_total: usize = report
        .per_category_stats
        .iter()
        .map(|stats| stats.total_problems)
        .sum();
    assert_eq!(
        category_total, report.total_problems,
        "per-category totals should match the global total"
    );
}

#[tokio::test]
async fn test_minif2f_runner_smoke() {
    let state = prelude_state();
    let problems = benchmark_smoke_problems();

    let prove_results = exercise_handle_prove(&state, &problems).await;
    assert_eq!(
        prove_results.len(),
        problems.len(),
        "handle_prove smoke check should cover the selected subset"
    );

    let (outcomes, report) = run_search_benchmark(&state, &problems).await;
    let markdown = render_markdown_report(&problems, &outcomes, &report);
    println!("\n{markdown}");

    assert_eq!(outcomes.len(), problems.len());
    assert_eq!(report.total_problems, problems.len());
    assert_report_is_consistent(&report);
    assert!(
        markdown.contains("| Problem | Category | Difficulty | Result | Method | Time | Error |"),
        "markdown report should include the problem table header"
    );
}

#[tokio::test]
async fn test_minif2f_auto_only_benchmark_report() {
    let state = prelude_state();
    let problems = benchmark_problems();

    let (outcomes, report) = run_search_benchmark(&state, &problems).await;
    let markdown = render_markdown_report(&problems, &outcomes, &report);
    println!("\n{markdown}");

    assert_eq!(
        problems.len(),
        30,
        "benchmark corpus should stay at 30 problems"
    );
    assert_eq!(outcomes.len(), problems.len());
    assert_eq!(report.total_problems, problems.len());
    assert_eq!(
        report.per_category_stats.len(),
        5,
        "report should cover all requested categories"
    );
    assert_report_is_consistent(&report);
}

// ---------------------------------------------------------------------------
// clean-auto AUTOMATION ENGINE success-rate measurement (Task #6)
//
// This exercises the REAL clean-auto cascade
// (`AutomationEngine::auto_prove_with_query`: SMT -> superposition -> oracle)
// via `handle_prove` with the default ("auto") strategy. It is distinct from
// `run_search_benchmark`, which drives the SMT-bridge-only `searchProof` path.
// The committed `data/clean_auto_success_rate.json` records the measured
// counts; the live test below is a shrink-only ratchet against them.
// ---------------------------------------------------------------------------

/// Committed baseline for the clean-auto cascade success rate.
#[derive(Debug, Clone, Deserialize, Serialize)]
struct CleanAutoSuccessBaseline {
    last_updated: String,
    engine: String,
    corpus: String,
    total: usize,
    proved: usize,
    disproved: usize,
    error: usize,
    pass_rate_pct: u32,
}

/// Path to the committed clean-auto success-rate baseline (repo `data/`).
fn clean_auto_baseline_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("clean-server crate dir has a parent")
        .parent()
        .expect("crates dir has a parent (workspace root)")
        .join("data/clean_auto_success_rate.json")
}

/// Classify a `ProveResult` from the auto cascade into a coarse benchmark bucket.
///
/// Mirrors [`classify_search_response`] but buckets on the typed `ProveResult`
/// returned by `handle_prove`. A `KernelRejected` proof term is a failure and is
/// bucketed as `Error`; it must NEVER count as `Proved`.
fn classify_prove_response(
    problem: &BenchmarkProblem,
    result: &ProveResult,
    elapsed_ns: u64,
) -> BenchmarkOutcome {
    let bucket = match result.status {
        ProveStatus::Verified | ProveStatus::Unverified if result.found => BenchmarkResult::Proved,
        ProveStatus::Verified | ProveStatus::Unverified => BenchmarkResult::Error,
        // A kernel-rejected proof term is a failure, never a Proved bucket.
        ProveStatus::KernelRejected => BenchmarkResult::Error,
        ProveStatus::Refuted => BenchmarkResult::Disproved,
        ProveStatus::Unknown => BenchmarkResult::Error,
    };

    BenchmarkOutcome {
        problem_name: problem.name.clone(),
        result: bucket,
        time_ns: if result.time_ns.unwrap_or(0) == 0 {
            elapsed_ns
        } else {
            result.time_ns.unwrap_or(elapsed_ns)
        },
        method_used: result
            .method
            .clone()
            .unwrap_or_else(|| CASCADE_METHOD_LABEL.to_string()),
        error_message: result.reason.clone(),
    }
}

/// Run the full corpus through the clean-auto cascade (`handle_prove`, default
/// "auto" strategy) and build a [`BenchmarkReport`] from the classified outcomes.
async fn run_auto_cascade_benchmark(
    state: &ServerState,
    problems: &[BenchmarkProblem],
) -> (Vec<BenchmarkOutcome>, BenchmarkReport) {
    let mut outcomes = Vec::with_capacity(problems.len());

    for (index, problem) in problems.iter().enumerate() {
        let params = ProveParams {
            goal: problem.lean_statement.clone(),
            hypotheses: Vec::new(),
            timeout_ms: Some(BENCHMARK_TIMEOUT_MS),
            // None => "auto" => AutomationEngine::auto_prove_with_query cascade.
            strategy: None,
        };

        let request_id = RequestId::String(format!("clean-auto-cascade-{index}"));
        let started = Instant::now();
        let response = handle_prove(state, request_id, params).await;
        let elapsed_ns = duration_to_ns(started.elapsed());

        let outcome = if let Some(error) = response.error {
            let result = if error.code == error_codes::TIMEOUT {
                BenchmarkResult::Timeout
            } else {
                BenchmarkResult::Error
            };
            BenchmarkOutcome {
                problem_name: problem.name.clone(),
                result,
                time_ns: elapsed_ns,
                method_used: CASCADE_METHOD_LABEL.to_string(),
                error_message: Some(error.message),
            }
        } else if let Some(value) = response.result {
            match serde_json::from_value::<ProveResult>(value) {
                Ok(prove_result) => classify_prove_response(problem, &prove_result, elapsed_ns),
                Err(error) => BenchmarkOutcome {
                    problem_name: problem.name.clone(),
                    result: BenchmarkResult::Error,
                    time_ns: elapsed_ns,
                    method_used: CASCADE_METHOD_LABEL.to_string(),
                    error_message: Some(format!("failed to decode ProveResult: {error}")),
                },
            }
        } else {
            BenchmarkOutcome {
                problem_name: problem.name.clone(),
                result: BenchmarkResult::Error,
                time_ns: elapsed_ns,
                method_used: CASCADE_METHOD_LABEL.to_string(),
                error_message: Some("prove returned neither result nor error".to_string()),
            }
        };

        outcomes.push(outcome);
    }

    let report = build_benchmark_report(problems, &outcomes);
    (outcomes, report)
}

/// Measure the REAL clean-auto cascade success rate and ratchet against the
/// committed baseline. The live proved-count must never drop below the recorded
/// figure in `data/clean_auto_success_rate.json` (shrink-only ratchet).
#[tokio::test]
async fn test_clean_auto_cascade_success_rate() {
    let state = prelude_state();
    let problems = benchmark_problems();

    let (outcomes, report) = run_auto_cascade_benchmark(&state, &problems).await;
    let markdown = render_markdown_report(&problems, &outcomes, &report);
    println!("\n# clean-auto AutomationEngine cascade (SMT -> superposition -> oracle)\n");
    println!("{markdown}");

    assert_eq!(outcomes.len(), problems.len());
    assert_eq!(report.total_problems, problems.len());
    assert_report_is_consistent(&report);

    let baseline_path = clean_auto_baseline_path();
    let baseline_json = std::fs::read_to_string(&baseline_path).unwrap_or_else(|e| {
        panic!(
            "committed clean-auto baseline should be readable at {}: {e}",
            baseline_path.display()
        )
    });
    let baseline: CleanAutoSuccessBaseline = serde_json::from_str(&baseline_json)
        .expect("clean_auto_success_rate.json should deserialize");

    assert_eq!(
        baseline.total, report.total_problems,
        "committed baseline total ({}) should match live corpus size ({})",
        baseline.total, report.total_problems
    );

    // Shrink-only ratchet: live proved-count may never regress below the
    // committed measurement.
    assert!(
        report.proved_count >= baseline.proved,
        "clean-auto cascade proved-count regressed: live {} < committed baseline {} \
         (corpus={}, engine={})",
        report.proved_count,
        baseline.proved,
        baseline.corpus,
        baseline.engine,
    );
}
